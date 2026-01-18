# app.R  (robust version)
# EVT Applications Dashboard: 5 Finance + 5 Insurance
# - Works fully with SIMULATED data by default
# - Yahoo is optional; if download fails/too short -> auto-fallback to simulated
#
# install.packages(c("shiny","shinydashboard","xts","DT","evir","evd","rugarch","ggplot2","quantmod"))

suppressPackageStartupMessages({
  library(shiny)
  library(shinydashboard)
  library(xts)
  library(DT)
  library(evir)
  library(evd)
  library(rugarch)
  library(ggplot2)
})

# quantmod is optional (only used when "Yahoo" selected)
has_quantmod <- requireNamespace("quantmod", quietly = TRUE)

# ----------------------------
# Helpers (defensive)
# ----------------------------
make_biz_dates <- function(n, end = Sys.Date()) {
  # Generate last n business days ending at 'end'
  d <- seq.Date(end - (n*2 + 30), end, by = "day")
  d <- d[weekdays(d) %in% c("Monday","Tuesday","Wednesday","Thursday","Friday")]
  tail(d, n)
}

get_returns_sim <- function(n = 2500, df_t = 5, end = Sys.Date()) {
  # heavy-tail + volatility clustering
  dates <- make_biz_dates(n, end = end)
  n <- length(dates)
  z <- rt(n, df = df_t)
  sig <- numeric(n)
  sig[1] <- 0.01
  if (n >= 2) {
    for (i in 2:n) sig[i] <- pmax(0.0005, 0.95 * sig[i-1] + 0.05 * abs(z[i-1]) * 0.02)
  }
  r <- sig * z
  xts(r, order.by = dates)
}

get_returns_yahoo <- function(ticker, from, to) {
  if (!has_quantmod) return(NULL)
  tryCatch({
    px <- suppressWarnings(quantmod::getSymbols(
      ticker, src = "yahoo", from = from, to = to, auto.assign = FALSE
    ))
    r <- quantmod::dailyReturn(quantmod::Ad(px), type = "log")
    na.omit(r)
  }, error = function(e) NULL)
}

returns_to_losses_pct <- function(r_xts) {
  # Positive loss in %: 100*(1-exp(r)) ; floor at 0 (loss-side only)
  r <- as.numeric(r_xts)
  L <- 100 * (1 - exp(r))
  L <- pmax(L, 0)
  xts(L, order.by = index(r_xts))
}

block_maxima <- function(loss_xts, block_size = 252) {
  x <- as.numeric(na.omit(loss_xts))
  n <- length(x)
  m <- floor(n / block_size)
  if (m < 5) return(NULL)
  x <- x[(n - m*block_size + 1):n]
  mat <- matrix(x, nrow = block_size, ncol = m)
  apply(mat, 2, max, na.rm = TRUE)
}

fit_gev <- function(maxima) {
  if (is.null(maxima) || length(maxima) < 5) return(NULL)
  tryCatch(evd::fgev(maxima), error = function(e) NULL)
}

gev_return_level <- function(fit, k = 10) {
  if (is.null(fit)) return(NA_real_)
  mu <- fit$estimate["loc"]
  si <- fit$estimate["scale"]
  xi <- fit$estimate["shape"]
  evd::qgev(1 - 1/k, loc = mu, scale = si, shape = xi)
}

fit_gpd <- function(x, u) {
  x <- x[is.finite(x)]
  if (length(x) < 200) return(NULL)
  if (sum(x > u) < 50) return(NULL)
  tryCatch(evir::gpd(x, threshold = u, method = "ml"), error = function(e) NULL)
}

mean_excess <- function(x, u_grid) {
  sapply(u_grid, function(u) {
    exc <- x[x > u]
    if (length(exc) < 10) return(NA_real_)
    mean(exc - u)
  })
}

gpd_var_es <- function(x, u, fit, alpha = 0.99) {
  x <- x[is.finite(x)]
  if (length(x) == 0 || is.null(fit)) return(list(VaR = NA_real_, ES = NA_real_))
  pu <- mean(x > u)
  if (!is.finite(pu) || pu <= 0) return(list(VaR = NA_real_, ES = NA_real_))
  
  xi   <- fit$par.ests[["xi"]]
  beta <- fit$par.ests[["beta"]]
  
  if (!is.finite(xi) || !is.finite(beta) || beta <= 0) {
    return(list(VaR = NA_real_, ES = NA_real_))
  }
  
  if (abs(xi) < 1e-8) {
    VaR <- u + beta * log(pu / (1 - alpha))
  } else {
    VaR <- u + (beta / xi) * ((( (1 - alpha) / pu )^(-xi)) - 1)
  }
  
  ES <- if (xi < 1) (VaR / (1 - xi)) + (beta - xi*u) / (1 - xi) else NA_real_
  list(VaR = VaR, ES = ES, xi = xi, beta = beta, pu = pu, Nu = sum(x > u), n = length(x))
}

kupiec_test <- function(exceed, p) {
  x <- sum(exceed, na.rm = TRUE)
  n <- sum(!is.na(exceed))
  if (n == 0) return(list(LR = NA, p.value = NA, x = x, n = n))
  phat <- x / n
  if (phat %in% c(0,1)) return(list(LR = Inf, p.value = 0, x = x, n = n))
  LR <- -2 * (log((1 - p)^(n - x) * p^x) - log((1 - phat)^(n - x) * phat^x))
  list(LR = LR, p.value = 1 - pchisq(LR, df = 1), x = x, n = n)
}

simulate_severity <- function(n, model) {
  if (model == "Lognormal") {
    x <- rlnorm(n, meanlog = 3.2, sdlog = 0.8)
  } else if (model == "Pareto") {
    alpha <- 1.8; xm <- 10
    u <- runif(n)
    x <- xm * (1 - u)^(-1/alpha)
  } else {
    mix <- rbinom(n, 1, 0.85) == 1
    x <- numeric(n)
    x[mix] <- rlnorm(sum(mix), meanlog = 3.0, sdlog = 0.7)
    alpha <- 1.7; xm <- 30
    u <- runif(sum(!mix))
    x[!mix] <- xm * (1 - u)^(-1/alpha)
  }
  x/10
}

simulate_semiparam_severity <- function(x, u, fit, n_sim = 50000) {
  x <- x[is.finite(x) & x >= 0]
  if (length(x) < 200 || is.null(fit)) return(sample(x, n_sim, replace = TRUE))
  
  xi   <- fit$par.ests[["xi"]]
  beta <- fit$par.ests[["beta"]]
  pu <- mean(x > u)
  
  body <- x[x <= u]
  if (length(body) < 100) body <- x
  
  is_tail <- rbinom(n_sim, 1, pu) == 1
  y <- numeric(n_sim)
  y[!is_tail] <- sample(body, sum(!is_tail), replace = TRUE)
  
  m <- sum(is_tail)
  if (m > 0) {
    U <- runif(m)
    exc <- if (abs(xi) < 1e-8) {
      -beta * log(1 - U)
    } else {
      (beta/xi) * ((1 - U)^(-xi) - 1)
    }
    y[is_tail] <- u + exc
  }
  y
}

# ----------------------------
# UI
# ----------------------------
scenarioBox <- function(title, html_text) {
  box(
    title = title, width = 12, status = "primary", solidHeader = TRUE, collapsible = TRUE,
    HTML(html_text)
  )
}

ui <- dashboardPage(
  dashboardHeader(title = "EVT Dashboard: Finance & Insurance (10 Applications)"),
  dashboardSidebar(
    sidebarMenu(id = "menu",
                menuItem("Overview", tabName = "overview", icon = icon("home")),
                
                menuItem("Finance (5)", icon = icon("chart-line"),
                         menuSubItem("1) Crash return levels (GEV)", tabName = "fin1"),
                         menuSubItem("2) Tail VaR/ES (GPD)", tabName = "fin2"),
                         menuSubItem("3) Conditional EVT (GARCH+GPD)", tabName = "fin3"),
                         menuSubItem("4) Threshold diagnostics", tabName = "fin4"),
                         menuSubItem("5) VaR backtest (Kupiec)", tabName = "fin5")
                ),
                
                menuItem("Insurance (5)", icon = icon("umbrella"),
                         menuSubItem("1) Large-claim tail (GPD)", tabName = "ins1"),
                         menuSubItem("2) Excess-of-loss pricing", tabName = "ins2"),
                         menuSubItem("3) Solvency capital (annual)", tabName = "ins3"),
                         menuSubItem("4) Cat return periods (GEV)", tabName = "ins4"),
                         menuSubItem("5) Sensitivity to threshold u", tabName = "ins5")
                )
    )
  ),
  dashboardBody(
    tabItems(
      tabItem(tabName = "overview",
              fluidRow(
                scenarioBox("How to use this dashboard",
                            paste0(
                              "<ul>",
                              "<li>Pick an application from the left menu.</li>",
                              "<li>Use <b>Simulated</b> to avoid any Yahoo/internet issues (recommended).</li>",
                              "<li>Each app shows: a diagnostic plot + EVT fit + a business interpretation.</li>",
                              "</ul>",
                              if (!has_quantmod) "<p><b>Note:</b> quantmod is not installed, so Yahoo option will auto-fallback to simulation.</p>" else ""
                            )
                )
              )
      ),
      
      # ---------- FIN1 ----------
      tabItem(tabName = "fin1",
              fluidRow(scenarioBox("Finance 1 — Crash return levels (GEV / block maxima)",
                                   "Goal: estimate rare crash levels (e.g., 10-year, 50-year) using block maxima and a GEV fit.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    selectInput("fin1_source","Data source", c("Simulated","Yahoo"), selected="Simulated"),
                    textInput("fin1_ticker","Ticker (Yahoo)", value="^GSPC"),
                    dateInput("fin1_from","From", value=Sys.Date()-3650),
                    dateInput("fin1_to","To", value=Sys.Date()),
                    numericInput("fin1_nsim","Sim n (if simulated)", value=2500, min=500, step=250),
                    selectInput("fin1_block","Block size (days)", c("Monthly ~21"=21,"Quarterly ~63"=63,"Annual ~252"=252), selected=252),
                    numericInput("fin1_k","Return period k blocks", value=10, min=2, step=1),
                    actionButton("fin1_run","Run", icon=icon("play"))
                ),
                box(title="Plots", width=8, status="info", solidHeader=TRUE,
                    plotOutput("fin1_plot_loss", height=230),
                    plotOutput("fin1_plot_max", height=230)
                )
              ),
              fluidRow(
                box(title="GEV results", width=12, status="success", solidHeader=TRUE,
                    DTOutput("fin1_tbl"),
                    verbatimTextOutput("fin1_txt")
                )
              )
      ),
      
      # ---------- FIN2 ----------
      tabItem(tabName = "fin2",
              fluidRow(scenarioBox("Finance 2 — Tail VaR/ES (GPD / POT)",
                                   "Goal: estimate VaR and ES at high confidence (e.g., 99%, 99.5%) using exceedances over a high threshold.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    selectInput("fin2_source","Data source", c("Simulated","Yahoo"), selected="Simulated"),
                    textInput("fin2_ticker","Ticker (Yahoo)", value="^GSPC"),
                    dateInput("fin2_from","From", value=Sys.Date()-3650),
                    dateInput("fin2_to","To", value=Sys.Date()),
                    numericInput("fin2_nsim","Sim n (if simulated)", value=2500, min=500, step=250),
                    sliderInput("fin2_uq","Threshold u quantile", 0.80, 0.99, 0.95, 0.005),
                    sliderInput("fin2_alpha","Risk level α", 0.90, 0.999, 0.99, 0.001),
                    actionButton("fin2_run","Run", icon=icon("play"))
                ),
                box(title="Diagnostics", width=8, status="info", solidHeader=TRUE,
                    plotOutput("fin2_me", height=230),
                    plotOutput("fin2_tail", height=230)
                )
              ),
              fluidRow(
                box(title="GPD results", width=12, status="success", solidHeader=TRUE,
                    DTOutput("fin2_tbl"),
                    verbatimTextOutput("fin2_txt")
                )
              )
      ),
      
      # ---------- FIN3 ----------
      tabItem(tabName = "fin3",
              fluidRow(scenarioBox("Finance 3 — Conditional EVT (GARCH + GPD)",
                                   "Goal: volatility changes over time; fit GARCH, EVT-fit extreme standardized residual losses, then scale to next-day conditional VaR/ES.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    selectInput("fin3_source","Data source", c("Simulated","Yahoo"), selected="Simulated"),
                    textInput("fin3_ticker","Ticker (Yahoo)", value="^GSPC"),
                    dateInput("fin3_from","From", value=Sys.Date()-3650),
                    dateInput("fin3_to","To", value=Sys.Date()),
                    numericInput("fin3_nsim","Sim n (if simulated)", value=3000, min=800, step=200),
                    sliderInput("fin3_uq","Residual-loss threshold quantile", 0.80, 0.99, 0.95, 0.005),
                    sliderInput("fin3_alpha","Risk level α", 0.90, 0.999, 0.99, 0.001),
                    actionButton("fin3_run","Run", icon=icon("play"))
                ),
                box(title="Outputs", width=8, status="info", solidHeader=TRUE,
                    plotOutput("fin3_vol", height=230),
                    plotOutput("fin3_res_tail", height=230)
                )
              ),
              fluidRow(
                box(title="Conditional risk results", width=12, status="success", solidHeader=TRUE,
                    DTOutput("fin3_tbl"),
                    verbatimTextOutput("fin3_txt")
                )
              )
      ),
      
      # ---------- FIN4 ----------
      tabItem(tabName = "fin4",
              fluidRow(scenarioBox("Finance 4 — Threshold diagnostics (Mean-Excess + Hill)",
                                   "Goal: choose a defensible threshold u. Look for mean-excess linear-ish region and stable Hill tail index region.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    selectInput("fin4_source","Data source", c("Simulated","Yahoo"), selected="Simulated"),
                    textInput("fin4_ticker","Ticker (Yahoo)", value="^GSPC"),
                    dateInput("fin4_from","From", value=Sys.Date()-3650),
                    dateInput("fin4_to","To", value=Sys.Date()),
                    numericInput("fin4_nsim","Sim n (if simulated)", value=2500, min=800, step=200),
                    sliderInput("fin4_uq_lo","u quantile low", 0.70, 0.95, 0.85, 0.01),
                    sliderInput("fin4_uq_hi","u quantile high", 0.80, 0.99, 0.97, 0.01),
                    actionButton("fin4_run","Run", icon=icon("play"))
                ),
                box(title="Diagnostics", width=8, status="info", solidHeader=TRUE,
                    plotOutput("fin4_me", height=240),
                    plotOutput("fin4_hill", height=240)
                )
              )
      ),
      
      # ---------- FIN5 ----------
      tabItem(tabName = "fin5",
              fluidRow(scenarioBox("Finance 5 — VaR backtesting (Kupiec coverage test)",
                                   "Goal: train EVT VaR on early sample, test on holdout. Check exceedance count and Kupiec p-value.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    selectInput("fin5_source","Data source", c("Simulated","Yahoo"), selected="Simulated"),
                    textInput("fin5_ticker","Ticker (Yahoo)", value="^GSPC"),
                    dateInput("fin5_from","From", value=Sys.Date()-3650),
                    dateInput("fin5_to","To", value=Sys.Date()),
                    numericInput("fin5_nsim","Sim n (if simulated)", value=2500, min=800, step=200),
                    sliderInput("fin5_train","Training fraction", 0.5, 0.9, 0.8, 0.05),
                    sliderInput("fin5_uq","Threshold u quantile", 0.80, 0.99, 0.95, 0.005),
                    sliderInput("fin5_alpha","Risk level α", 0.90, 0.999, 0.99, 0.001),
                    actionButton("fin5_run","Run", icon=icon("play"))
                ),
                box(title="Backtest plot", width=8, status="info", solidHeader=TRUE,
                    plotOutput("fin5_plot", height=480)
                )
              ),
              fluidRow(
                box(title="Backtest summary", width=12, status="success", solidHeader=TRUE,
                    DTOutput("fin5_tbl"),
                    verbatimTextOutput("fin5_txt")
                )
              )
      ),
      
      # ---------- INS1 ----------
      tabItem(tabName = "ins1",
              fluidRow(scenarioBox("Insurance 1 — Large-claim severity tail (GPD)",
                                   "Goal: model heavy-tailed claim severities; estimate extreme quantiles and ES.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    numericInput("ins1_n","Number of claims", 5000, min=1000, step=500),
                    selectInput("ins1_model","Severity model", c("Mixture (LN+Pareto)","Lognormal","Pareto"),
                                selected="Mixture (LN+Pareto)"),
                    sliderInput("ins1_uq","Threshold u quantile", 0.80, 0.99, 0.95, 0.005),
                    sliderInput("ins1_alpha","Risk level α", 0.90, 0.999, 0.995, 0.001),
                    actionButton("ins1_run","Run", icon=icon("play"))
                ),
                box(title="Diagnostics", width=8, status="info", solidHeader=TRUE,
                    plotOutput("ins1_me", height=230),
                    plotOutput("ins1_tail", height=230)
                )
              ),
              fluidRow(
                box(title="GPD results", width=12, status="success", solidHeader=TRUE,
                    DTOutput("ins1_tbl"),
                    verbatimTextOutput("ins1_txt")
                )
              )
      ),
      
      # ---------- INS2 ----------
      tabItem(tabName = "ins2",
              fluidRow(scenarioBox("Insurance 2 — Excess-of-loss layer pricing",
                                   "Goal: price a reinsurance layer with retention R and limit L using semi-parametric (empirical body + GPD tail) simulation.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    numericInput("ins2_n","Historical severities n", 7000, min=1000, step=500),
                    selectInput("ins2_model","Severity model", c("Mixture (LN+Pareto)","Lognormal","Pareto"),
                                selected="Mixture (LN+Pareto)"),
                    sliderInput("ins2_uq","Threshold u quantile", 0.80, 0.99, 0.95, 0.005),
                    numericInput("ins2_R","Retention R", 50, min=0, step=5),
                    numericInput("ins2_L","Limit L", 200, min=1, step=10),
                    numericInput("ins2_sim","Simulation draws", 50000, min=5000, step=5000),
                    actionButton("ins2_run","Run", icon=icon("play"))
                ),
                box(title="Layer distribution", width=8, status="info", solidHeader=TRUE,
                    plotOutput("ins2_plot", height=480)
                )
              ),
              fluidRow(
                box(title="Pricing output", width=12, status="success", solidHeader=TRUE,
                    DTOutput("ins2_tbl"),
                    verbatimTextOutput("ins2_txt")
                )
              )
      ),
      
      # ---------- INS3 ----------
      tabItem(tabName = "ins3",
              fluidRow(scenarioBox("Insurance 3 — Solvency capital (annual VaR/ES) frequency–severity",
                                   "Goal: simulate annual aggregate losses using Poisson frequency and heavy-tailed severity; compute VaR/ES at high α.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    numericInput("ins3_lambda","Poisson frequency λ", 40, min=1, step=1),
                    numericInput("ins3_hist_n","Severity sample n", 8000, min=1000, step=500),
                    selectInput("ins3_model","Severity model", c("Mixture (LN+Pareto)","Lognormal","Pareto"),
                                selected="Mixture (LN+Pareto)"),
                    sliderInput("ins3_uq","Tail threshold u quantile", 0.80, 0.99, 0.95, 0.005),
                    sliderInput("ins3_alpha","Capital level α", 0.90, 0.999, 0.995, 0.001),
                    numericInput("ins3_years","Simulation years", 20000, min=2000, step=2000),
                    actionButton("ins3_run","Run", icon=icon("play"))
                ),
                box(title="Aggregate loss distribution", width=8, status="info", solidHeader=TRUE,
                    plotOutput("ins3_plot", height=480)
                )
              ),
              fluidRow(
                box(title="Capital output", width=12, status="success", solidHeader=TRUE,
                    DTOutput("ins3_tbl"),
                    verbatimTextOutput("ins3_txt")
                )
              )
      ),
      
      # ---------- INS4 ----------
      tabItem(tabName = "ins4",
              fluidRow(scenarioBox("Insurance 4 — Cat return periods (GEV)",
                                   "Goal: fit GEV to annual maxima (simulated) and compute return levels like 1-in-100.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    numericInput("ins4_years","Years of maxima", 60, min=20, step=5),
                    numericInput("ins4_loc","True loc (sim)", 20, step=1),
                    numericInput("ins4_scale","True scale (sim)", 10, step=1),
                    numericInput("ins4_shape","True shape ξ (sim)", 0.2, step=0.05),
                    numericInput("ins4_k","Return period (years)", 100, min=2, step=1),
                    actionButton("ins4_run","Run", icon=icon("play"))
                ),
                box(title="Maxima", width=8, status="info", solidHeader=TRUE,
                    plotOutput("ins4_plot", height=480)
                )
              ),
              fluidRow(
                box(title="GEV output", width=12, status="success", solidHeader=TRUE,
                    DTOutput("ins4_tbl"),
                    verbatimTextOutput("ins4_txt")
                )
              )
      ),
      
      # ---------- INS5 ----------
      tabItem(tabName = "ins5",
              fluidRow(scenarioBox("Insurance 5 — Sensitivity to threshold u",
                                   "Goal: show how ξ and VaR(α) change across u-quantiles; pick stable region.")),
              fluidRow(
                box(title="Inputs", width=4, status="warning", solidHeader=TRUE,
                    numericInput("ins5_n","Number of claims", 8000, min=2000, step=500),
                    selectInput("ins5_model","Severity model", c("Mixture (LN+Pareto)","Lognormal","Pareto"),
                                selected="Mixture (LN+Pareto)"),
                    sliderInput("ins5_uq_lo","u quantile low", 0.70, 0.95, 0.85, 0.01),
                    sliderInput("ins5_uq_hi","u quantile high", 0.80, 0.99, 0.97, 0.01),
                    sliderInput("ins5_alpha","Risk level α", 0.95, 0.999, 0.999, 0.001),
                    actionButton("ins5_run","Run", icon=icon("play"))
                ),
                box(title="Sensitivity plots", width=8, status="info", solidHeader=TRUE,
                    plotOutput("ins5_xi", height=240),
                    plotOutput("ins5_var", height=240)
                )
              ),
              fluidRow(
                box(title="Table", width=12, status="success", solidHeader=TRUE,
                    DTOutput("ins5_tbl")
                )
              )
      )
    )
  )
)

# ----------------------------
# Server: data getter per finance tab (no shared switch -> fewer NULL bugs)
# ----------------------------
get_fin_losses <- function(source, ticker, from, to, nsim) {
  if (identical(source, "Yahoo")) {
    r <- get_returns_yahoo(ticker, from, to)
    # fallback if Yahoo fails or too short
    if (is.null(r) || NROW(r) < 800) {
      r <- get_returns_sim(n = nsim, df_t = 5, end = to)
      source_used <- "Simulated (fallback)"
    } else {
      source_used <- paste0("Yahoo (", ticker, ")")
    }
  } else {
    r <- get_returns_sim(n = nsim, df_t = 5, end = to)
    source_used <- "Simulated"
  }
  L <- returns_to_losses_pct(r)
  list(losses = L, returns = r, source_used = source_used)
}

server <- function(input, output, session) {
  
  # ========== FIN1 ==========
  fin1_res <- eventReactive(input$fin1_run, {
    d <- get_fin_losses(input$fin1_source, input$fin1_ticker, input$fin1_from, input$fin1_to, input$fin1_nsim)
    validate(need(NROW(d$losses) >= 800, "Not enough data. Increase simulation n or widen Yahoo date range."))
    
    maxima <- block_maxima(d$losses, block_size = as.integer(input$fin1_block))
    validate(need(!is.null(maxima), "Not enough blocks for GEV. Use smaller block size or more data."))
    
    fit <- fit_gev(maxima)
    validate(need(!is.null(fit), "GEV fit failed."))
    
    list(d=d, maxima=maxima, fit=fit)
  })
  
  output$fin1_plot_loss <- renderPlot({
    res <- fin1_res()
    x <- as.numeric(res$d$losses)
    plot(index(res$d$losses), x, type="l", xlab="Date", ylab="Loss (%)",
         main=paste0("Loss series — ", res$d$source_used))
  })
  
  output$fin1_plot_max <- renderPlot({
    res <- fin1_res()
    plot(res$maxima, type="h", xlab="Block", ylab="Max loss (%)",
         main="Block maxima (GEV input)")
  })
  
  output$fin1_tbl <- renderDT({
    res <- fin1_res()
    est <- res$fit$estimate
    
    # robust std error extraction
    se <- rep(NA_real_, length(est))
    names(se) <- names(est)
    
    # try covariance matrix first
    covm <- res$fit$cov
    if (!is.null(covm)) {
      tmp <- tryCatch(sqrt(diag(covm)), error = function(e) NULL)
      if (!is.null(tmp) && length(tmp) > 0) {
        # align by names if possible
        if (!is.null(names(tmp))) {
          se[names(tmp)] <- tmp
        } else if (length(tmp) == length(se)) {
          se <- tmp
          names(se) <- names(est)
        }
      }
    }
    
    # fallback: some versions store std errors directly
    if (all(is.na(se))) {
      tmp <- NULL
      if (!is.null(res$fit$std.err)) tmp <- res$fit$std.err
      if (!is.null(res$fit$se))      tmp <- res$fit$se
      if (!is.null(tmp) && length(tmp) > 0) {
        if (!is.null(names(tmp))) se[names(tmp)] <- tmp
        else if (length(tmp) == length(se)) se <- tmp
      }
    }
    
    df <- data.frame(
      Parameter = names(est),
      Estimate  = as.numeric(est),
      StdErr    = as.numeric(se),
      row.names = NULL
    )
    
    DT::datatable(df, options = list(dom = "tip", pageLength = 5))
  })
  
  
  output$fin1_txt <- renderPrint({
    res <- fin1_res()
    k <- as.integer(input$fin1_k)
    rl <- gev_return_level(res$fit, k = k)
    cat("Return level (exceeded about once every", k, "blocks):\n")
    cat(sprintf("  %.3f %% loss\n", rl))
    cat("\nIf block is annual (~252 days), k=10 ≈ 10-year crash level.\n")
  })
  
  # ========== FIN2 ==========
  fin2_res <- eventReactive(input$fin2_run, {
    d <- get_fin_losses(input$fin2_source, input$fin2_ticker, input$fin2_from, input$fin2_to, input$fin2_nsim)
    x <- as.numeric(na.omit(d$losses))
    validate(need(length(x) >= 800, "Not enough data."))
    
    u <- as.numeric(quantile(x, probs = input$fin2_uq, na.rm = TRUE))
    fit <- fit_gpd(x, u)
    validate(need(!is.null(fit), "GPD fit failed: too few exceedances. Lower u quantile or increase n."))
    
    risk <- gpd_var_es(x, u, fit, alpha = input$fin2_alpha)
    list(d=d, x=x, u=u, fit=fit, risk=risk)
  })
  
  output$fin2_me <- renderPlot({
    res <- fin2_res()
    u_grid <- as.numeric(quantile(res$x, probs = seq(0.80, 0.99, by = 0.01), na.rm = TRUE))
    me <- mean_excess(res$x, u_grid)
    plot(u_grid, me, type="b", xlab="u (loss %)", ylab="Mean excess",
         main=paste0("Mean Excess — ", res$d$source_used))
    abline(v = res$u, lty=2)
  })
  
  output$fin2_tail <- renderPlot({
    res <- fin2_res()
    x <- sort(res$x)
    n <- length(x)
    p_emp <- (n:1)/n
    plot(log(x + 1e-9), log(p_emp), pch=16, cex=0.5,
         xlab="log(loss)", ylab="log(1-F)", main="Tail (empirical) + GPD")
    u <- res$u
    tail_x <- x[x >= u]
    pu <- mean(res$x > u)
    xi <- res$fit$par.ests[["xi"]]
    beta <- res$fit$par.ests[["beta"]]
    if (abs(xi) < 1e-8) {
      p_gpd <- pu * exp(-(tail_x - u)/beta)
    } else {
      p_gpd <- pu * (1 + xi * (tail_x - u) / beta)^(-1/xi)
    }
    lines(log(tail_x + 1e-9), log(p_gpd + 1e-12), lwd=2)
    abline(v=log(u + 1e-9), lty=2)
  })
  
  output$fin2_tbl <- renderDT({
    res <- fin2_res()
    datatable(data.frame(
      Metric=c("Source","u","Nu","P(X>u)","xi","beta",paste0("VaR(",input$fin2_alpha,")"),paste0("ES(",input$fin2_alpha,")")),
      Value=c(res$d$source_used, res$u, res$risk$Nu, res$risk$pu, res$risk$xi, res$risk$beta, res$risk$VaR, res$risk$ES)
    ), options=list(dom="tip", pageLength=10))
  })
  
  output$fin2_txt <- renderPrint({
    res <- fin2_res()
    cat("Business meaning:\n")
    cat("- VaR(α): loss level exceeded with probability (1-α).\n")
    cat("- ES(α): average loss given you exceeded VaR(α) (finite when xi < 1).\n")
  })
  
  # ========== FIN3 ==========
  fin3_res <- eventReactive(input$fin3_run, {
    d <- get_fin_losses(input$fin3_source, input$fin3_ticker, input$fin3_from, input$fin3_to, input$fin3_nsim)
    r <- as.numeric(na.omit(d$returns))
    validate(need(length(r) >= 1500, "Need a longer series for GARCH+EVT (increase sim n or widen Yahoo range)."))
    
    spec <- ugarchspec(
      variance.model = list(model = "sGARCH", garchOrder = c(1,1)),
      mean.model = list(armaOrder = c(0,0), include.mean = TRUE),
      distribution.model = "norm"
    )
    gfit <- tryCatch(ugarchfit(spec, data = r, solver = "hybrid"), error = function(e) NULL)
    validate(need(!is.null(gfit), "GARCH fit failed."))
    
    z <- as.numeric(residuals(gfit, standardize = TRUE))
    zloss <- pmax(-z, 0)
    
    u <- as.numeric(quantile(zloss, probs = input$fin3_uq, na.rm = TRUE))
    gpd <- fit_gpd(zloss, u)
    validate(need(!is.null(gpd), "GPD on residual losses failed: lower threshold or increase data."))
    
    riskZ <- gpd_var_es(zloss, u, gpd, alpha = input$fin3_alpha)
    
    fc <- tryCatch(ugarchforecast(gfit, n.ahead = 1), error = function(e) NULL)
    validate(need(!is.null(fc), "GARCH forecast failed."))
    
    mu1 <- as.numeric(fitted(fc)); sig1 <- as.numeric(sigma(fc))
    validate(need(length(mu1)==1 && length(sig1)==1, "Forecast returned empty values."))
    
    # Rough mapping to loss% (small-return approx): loss% ~ -100 * return
    VaR_loss_pct <- 100 * (-(mu1) + sig1 * riskZ$VaR)
    ES_loss_pct  <- 100 * (-(mu1) + sig1 * riskZ$ES)
    
    list(d=d, gfit=gfit, zloss=zloss, u=u, gpd=gpd, riskZ=riskZ,
         mu1=mu1, sig1=sig1, VaR_loss_pct=VaR_loss_pct, ES_loss_pct=ES_loss_pct)
  })
  
  output$fin3_vol <- renderPlot({
    res <- fin3_res()
    plot(sigma(res$gfit), type="l", xlab="Time", ylab="Sigma", main="GARCH volatility")
  })
  
  output$fin3_res_tail <- renderPlot({
    res <- fin3_res()
    x <- sort(res$zloss)
    n <- length(x)
    p_emp <- (n:1)/n
    plot(log(x + 1e-9), log(p_emp), pch=16, cex=0.5,
         xlab="log(residual loss)", ylab="log(1-F)", main="Residual loss tail + GPD")
    u <- res$u
    tail_x <- x[x >= u]
    pu <- mean(res$zloss > u)
    xi <- res$gpd$par.ests[["xi"]]
    beta <- res$gpd$par.ests[["beta"]]
    if (abs(xi) < 1e-8) {
      p_gpd <- pu * exp(-(tail_x - u)/beta)
    } else {
      p_gpd <- pu * (1 + xi * (tail_x - u) / beta)^(-1/xi)
    }
    lines(log(tail_x + 1e-9), log(p_gpd + 1e-12), lwd=2)
    abline(v=log(u + 1e-9), lty=2)
  })
  
  output$fin3_tbl <- renderDT({
    res <- fin3_res()
    datatable(data.frame(
      Item=c("Source", "mu(t+1)", "sigma(t+1)", "Residual xi", "Residual beta",
             paste0("Cond VaR(",input$fin3_alpha,") loss%"), paste0("Cond ES(",input$fin3_alpha,") loss%")),
      Value=c(res$d$source_used, res$mu1, res$sig1, res$riskZ$xi, res$riskZ$beta, res$VaR_loss_pct, res$ES_loss_pct)
    ), options=list(dom="tip", pageLength=10))
  })
  
  output$fin3_txt <- renderPrint({
    cat("Meaning:\n- GARCH adapts to changing volatility.\n- EVT models only the extreme residual tail.\n- Conditional VaR/ES scale with forecast sigma(t+1).\n")
  })
  
  # ========== FIN4 ==========
  fin4_res <- eventReactive(input$fin4_run, {
    d <- get_fin_losses(input$fin4_source, input$fin4_ticker, input$fin4_from, input$fin4_to, input$fin4_nsim)
    x <- as.numeric(na.omit(d$losses))
    validate(need(length(x) >= 800, "Not enough data."))
    
    qs <- seq(input$fin4_uq_lo, input$fin4_uq_hi, length.out = 25)
    us <- as.numeric(quantile(x, probs = qs, na.rm = TRUE))
    list(d=d, x=x, qs=qs, us=us)
  })
  
  output$fin4_me <- renderPlot({
    res <- fin4_res()
    me <- mean_excess(res$x, res$us)
    plot(res$us, me, type="b", xlab="u (loss%)", ylab="Mean excess", main="Mean excess vs u")
  })
  
  output$fin4_hill <- renderPlot({
    res <- fin4_res()
    x <- res$x[res$x > 0]
    validate(need(length(x) >= 800, "Need more positive losses for Hill plot."))
    
    h <- evir::hill(x)  # returns list with x=k, y=alpha_hat
    # safer manual plot (avoids method issues)
    plot(h$x, h$y, type="l", xlab="k (upper order stats)", ylab="Hill alpha-hat",
         main="Hill plot (stability region suggests good tail fit)")
  })
  
  # ========== FIN5 ==========
  fin5_res <- eventReactive(input$fin5_run, {
    d <- get_fin_losses(input$fin5_source, input$fin5_ticker, input$fin5_from, input$fin5_to, input$fin5_nsim)
    x <- as.numeric(na.omit(d$losses))
    validate(need(length(x) >= 1000, "Need at least ~1000 points for train/test backtest."))
    
    n <- length(x)
    n_tr <- floor(n * input$fin5_train)
    x_tr <- x[1:n_tr]
    x_te <- x[(n_tr+1):n]
    
    u <- as.numeric(quantile(x_tr, probs = input$fin5_uq, na.rm = TRUE))
    fit <- fit_gpd(x_tr, u)
    validate(need(!is.null(fit), "GPD fit failed: lower u or increase data."))
    
    risk <- gpd_var_es(x_tr, u, fit, alpha = input$fin5_alpha)
    VaR <- risk$VaR
    validate(need(is.finite(VaR), "VaR could not be computed."))
    
    exceed <- x_te > VaR
    kt <- kupiec_test(exceed, p = 1 - input$fin5_alpha)
    
    list(d=d, x_te=x_te, VaR=VaR, kt=kt, risk=risk, u=u)
  })
  
  output$fin5_plot <- renderPlot({
    res <- fin5_res()
    plot(res$x_te, type="l", xlab="Test index", ylab="Loss (%)",
         main=paste0("Holdout losses + EVT VaR(α=", input$fin5_alpha, ")"))
    abline(h=res$VaR, lty=2, lwd=2)
    which_exc <- which(res$x_te > res$VaR)
    if (length(which_exc) > 0) points(which_exc, res$x_te[which_exc], pch=16)
  })
  
  output$fin5_tbl <- renderDT({
    res <- fin5_res()
    datatable(data.frame(
      Item=c("Source","u","xi","beta","VaR(train)","Test exceedances","Test n","Kupiec LR","Kupiec p-value"),
      Value=c(res$d$source_used, res$u, res$risk$xi, res$risk$beta, res$VaR, res$kt$x, res$kt$n, res$kt$LR, res$kt$p.value)
    ), options=list(dom="tip", pageLength=10))
  })
  
  output$fin5_txt <- renderPrint({
    res <- fin5_res()
    cat("Interpretation:\n")
    cat("- Expected exceedance rate ≈ (1-α).\n")
    cat("- Small Kupiec p-value suggests the VaR coverage is inconsistent.\n")
  })
  
  # ========== INS1 ==========
  ins1_res <- eventReactive(input$ins1_run, {
    x <- simulate_severity(input$ins1_n, input$ins1_model)
    validate(need(length(x) >= 1000, "Increase number of claims."))
    
    u <- as.numeric(quantile(x, probs = input$ins1_uq, na.rm = TRUE))
    fit <- fit_gpd(x, u)
    validate(need(!is.null(fit), "GPD fit failed: lower u or increase n."))
    
    risk <- gpd_var_es(x, u, fit, alpha = input$ins1_alpha)
    list(x=x, u=u, fit=fit, risk=risk)
  })
  
  output$ins1_me <- renderPlot({
    res <- ins1_res()
    u_grid <- as.numeric(quantile(res$x, probs=seq(0.80,0.99,by=0.01), na.rm=TRUE))
    me <- mean_excess(res$x, u_grid)
    plot(u_grid, me, type="b", xlab="u", ylab="Mean excess", main="Mean-excess (severity)")
    abline(v=res$u, lty=2)
  })
  
  output$ins1_tail <- renderPlot({
    res <- ins1_res()
    x <- sort(res$x)
    n <- length(x)
    p_emp <- (n:1)/n
    plot(log(x + 1e-9), log(p_emp), pch=16, cex=0.5,
         xlab="log(severity)", ylab="log(1-F)", main="Severity tail + GPD")
    u <- res$u
    tail_x <- x[x >= u]
    pu <- mean(res$x > u)
    xi <- res$fit$par.ests[["xi"]]
    beta <- res$fit$par.ests[["beta"]]
    if (abs(xi) < 1e-8) {
      p_gpd <- pu * exp(-(tail_x - u)/beta)
    } else {
      p_gpd <- pu * (1 + xi * (tail_x - u) / beta)^(-1/xi)
    }
    lines(log(tail_x + 1e-9), log(p_gpd + 1e-12), lwd=2)
    abline(v=log(u + 1e-9), lty=2)
  })
  
  output$ins1_tbl <- renderDT({
    res <- ins1_res()
    datatable(data.frame(
      Metric=c("u","Nu","P(X>u)","xi","beta",paste0("VaR(",input$ins1_alpha,")"),paste0("ES(",input$ins1_alpha,")")),
      Value=c(res$u, res$risk$Nu, res$risk$pu, res$risk$xi, res$risk$beta, res$risk$VaR, res$risk$ES)
    ), options=list(dom="tip", pageLength=10))
  })
  
  output$ins1_txt <- renderPrint({
    cat("Business meaning:\n- High-layer pricing and capital depend on the tail shape xi.\n- If xi is large, extreme claims dominate risk.\n")
  })
  
  # ========== INS2 ==========
  ins2_res <- eventReactive(input$ins2_run, {
    x <- simulate_severity(input$ins2_n, input$ins2_model)
    u <- as.numeric(quantile(x, probs = input$ins2_uq, na.rm = TRUE))
    fit <- fit_gpd(x, u)
    validate(need(!is.null(fit), "GPD fit failed: lower u or increase n."))
    
    sev_sim <- simulate_semiparam_severity(x, u, fit, n_sim = input$ins2_sim)
    R <- input$ins2_R
    L <- input$ins2_L
    layer <- pmin(pmax(sev_sim - R, 0), L)
    
    list(u=u, fit=fit, layer=layer, EL=mean(layer), q95=quantile(layer,0.95), q99=quantile(layer,0.99),
         R=R, L=L)
  })
  
  output$ins2_plot <- renderPlot({
    res <- ins2_res()
    hist(res$layer, breaks=60, main="Layer payments (simulation)", xlab="Payment", border=NA)
    abline(v=res$EL, lty=2, lwd=2)
  })
  
  output$ins2_tbl <- renderDT({
    res <- ins2_res()
    datatable(data.frame(
      Item=c("u","xi","beta","Retention R","Limit L","Expected layer loss","Layer 95%","Layer 99%"),
      Value=c(res$u, res$fit$par.ests[["xi"]], res$fit$par.ests[["beta"]], res$R, res$L, res$EL, res$q95, res$q99)
    ), options=list(dom="tip", pageLength=10))
  })
  
  output$ins2_txt <- renderPrint({
    cat("Business meaning:\n- Expected layer loss is the pure premium for the reinsurance layer.\n- Tail modeling matters most when R is high.\n")
  })
  
  # ========== INS3 ==========
  ins3_res <- eventReactive(input$ins3_run, {
    x <- simulate_severity(input$ins3_hist_n, input$ins3_model)
    u <- as.numeric(quantile(x, probs = input$ins3_uq, na.rm = TRUE))
    fit <- fit_gpd(x, u)
    validate(need(!is.null(fit), "GPD fit failed: lower u or increase severity sample size."))
    
    years <- input$ins3_years
    lam <- input$ins3_lambda
    
    # Ensure we draw enough severities (sum of Poisson can exceed years*lam)
    N <- rpois(years, lam)
    totalN <- sum(N)
    sev_pool <- simulate_semiparam_severity(x, u, fit, n_sim = max(2000, totalN))
    
    agg <- numeric(years)
    idx <- 1
    for (i in 1:years) {
      ni <- N[i]
      if (ni > 0) {
        agg[i] <- sum(sev_pool[idx:(idx+ni-1)])
        idx <- idx + ni
      }
    }
    
    alpha <- input$ins3_alpha
    VaR <- as.numeric(quantile(agg, probs = alpha))
    ES  <- mean(agg[agg >= VaR])
    
    list(u=u, fit=fit, agg=agg, VaR=VaR, ES=ES)
  })
  
  output$ins3_plot <- renderPlot({
    res <- ins3_res()
    hist(res$agg, breaks=60, main="Annual aggregate losses", xlab="Aggregate", border=NA)
    abline(v=res$VaR, lty=2, lwd=2)
  })
  
  output$ins3_tbl <- renderDT({
    res <- ins3_res()
    datatable(data.frame(
      Item=c("Severity u","xi","beta",paste0("Agg VaR(",input$ins3_alpha,")"),paste0("Agg ES(",input$ins3_alpha,")")),
      Value=c(res$u, res$fit$par.ests[["xi"]], res$fit$par.ests[["beta"]], res$VaR, res$ES)
    ), options=list(dom="tip", pageLength=10))
  })
  
  output$ins3_txt <- renderPrint({
    cat("Business meaning:\n- Annual VaR/ES are solvency-style capital numbers.\n- Heavy-tail severity increases ES strongly.\n")
  })
  
  # ========== INS4 ==========
  ins4_res <- eventReactive(input$ins4_run, {
    maxima <- evd::rgev(input$ins4_years, loc=input$ins4_loc, scale=input$ins4_scale, shape=input$ins4_shape)
    fit <- fit_gev(maxima)
    validate(need(!is.null(fit), "GEV fit failed."))
    
    rl <- gev_return_level(fit, k = input$ins4_k)
    list(maxima=maxima, fit=fit, rl=rl)
  })
  
  output$ins4_plot <- renderPlot({
    res <- ins4_res()
    plot(res$maxima, type="h", xlab="Year", ylab="Annual max", main="Annual maxima (simulated)")
    abline(h=res$rl, lty=2, lwd=2)
  })
  
  output$ins4_tbl <- renderDT({
    res <- ins4_res()
    est <- res$fit$estimate
    datatable(data.frame(Parameter=names(est), Estimate=as.numeric(est)),
              options=list(dom="tip", pageLength=5))
  })
  
  output$ins4_txt <- renderPrint({
    res <- ins4_res()
    cat("Return level (exceeded about once every", input$ins4_k, "years):\n")
    cat(sprintf("  %.3f\n", res$rl))
  })
  
  # ========== INS5 ==========
  ins5_res <- eventReactive(input$ins5_run, {
    x <- simulate_severity(input$ins5_n, input$ins5_model)
    qs <- seq(input$ins5_uq_lo, input$ins5_uq_hi, length.out = 25)
    us <- as.numeric(quantile(x, probs = qs, na.rm = TRUE))
    alpha <- input$ins5_alpha
    
    out <- data.frame(uq=qs, u=us, Nu=NA, xi=NA, beta=NA, VaR=NA, ES=NA)
    
    for (i in seq_along(us)) {
      u <- us[i]
      fit <- fit_gpd(x, u)
      if (!is.null(fit)) {
        risk <- gpd_var_es(x, u, fit, alpha = alpha)
        out$Nu[i] <- risk$Nu
        out$xi[i] <- risk$xi
        out$beta[i] <- risk$beta
        out$VaR[i] <- risk$VaR
        out$ES[i]  <- risk$ES
      }
    }
    list(out=out, alpha=alpha)
  })
  
  output$ins5_xi <- renderPlot({
    res <- ins5_res()
    plot(res$out$u, res$out$xi, type="b", xlab="u", ylab="xi",
         main="xi stability vs threshold u")
  })
  
  output$ins5_var <- renderPlot({
    res <- ins5_res()
    plot(res$out$u, res$out$VaR, type="b", xlab="u", ylab=paste0("VaR(",res$alpha,")"),
         main="VaR sensitivity vs threshold u")
  })
  
  output$ins5_tbl <- renderDT({
    res <- ins5_res()
    datatable(res$out, options=list(pageLength=10))
  })
}

shinyApp(ui, server)
