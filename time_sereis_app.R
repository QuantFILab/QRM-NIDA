# app.R
# Two-page Shiny learning dashboard:
# 1) Learning Page (Yahoo Finance case study)
# 2) Simulate Data (theory + simulation + interactive plots)
# Run: shiny::runApp()

library(shiny)
library(shinydashboard)
library(quantmod)
library(xts)
library(plotly)
library(DT)
library(forecast)
library(rugarch)
library(tseries)
library(MASS)

`%||%` <- function(a, b) if (!is.null(a)) a else b

# -----------------------------
# Helpers
# -----------------------------
fetch_yahoo <- function(symbol, from, to, price_field = c("Adjusted", "Close")) {
  price_field <- match.arg(price_field)
  xt <- tryCatch(
    getSymbols(symbol, src = "yahoo", from = from, to = to, auto.assign = FALSE, warnings = FALSE),
    error = function(e) stop("Yahoo download failed. Check ticker/date range.\n", e$message)
  )
  
  px <- tryCatch(
    if (price_field == "Adjusted") Ad(xt) else Cl(xt),
    error = function(e) Cl(xt)
  )
  
  px <- px[is.finite(px)]
  ret <- diff(log(px))
  ret <- na.omit(ret)
  
  if (NROW(ret) < 200) stop("Not enough return points (need at least ~200). Try a longer date range.")
  
  list(symbol = symbol, px = px, ret = ret)
}

fetch_yahoo_multi_returns <- function(symbols, from, to, price_field = c("Adjusted", "Close")) {
  price_field <- match.arg(price_field)
  
  rets <- lapply(symbols, function(sym) {
    sym <- trimws(sym)
    if (!nzchar(sym)) return(NULL)
    xt <- tryCatch(
      getSymbols(sym, src = "yahoo", from = from, to = to, auto.assign = FALSE, warnings = FALSE),
      error = function(e) NULL
    )
    if (is.null(xt)) return(NULL)
    
    px <- tryCatch(
      if (price_field == "Adjusted") Ad(xt) else Cl(xt),
      error = function(e) Cl(xt)
    )
    
    px <- px[is.finite(px)]
    r <- na.omit(diff(log(px)))
    if (NROW(r) < 200) return(NULL)
    colnames(r) <- sym
    r
  })
  
  rets <- Filter(Negate(is.null), rets)
  if (length(rets) < 2) stop("Need at least 2 valid tickers with enough data.")
  
  R <- do.call(merge, c(rets, list(all = FALSE)))
  R <- na.omit(R)
  
  if (NROW(R) < 200) stop("After aligning dates, not enough rows. Try longer range or different tickers.")
  R
}

acf_df <- function(x, lag_max = 40) {
  a <- acf(x, plot = FALSE, lag.max = lag_max, na.action = na.omit)
  data.frame(lag = as.numeric(a$lag)[-1], value = as.numeric(a$acf)[-1])
}
pacf_df <- function(x, lag_max = 40) {
  p <- pacf(x, plot = FALSE, lag.max = lag_max, na.action = na.omit)
  data.frame(lag = seq_along(p$acf), value = as.numeric(p$acf))
}
acf_plotly_bar <- function(df, title, ci, lag_max) {
  plot_ly(df, x = ~lag, y = ~value, type = "bar") |>
    add_segments(x = 0, xend = lag_max, y = ci,  yend = ci,  inherit = FALSE) |>
    add_segments(x = 0, xend = lag_max, y = -ci, yend = -ci, inherit = FALSE) |>
    layout(title = title,
           xaxis = list(title = "Lag"),
           yaxis = list(title = "Value"),
           bargap = 0.2)
}
lb_table <- function(x, lag = 10) {
  out <- Box.test(x, lag = lag, type = "Ljung-Box")
  data.frame(statistic = unname(out$statistic), df = unname(out$parameter), p_value = out$p.value)
}

# Cross-correlation at lag h: corr(x_{t+h}, y_t)
crosscorr_at_lag <- function(x, y, h) {
  n <- length(x)
  if (h >= 0) {
    if (h >= n - 2) return(NA_real_)
    xs <- x[(h + 1):n]
    ys <- y[1:(n - h)]
  } else {
    hh <- -h
    if (hh >= n - 2) return(NA_real_)
    xs <- x[1:(n - hh)]
    ys <- y[(hh + 1):n]
  }
  suppressWarnings(cor(xs, ys, use = "pairwise.complete.obs"))
}
crosscorr_df <- function(x, y, lag_max = 25) {
  lags <- -lag_max:lag_max
  vals <- vapply(lags, function(h) crosscorr_at_lag(x, y, h), numeric(1))
  data.frame(lag = lags, value = vals)
}

# Convert covariance-like matrix Q to correlation matrix P
cov_to_cor <- function(Q) {
  d <- sqrt(diag(Q))
  d[d == 0] <- NA_real_
  Dinv <- diag(1 / d)
  P <- Dinv %*% Q %*% Dinv
  (P + t(P)) / 2
}

# ES for standardized Normal and standardized Student-t (teaching-friendly closed form)
esz_norm <- function(alpha) -dnorm(qnorm(alpha)) / alpha
esz_std_t <- function(alpha, df) {
  q <- qt(alpha, df = df)
  - (dt(q, df = df) * (df + q^2)) / ((df - 1) * alpha)
}

# -----------------------------
# Simulation helpers
# -----------------------------
simulate_arma_family <- function(model = c("WN", "AR1", "MA1", "ARMA11"),
                                 n = 1000, mu = 0, sigma = 1,
                                 phi = 0.5, theta = 0.5, seed = 1) {
  model <- match.arg(model)
  set.seed(seed)
  
  # arima.sim produces zero-mean series; we add mu at end
  x <- switch(
    model,
    "WN"     = rnorm(n, mean = 0, sd = sigma),
    "AR1"    = as.numeric(arima.sim(model = list(ar = phi), n = n, sd = sigma)),
    "MA1"    = as.numeric(arima.sim(model = list(ma = theta), n = n, sd = sigma)),
    "ARMA11" = as.numeric(arima.sim(model = list(ar = phi, ma = theta), n = n, sd = sigma))
  )
  x + mu
}

simulate_garch11 <- function(n = 2000, mu = 0, omega = 0.00001, alpha1 = 0.05, beta1 = 0.90,
                             dist = c("norm", "std"), shape = 8, seed = 1) {
  dist <- match.arg(dist)
  set.seed(seed)
  
  fixed <- list(mu = mu, omega = omega, alpha1 = alpha1, beta1 = beta1)
  if (dist == "std") fixed$shape <- shape
  
  spec <- ugarchspec(
    variance.model = list(model = "sGARCH", garchOrder = c(1, 1)),
    mean.model = list(armaOrder = c(0, 0), include.mean = TRUE),
    distribution.model = dist,
    fixed.pars = fixed
  )
  path <- ugarchpath(spec, n.sim = n, m.sim = 1)
  
  p <- path@path
  x <- as.numeric(p$seriesSim)
  sig <- as.numeric(p$sigmaSim)
  
  list(x = x, sigma = sig)
}

simulate_var1_2d <- function(n = 500, Phi = matrix(c(0.6, 0.2, -0.1, 0.5), 2, 2),
                             sd_eps = 1, rho_eps = 0.2, seed = 1) {
  set.seed(seed)
  Sigma <- matrix(c(sd_eps^2, rho_eps*sd_eps^2,
                    rho_eps*sd_eps^2, sd_eps^2), 2, 2)
  
  eps <- MASS::mvrnorm(n = n, mu = c(0, 0), Sigma = Sigma)
  
  X <- matrix(0, n, 2)
  X[1, ] <- eps[1, ]
  for (t in 2:n) X[t, ] <- as.numeric(Phi %*% X[t - 1, ]) + eps[t, ]
  
  eig <- eigen(Phi)$values
  list(X = X, eps = eps, Phi = Phi, eig = eig)
}

simulate_dcc11_2d <- function(n = 800, alpha = 0.05, beta = 0.90, rho_longrun = 0.5, seed = 1) {
  set.seed(seed)
  Pc <- matrix(c(1, rho_longrun, rho_longrun, 1), 2, 2)
  
  # Lecture-style recursion uses P_{t-1} in the update step (teaching recursion)
  P_prev <- Pc
  y <- matrix(NA_real_, n, 2)
  rho_t <- numeric(n)
  
  for (t in 1:n) {
    P <- P_prev
    # simulate y_t ~ N(0, P)
    L <- chol(P) # upper triangular
    y[t, ] <- as.numeric(t(L) %*% rnorm(2))
    rho_t[t] <- P[1, 2]
    
    Q <- (1 - alpha - beta) * Pc + alpha * (y[t, ] %o% y[t, ]) + beta * P
    P_prev <- cov_to_cor(Q)
  }
  
  list(y = y, rho_t = rho_t, Pc = Pc)
}

# -----------------------------
# UI
# -----------------------------
ui <- dashboardPage(
  dashboardHeader(title = "Time Series Learning (Yahoo Finance + Simulation)"),
  dashboardSidebar(
    sidebarMenu(
      menuItem("Learning Page", tabName = "learn", icon = icon("book-open")),
      menuItem("Simulate Data", tabName = "simulate", icon = icon("flask"))
    )
  ),
  dashboardBody(
    withMathJax(),
    tags$head(tags$style(HTML("
      .small-note { color:#666; font-size:12px; }
      .theory { font-size:14px; line-height:1.45; }
      .kpi { font-size:13px; }
    "))),
    tabItems(
      
      # ==========================================================
      # PAGE 1 — Learning (Yahoo Finance)
      # ==========================================================
      tabItem(
        tabName = "learn",
        
        fluidRow(
          box(
            width = 12, status = "primary", solidHeader = TRUE, title = "Case Study Inputs (Yahoo Finance)",
            fluidRow(
              column(3,
                     textInput("ticker", "Ticker", value = "^SET.BK"),
                     selectInput("price_field", "Price series", choices = c("Adjusted", "Close"), selected = "Adjusted")
              ),
              column(3,
                     dateInput("from", "From", value = Sys.Date() - 365*5),
                     dateInput("to", "To", value = Sys.Date())
              ),
              column(3,
                     numericInput("lag_max", "Max lag (ACF/PACF)", value = 40, min = 10, max = 200),
                     numericInput("lb_lag", "Ljung–Box lag", value = 10, min = 5, max = 60)
              ),
              column(3,
                     actionButton("load_btn", "Load data", icon = icon("download")),
                     br(), br(),
                     tags$div(class = "small-note",
                              "Examples: ^SET.BK, PTT.BK, CPALL.BK, AAPL, ^GSPC, SPY, BTC-USD")
              )
            ),
            verbatimTextOutput("data_summary")
          )
        ),
        
        # 1) Stationarity
        fluidRow(
          box(
            width = 12, status = "info", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "1) Stationarity (Definition + interactive price/return plots)",
            tags$div(
              class = "theory",
              HTML("
              <b>Definition (covariance-stationary / weakly stationary).</b>
              A process \\(\\{X_t\\}\\) is covariance-stationary if:
              <ol>
                <li>\\(\\mathbb{E}[X_t]=\\mu\\) is constant</li>
                <li>\\(\\mathrm{Var}(X_t)=\\gamma(0)\\) is constant</li>
                <li>\\(\\mathrm{Cov}(X_t, X_{t-h})=\\gamma(h)\\) depends only on lag \\(h\\)</li>
              </ol>
              <b>Why returns?</b> Prices often trend (non-stationary). Log-returns \\(r_t=\\Delta\\log(P_t)\\) are often closer to stationary.
              <br/><br/>
              <b>ADF test (unit root test).</b> Null hypothesis: unit root (non-stationary). Small p-value suggests stationarity.
              ")
            ),
            fluidRow(
              column(8, plotlyOutput("price_return_plot", height = "450px")),
              column(4,
                     tags$div(class="kpi", verbatimTextOutput("adf_out")),
                     tags$div(class="small-note",
                              "Tip: Even if returns look stationary, volatility can still be time-varying (see ARCH/GARCH).")
              )
            )
          )
        ),
        
        # 2) ACF / PACF
        fluidRow(
          box(
            width = 12, status = "info", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "2) ACF & PACF (Definitions + interactive correlograms)",
            tags$div(
              class = "theory",
              HTML("
              <b>ACF.</b> \\(\\rho(h)=\\gamma(h)/\\gamma(0)\\), where \\(\\gamma(h)=\\mathrm{Cov}(X_t,X_{t-h})\\).<br/>
              <b>PACF.</b> Correlation between \\(X_t\\) and \\(X_{t-h}\\) after removing linear effects of lags \\(1..h-1\\).<br/><br/>
              <b>Box–Jenkins (rule of thumb):</b>
              <ul>
                <li>AR(p): PACF cuts off after p, ACF tails off</li>
                <li>MA(q): ACF cuts off after q, PACF tails off</li>
                <li>ARMA: both tail off</li>
              </ul>
              The dashed lines are approximately \\(\\pm 1.96/\\sqrt{n}\\).
              ")
            ),
            fluidRow(
              column(6, plotlyOutput("acf_plot", height = "320px")),
              column(6, plotlyOutput("pacf_plot", height = "320px"))
            ),
            fluidRow(
              column(6, plotlyOutput("acf_sq_plot", height = "320px")),
              column(6, DTOutput("lb_table"))
            )
          )
        ),
        
        # 3) ARMA
        fluidRow(
          box(
            width = 12, status = "warning", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "3) ARMA (Mean model) — Definition + conditions + interactive diagnostics",
            tags$div(
              class = "theory",
              HTML("
              <b>ARMA(p,q).</b>
              \\[
                X_t - \\phi_1X_{t-1}-\\cdots-\\phi_pX_{t-p}
                = \\varepsilon_t + \\theta_1\\varepsilon_{t-1}+\\cdots+\\theta_q\\varepsilon_{t-q}
              \\]<br/>
              <b>Key conditions:</b>
              <ul>
                <li><b>Causality/stationarity (AR part):</b> roots of \\(\\phi(z)=0\\) lie outside \\(|z|\\le 1\\)</li>
                <li><b>Invertibility (MA part):</b> roots of \\(\\theta(z)=0\\) lie outside \\(|z|\\le 1\\)</li>
              </ul>
              ")
            ),
            fluidRow(
              column(
                4,
                checkboxInput("arma_auto", "Auto-select ARMA (auto.arima)", TRUE),
                conditionalPanel(
                  condition = "!input.arma_auto",
                  numericInput("arma_p", "p", value = 1, min = 0, max = 10),
                  numericInput("arma_q", "q", value = 1, min = 0, max = 10)
                ),
                actionButton("fit_arma_btn", "Fit ARMA", icon = icon("wave-square")),
                br(), br(),
                verbatimTextOutput("arma_summary")
              ),
              column(
                8,
                plotlyOutput("arma_diag_plot", height = "520px"),
                DTOutput("arma_lb")
              )
            )
          )
        ),
        
        # 4) GARCH
        fluidRow(
          box(
            width = 12, status = "danger", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "4) ARCH/GARCH (Volatility) — Definitions + conditions + interactive diagnostics",
            tags$div(
              class = "theory",
              HTML("
              <b>ARCH/GARCH idea:</b> volatility clustering via time-varying conditional variance.<br/><br/>
              <b>GARCH(p,q):</b>
              \\(\\sigma_t^2 = \\omega + \\sum_{i=1}^p \\alpha_i X_{t-i}^2 + \\sum_{j=1}^q \\beta_j \\sigma_{t-j}^2\\).<br/>
              <b>Typical stationarity condition (GARCH(1,1)):</b> \\(\\alpha_1+\\beta_1<1\\).
              ")
            ),
            fluidRow(
              column(
                4,
                numericInput("garch_p", "p (ARCH terms)", value = 1, min = 0, max = 5),
                numericInput("garch_q", "q (GARCH terms)", value = 1, min = 0, max = 5),
                selectInput("garch_dist", "Innovation distribution", choices = c("norm", "std"), selected = "std"),
                actionButton("fit_garch_btn", "Fit GARCH", icon = icon("bolt")),
                br(), br(),
                verbatimTextOutput("garch_summary")
              ),
              column(8, plotlyOutput("garch_diag_plot", height = "520px"))
            )
          )
        ),
        
        # 5) Forecast + VaR/ES
        fluidRow(
          box(
            width = 12, status = "success", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "5) Forecast Volatility + VaR / ES — Definitions + interactive forecast plots",
            tags$div(
              class = "theory",
              HTML("
              <b>VaR:</b> \\(\\mathrm{VaR}_{\\alpha}^{t+1} = \\inf\\{x : \\mathbb{P}(X_{t+1}\\le x\\mid\\mathcal{F}_t)\\ge \\alpha\\}\\).<br/>
              <b>ES:</b> \\(\\mathrm{ES}_{\\alpha}^{t+1} = \\mathbb{E}[X_{t+1}\\mid X_{t+1}\\le \\mathrm{VaR}_{\\alpha}^{t+1},\\mathcal{F}_t]\\).<br/><br/>
              If \\(X_{t+1}=\\mu_{t+1}+\\sigma_{t+1}Z_{t+1}\\), then
              \\(\\mathrm{VaR}=\\mu_{t+1}+\\sigma_{t+1}q_{\\alpha}\\) and similarly for ES.
              ")
            ),
            fluidRow(
              column(
                4,
                numericInput("h", "Forecast horizon (days)", value = 20, min = 1, max = 250),
                sliderInput("alpha", "alpha", min = 0.001, max = 0.10, value = 0.05, step = 0.001),
                actionButton("forecast_btn", "Forecast + VaR/ES", icon = icon("calculator")),
                br(), br(),
                tags$div(class="small-note", "Requires a fitted GARCH model above.")
              ),
              column(
                8,
                plotlyOutput("risk_plot", height = "420px"),
                DTOutput("risk_table")
              )
            )
          )
        )
      ),
      
      # ==========================================================
      # PAGE 2 — Simulate Data (Theory + Interactive Simulation)
      # ==========================================================
      tabItem(
        tabName = "simulate",
        
        fluidRow(
          box(
            width = 12, status = "primary", solidHeader = TRUE, title = "Simulation Lab (No Yahoo needed) — definitions + theorems + interactive plots",
            tags$div(class="small-note",
                     "Use this page to *learn* model behavior by generating synthetic series. Each section includes theory + interactive plots.")
          )
        ),
        
        # --- A) ARMA family simulation
        fluidRow(
          box(
            width = 12, status = "info", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "A) White Noise / AR / MA / ARMA Simulation",
            tags$div(class="theory", HTML("
              <b>White Noise (WN):</b> uncorrelated series with constant mean/variance.<br/>
              <b>ARMA(p,q):</b>
              \\(\\phi(B)X_t = \\theta(B)\\varepsilon_t\\).<br/>
              <b>Key theorem facts:</b> stationary & causal iff \\(\\phi(z)\\neq0\\) for \\(|z|\\le1\\); invertible iff \\(\\theta(z)\\neq0\\) for \\(|z|\\le1\\).<br/>
              <b>ACF band:</b> for WN, sample ACF is approximately within \\(\\pm 1.96/\\sqrt{n}\\) (large n).
            ")),
            fluidRow(
              column(
                3,
                selectInput("sim_arma_model", "Model", choices = c("WN", "AR1", "MA1", "ARMA11"), selected = "ARMA11"),
                numericInput("sim_arma_n", "n", value = 1000, min = 200, max = 20000),
                numericInput("sim_arma_mu", "mu", value = 0),
                numericInput("sim_arma_sigma", "sigma (innovation sd)", value = 1, min = 0.0001)
              ),
              column(
                3,
                sliderInput("sim_arma_phi", "phi (AR1)", min = -0.99, max = 0.99, value = 0.5, step = 0.01),
                sliderInput("sim_arma_theta", "theta (MA1)", min = -0.99, max = 0.99, value = 0.5, step = 0.01),
                numericInput("sim_arma_lag", "ACF/PACF max lag", value = 40, min = 10, max = 300),
                numericInput("sim_arma_seed", "seed", value = 1, min = 1)
              ),
              column(
                3,
                actionButton("sim_arma_btn", "Simulate", icon = icon("play")),
                br(), br(),
                verbatimTextOutput("sim_arma_checks")
              ),
              column(
                3,
                DTOutput("sim_arma_lb")
              )
            ),
            fluidRow(
              column(6, plotlyOutput("sim_arma_ts", height = "280px")),
              column(6, plotlyOutput("sim_arma_hist", height = "280px"))
            ),
            fluidRow(
              column(6, plotlyOutput("sim_arma_acf", height = "280px")),
              column(6, plotlyOutput("sim_arma_pacf", height = "280px"))
            )
          )
        ),
        
        # --- B) GARCH simulation
        fluidRow(
          box(
            width = 12, status = "danger", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "B) GARCH(1,1) Simulation (Volatility Clustering)",
            tags$div(class="theory", HTML("
              <b>GARCH(1,1):</b> \\(\\sigma_t^2=\\omega+\\alpha X_{t-1}^2+\\beta\\sigma_{t-1}^2\\).<br/>
              <b>Typical stationarity condition:</b> \\(\\alpha+\\beta<1\\) (finite unconditional variance).<br/>
              You should see weak ACF in returns, but strong ACF in returns², plus time-varying \\(\\sigma_t\\).
            ")),
            fluidRow(
              column(
                3,
                numericInput("sim_garch_n", "n", value = 2000, min = 500, max = 50000),
                numericInput("sim_garch_mu", "mu", value = 0),
                numericInput("sim_garch_omega", "omega", value = 0.00001, min = 0.0),
                sliderInput("sim_garch_alpha", "alpha", min = 0, max = 0.50, value = 0.05, step = 0.01)
              ),
              column(
                3,
                sliderInput("sim_garch_beta", "beta", min = 0, max = 0.99, value = 0.90, step = 0.01),
                selectInput("sim_garch_dist", "dist", choices = c("norm", "std"), selected = "std"),
                numericInput("sim_garch_df", "df (if std)", value = 8, min = 3, max = 50),
                numericInput("sim_garch_seed", "seed", value = 1, min = 1)
              ),
              column(
                3,
                numericInput("sim_garch_lag", "ACF max lag", value = 40, min = 10, max = 300),
                actionButton("sim_garch_btn", "Simulate", icon = icon("play")),
                br(), br(),
                verbatimTextOutput("sim_garch_checks")
              ),
              column(
                3,
                DTOutput("sim_garch_lb")
              )
            ),
            fluidRow(
              column(6, plotlyOutput("sim_garch_ts", height = "280px")),
              column(6, plotlyOutput("sim_garch_sigma", height = "280px"))
            ),
            fluidRow(
              column(6, plotlyOutput("sim_garch_acf", height = "280px")),
              column(6, plotlyOutput("sim_garch_acf2", height = "280px"))
            )
          )
        ),
        
        # --- C) VAR simulation
        fluidRow(
          box(
            width = 12, status = "warning", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "C) VAR(1) Simulation (2D) + Cross-correlation",
            tags$div(class="theory", HTML("
              <b>VAR(1):</b> \\(X_t = \\Phi X_{t-1} + \\varepsilon_t\\).<br/>
              <b>Stationarity condition:</b> all eigenvalues of \\(\\Phi\\) have modulus < 1.<br/>
              Use the cross-correlogram to see lead/lag relationships.
            ")),
            fluidRow(
              column(
                3,
                numericInput("sim_var_n", "n", value = 600, min = 200, max = 20000),
                numericInput("sim_var_sd", "eps sd", value = 1, min = 0.0001),
                sliderInput("sim_var_rho", "eps corr (rho)", min = -0.95, max = 0.95, value = 0.2, step = 0.01),
                numericInput("sim_var_seed", "seed", value = 1, min = 1),
                actionButton("sim_var_btn", "Simulate", icon = icon("play"))
              ),
              column(
                3,
                sliderInput("sim_phi11", "Phi[1,1]", min = -0.99, max = 0.99, value = 0.60, step = 0.01),
                sliderInput("sim_phi12", "Phi[1,2]", min = -0.99, max = 0.99, value = 0.20, step = 0.01),
                sliderInput("sim_phi21", "Phi[2,1]", min = -0.99, max = 0.99, value = -0.10, step = 0.01),
                sliderInput("sim_phi22", "Phi[2,2]", min = -0.99, max = 0.99, value = 0.50, step = 0.01)
              ),
              column(
                3,
                numericInput("sim_var_lag", "Cross-corr max lag", value = 25, min = 5, max = 300),
                verbatimTextOutput("sim_var_eig")
              ),
              column(
                3,
                plotlyOutput("sim_var_corr_heat", height = "260px")
              )
            ),
            fluidRow(
              column(6, plotlyOutput("sim_var_ts", height = "280px")),
              column(6, plotlyOutput("sim_var_crosscorr", height = "280px"))
            )
          )
        ),
        
        # --- D) DCC simulation
        fluidRow(
          box(
            width = 12, status = "success", solidHeader = TRUE, collapsible = TRUE, collapsed = FALSE,
            title = "D) DCC(1,1) Simulation (2D) — Dynamic Correlation Path",
            tags$div(class="theory", HTML("
              <b>DCC idea:</b> correlation evolves dynamically around a long-run correlation \\(P_c\\).<br/>
              <b>Constraint:</b> \\(\\alpha\\ge0,\\beta\\ge0,\\alpha+\\beta<1\\) (stable recursion).<br/>
              This demo simulates devolatilized shocks \\(Y_t\\sim N(0,P_t)\\) with \\(P_t\\) updating over time.
            ")),
            fluidRow(
              column(
                3,
                numericInput("sim_dcc_n", "n", value = 800, min = 200, max = 50000),
                sliderInput("sim_dcc_alpha", "alpha", min = 0, max = 0.30, value = 0.05, step = 0.01),
                sliderInput("sim_dcc_beta", "beta", min = 0, max = 0.98, value = 0.90, step = 0.01),
                sliderInput("sim_dcc_rho", "long-run corr (Pc[1,2])", min = -0.95, max = 0.95, value = 0.5, step = 0.01),
                numericInput("sim_dcc_seed", "seed", value = 1, min = 1),
                actionButton("sim_dcc_btn", "Simulate", icon = icon("play")),
                br(), br(),
                verbatimTextOutput("sim_dcc_check")
              ),
              column(
                9,
                plotlyOutput("sim_dcc_rho_path", height = "280px"),
                plotlyOutput("sim_dcc_y", height = "280px")
              )
            )
          )
        )
      )
    )
  )
)

# -----------------------------
# Server
# -----------------------------
server <- function(input, output, session) {
  
  # -----------------------------
  # LEARN PAGE (Yahoo)
  # -----------------------------
  data_obj <- eventReactive(input$load_btn, {
    sym <- trimws(input$ticker)
    validate(
      need(nchar(sym) > 0, "Please enter a ticker."),
      need(input$from < input$to, "From must be earlier than To.")
    )
    withProgress(message = "Loading Yahoo Finance data...", value = 0.2, {
      d <- fetch_yahoo(sym, input$from, input$to, input$price_field)
      incProgress(0.8)
      d
    })
  }, ignoreInit = FALSE)
  
  output$data_summary <- renderPrint({
    d <- data_obj()
    x <- as.numeric(d$ret)
    cat("Ticker:", d$symbol, "\n")
    cat("Price points:", NROW(d$px), "\n")
    cat("Return points:", NROW(d$ret), "\n\n")
    cat("Returns mean:", mean(x), "\n")
    cat("Returns sd:", sd(x), "\n")
    cat("Returns min/max:", min(x), "/", max(x), "\n")
  })
  
  output$adf_out <- renderPrint({
    d <- data_obj()
    x <- as.numeric(d$ret)
    cat("ADF test (unit root):\n")
    print(tseries::adf.test(x))
  })
  
  output$price_return_plot <- renderPlotly({
    d <- data_obj()
    px_df <- data.frame(date = as.Date(index(d$px)), price = as.numeric(d$px))
    rt_df <- data.frame(date = as.Date(index(d$ret)), ret = as.numeric(d$ret))
    
    p1 <- plot_ly(px_df, x = ~date, y = ~price, type = "scatter", mode = "lines") |>
      layout(title = paste0(d$symbol, " Price (", input$price_field, ")"),
             xaxis = list(title = "Date"), yaxis = list(title = "Price"))
    
    p2 <- plot_ly(rt_df, x = ~date, y = ~ret, type = "scatter", mode = "lines") |>
      layout(title = paste0(d$symbol, " Log-Returns"),
             xaxis = list(title = "Date"), yaxis = list(title = "Return"))
    
    subplot(p1, p2, nrows = 2, shareX = TRUE, titleY = TRUE)
  })
  
  output$acf_plot <- renderPlotly({
    d <- data_obj()
    x <- as.numeric(d$ret)
    lag_max <- input$lag_max
    ci <- 1.96 / sqrt(length(x))
    df <- acf_df(x, lag_max)
    acf_plotly_bar(df, "ACF(returns)", ci, lag_max)
  })
  
  output$pacf_plot <- renderPlotly({
    d <- data_obj()
    x <- as.numeric(d$ret)
    lag_max <- input$lag_max
    ci <- 1.96 / sqrt(length(x))
    df <- pacf_df(x, lag_max)
    acf_plotly_bar(df, "PACF(returns)", ci, lag_max)
  })
  
  output$acf_sq_plot <- renderPlotly({
    d <- data_obj()
    x <- as.numeric(d$ret)
    lag_max <- input$lag_max
    ci <- 1.96 / sqrt(length(x))
    df <- acf_df(x^2, lag_max)
    acf_plotly_bar(df, "ACF(returns^2) — volatility clustering signal", ci, lag_max)
  })
  
  output$lb_table <- renderDT({
    d <- data_obj()
    x <- as.numeric(d$ret)
    m <- input$lb_lag
    out <- rbind(
      cbind(series = "returns", lb_table(x, m)),
      cbind(series = "abs(returns)", lb_table(abs(x), m)),
      cbind(series = "returns^2", lb_table(x^2, m))
    )
    datatable(out, options = list(dom = "t"))
  })
  
  arma_fit <- eventReactive(input$fit_arma_btn, {
    d <- data_obj()
    x <- as.numeric(d$ret)
    withProgress(message = "Fitting ARMA...", value = 0.3, {
      fit <- if (isTRUE(input$arma_auto)) {
        auto.arima(x, seasonal = FALSE, stepwise = TRUE, approximation = FALSE)
      } else {
        Arima(x, order = c(input$arma_p, 0, input$arma_q), include.mean = TRUE)
      }
      incProgress(0.7)
      fit
    })
  })
  
  output$arma_summary <- renderPrint({
    req(arma_fit())
    print(arma_fit())
  })
  
  output$arma_diag_plot <- renderPlotly({
    req(arma_fit())
    fit <- arma_fit()
    r <- as.numeric(residuals(fit))
    
    n <- length(r)
    lag_max <- input$lag_max
    ci <- 1.96 / sqrt(n)
    
    r_df <- data.frame(t = seq_along(r), resid = r)
    p_resid <- plot_ly(r_df, x = ~t, y = ~resid, type = "scatter", mode = "lines") |>
      layout(title = "ARMA residuals", xaxis = list(title = "t"), yaxis = list(title = "residual"))
    
    p_acf_r <- acf_plotly_bar(acf_df(r, lag_max), "ACF(residuals)", ci, lag_max)
    p_acf_r2 <- acf_plotly_bar(acf_df(r^2, lag_max), "ACF(residuals^2) — ARCH effect indicator", ci, lag_max)
    
    subplot(p_resid, p_acf_r, p_acf_r2, nrows = 3, shareX = FALSE, titleY = TRUE)
  })
  
  output$arma_lb <- renderDT({
    req(arma_fit())
    r <- as.numeric(residuals(arma_fit()))
    m <- input$lb_lag
    out <- rbind(
      cbind(series = "residuals", lb_table(r, m)),
      cbind(series = "abs(residuals)", lb_table(abs(r), m)),
      cbind(series = "residuals^2", lb_table(r^2, m))
    )
    datatable(out, options = list(dom = "t"))
  })
  
  garch_fit <- eventReactive(input$fit_garch_btn, {
    d <- data_obj()
    x <- as.numeric(d$ret)
    validate(need(input$garch_p + input$garch_q > 0, "Choose p and/or q > 0 for GARCH order."))
    withProgress(message = "Fitting GARCH...", value = 0.2, {
      spec <- ugarchspec(
        variance.model = list(model = "sGARCH", garchOrder = c(input$garch_p, input$garch_q)),
        mean.model = list(armaOrder = c(0, 0), include.mean = TRUE),
        distribution.model = input$garch_dist
      )
      fit <- ugarchfit(spec, data = x, solver = "hybrid")
      incProgress(0.8)
      fit
    })
  })
  
  output$garch_summary <- renderPrint({
    req(garch_fit())
    show(garch_fit())
  })
  
  output$garch_diag_plot <- renderPlotly({
    req(garch_fit())
    fit <- garch_fit()
    
    sig <- as.numeric(sigma(fit))
    z <- as.numeric(residuals(fit, standardize = TRUE))
    
    n <- length(z)
    lag_max <- input$lag_max
    ci <- 1.96 / sqrt(n)
    
    sig_df <- data.frame(t = seq_along(sig), sigma = sig)
    p_sig <- plot_ly(sig_df, x = ~t, y = ~sigma, type = "scatter", mode = "lines") |>
      layout(title = "Conditional sigma(t)", xaxis = list(title = "t"), yaxis = list(title = "sigma"))
    
    z_df <- data.frame(t = seq_along(z), z = z)
    p_z <- plot_ly(z_df, x = ~t, y = ~z, type = "scatter", mode = "lines") |>
      layout(title = "Standardized residuals (Z-hat)", xaxis = list(title = "t"), yaxis = list(title = "Z"))
    
    p_acf_z <- acf_plotly_bar(acf_df(z, lag_max), "ACF(Z-hat)", ci, lag_max)
    p_acf_absz <- acf_plotly_bar(acf_df(abs(z), lag_max), "ACF(|Z-hat|)", ci, lag_max)
    
    subplot(p_sig, p_z, p_acf_z, p_acf_absz, nrows = 2, shareX = FALSE, titleY = TRUE)
  })
  
  risk_out <- eventReactive(input$forecast_btn, {
    req(garch_fit())
    fit <- garch_fit()
    h <- input$h
    alpha <- input$alpha
    
    fc <- ugarchforecast(fit, n.ahead = h)
    mu <- as.numeric(fitted(fc))
    sig <- as.numeric(sigma(fc))
    
    dist <- fit@model$modeldesc$distribution
    co <- coef(fit)
    
    if (dist == "norm") {
      qz <- qnorm(alpha); esz <- esz_norm(alpha)
    } else if (dist == "std") {
      df <- unname(co["shape"])
      qz <- qt(alpha, df = df); esz <- esz_std_t(alpha, df = df)
    } else {
      qz <- qnorm(alpha); esz <- esz_norm(alpha)
    }
    
    VaR <- mu + sig * qz
    ES  <- mu + sig * esz
    
    data.frame(h = seq_len(h), mu = mu, sigma = sig, VaR = VaR, ES = ES)
  })
  
  output$risk_table <- renderDT({
    req(risk_out())
    datatable(risk_out(), options = list(pageLength = 10))
  })
  
  output$risk_plot <- renderPlotly({
    req(risk_out())
    df <- risk_out()
    
    p_sigma <- plot_ly(df, x = ~h, y = ~sigma, type = "scatter", mode = "lines", name = "sigma") |>
      layout(title = "Forecasted volatility (sigma)", xaxis = list(title = "h"), yaxis = list(title = "sigma"))
    
    p_risk <- plot_ly(df, x = ~h, y = ~VaR, type = "scatter", mode = "lines", name = "VaR") |>
      add_lines(x = ~h, y = ~ES, name = "ES") |>
      layout(title = paste0("Forecasted VaR & ES (alpha=", input$alpha, ")"),
             xaxis = list(title = "h"), yaxis = list(title = "Return threshold"))
    
    subplot(p_sigma, p_risk, nrows = 2, shareX = TRUE, titleY = TRUE)
  })
  
  # -----------------------------
  # SIMULATE PAGE
  # -----------------------------
  sim_arma <- eventReactive(input$sim_arma_btn, {
    x <- simulate_arma_family(
      model = input$sim_arma_model,
      n = input$sim_arma_n,
      mu = input$sim_arma_mu,
      sigma = input$sim_arma_sigma,
      phi = input$sim_arma_phi,
      theta = input$sim_arma_theta,
      seed = input$sim_arma_seed
    )
    x
  }, ignoreInit = TRUE)
  
  output$sim_arma_checks <- renderPrint({
    req(sim_arma())
    x <- sim_arma()
    ci <- 1.96 / sqrt(length(x))
    cat("n =", length(x), "\n")
    cat("ACF band approx: ±", round(ci, 4), "\n")
    cat("mean =", round(mean(x), 5), "sd =", round(sd(x), 5), "\n")
    if (input$sim_arma_model %in% c("AR1", "ARMA11")) {
      cat("phi =", input$sim_arma_phi, " (AR stationarity for AR1: |phi|<1)\n")
    }
    if (input$sim_arma_model %in% c("MA1", "ARMA11")) {
      cat("theta =", input$sim_arma_theta, " (MA invertibility for MA1: |theta|<1)\n")
    }
  })
  
  output$sim_arma_lb <- renderDT({
    req(sim_arma())
    x <- sim_arma()
    out <- rbind(
      cbind(series = "x", lb_table(x, lag = min(20, input$sim_arma_lag))),
      cbind(series = "x^2", lb_table(x^2, lag = min(20, input$sim_arma_lag)))
    )
    datatable(out, options = list(dom = "t"))
  })
  
  output$sim_arma_ts <- renderPlotly({
    req(sim_arma())
    x <- sim_arma()
    df <- data.frame(t = seq_along(x), x = x)
    plot_ly(df, x = ~t, y = ~x, type = "scatter", mode = "lines") |>
      layout(title = paste0("Simulated series: ", input$sim_arma_model),
             xaxis = list(title = "t"), yaxis = list(title = "value"))
  })
  
  output$sim_arma_hist <- renderPlotly({
    req(sim_arma())
    x <- sim_arma()
    plot_ly(x = x, type = "histogram") |>
      layout(title = "Histogram", xaxis = list(title = "value"), yaxis = list(title = "count"))
  })
  
  output$sim_arma_acf <- renderPlotly({
    req(sim_arma())
    x <- sim_arma()
    lag_max <- input$sim_arma_lag
    ci <- 1.96 / sqrt(length(x))
    acf_plotly_bar(acf_df(x, lag_max), "ACF(x)", ci, lag_max)
  })
  
  output$sim_arma_pacf <- renderPlotly({
    req(sim_arma())
    x <- sim_arma()
    lag_max <- input$sim_arma_lag
    ci <- 1.96 / sqrt(length(x))
    acf_plotly_bar(pacf_df(x, lag_max), "PACF(x)", ci, lag_max)
  })
  
  sim_garch <- eventReactive(input$sim_garch_btn, {
    simulate_garch11(
      n = input$sim_garch_n,
      mu = input$sim_garch_mu,
      omega = input$sim_garch_omega,
      alpha1 = input$sim_garch_alpha,
      beta1 = input$sim_garch_beta,
      dist = input$sim_garch_dist,
      shape = input$sim_garch_df,
      seed = input$sim_garch_seed
    )
  }, ignoreInit = TRUE)
  
  output$sim_garch_checks <- renderPrint({
    req(sim_garch())
    s <- input$sim_garch_alpha + input$sim_garch_beta
    cat("alpha + beta =", round(s, 4), "\n")
    if (s < 1) cat("OK: alpha+beta<1 (typical stationarity condition)\n")
    if (s >= 1) cat("Warning: alpha+beta>=1 (nonstationary/IGARCH-like behavior)\n")
  })
  
  output$sim_garch_lb <- renderDT({
    req(sim_garch())
    x <- sim_garch()$x
    lag <- min(20, input$sim_garch_lag)
    out <- rbind(
      cbind(series = "x", lb_table(x, lag)),
      cbind(series = "x^2", lb_table(x^2, lag))
    )
    datatable(out, options = list(dom = "t"))
  })
  
  output$sim_garch_ts <- renderPlotly({
    req(sim_garch())
    x <- sim_garch()$x
    df <- data.frame(t = seq_along(x), x = x)
    plot_ly(df, x = ~t, y = ~x, type = "scatter", mode = "lines") |>
      layout(title = "Simulated GARCH returns", xaxis = list(title="t"), yaxis=list(title="x"))
  })
  
  output$sim_garch_sigma <- renderPlotly({
    req(sim_garch())
    sig <- sim_garch()$sigma
    df <- data.frame(t = seq_along(sig), sigma = sig)
    plot_ly(df, x = ~t, y = ~sigma, type = "scatter", mode = "lines") |>
      layout(title = "Simulated conditional sigma(t)", xaxis = list(title="t"), yaxis=list(title="sigma"))
  })
  
  output$sim_garch_acf <- renderPlotly({
    req(sim_garch())
    x <- sim_garch()$x
    lag_max <- input$sim_garch_lag
    ci <- 1.96 / sqrt(length(x))
    acf_plotly_bar(acf_df(x, lag_max), "ACF(x)", ci, lag_max)
  })
  
  output$sim_garch_acf2 <- renderPlotly({
    req(sim_garch())
    x <- sim_garch()$x
    lag_max <- input$sim_garch_lag
    ci <- 1.96 / sqrt(length(x))
    acf_plotly_bar(acf_df(x^2, lag_max), "ACF(x^2) — volatility clustering", ci, lag_max)
  })
  
  sim_var <- eventReactive(input$sim_var_btn, {
    Phi <- matrix(c(input$sim_phi11, input$sim_phi12,
                    input$sim_phi21, input$sim_phi22), 2, 2, byrow = TRUE)
    simulate_var1_2d(
      n = input$sim_var_n,
      Phi = Phi,
      sd_eps = input$sim_var_sd,
      rho_eps = input$sim_var_rho,
      seed = input$sim_var_seed
    )
  }, ignoreInit = TRUE)
  
  output$sim_var_eig <- renderPrint({
    req(sim_var())
    eig <- sim_var()$eig
    cat("Eigenvalues(Phi):\n")
    print(round(eig, 4))
    cat("max |eig| =", round(max(Mod(eig)), 4), "\n")
    cat("Stationary VAR(1) rule: max |eig| < 1\n")
  })
  
  output$sim_var_corr_heat <- renderPlotly({
    req(sim_var())
    X <- sim_var()$X
    C <- cor(X)
    labs <- c("X1", "X2")
    plot_ly(x = labs, y = labs, z = C, type = "heatmap",
            text = round(C, 3), hoverinfo = "text") |>
      layout(title = "Corr(X) at lag 0")
  })
  
  output$sim_var_ts <- renderPlotly({
    req(sim_var())
    X <- sim_var()$X
    df <- data.frame(t = seq_len(nrow(X)), X1 = X[,1], X2 = X[,2])
    p1 <- plot_ly(df, x = ~t, y = ~X1, type="scatter", mode="lines", name="X1")
    p2 <- plot_ly(df, x = ~t, y = ~X2, type="scatter", mode="lines", name="X2")
    subplot(p1, p2, nrows = 2, shareX = TRUE, titleY = TRUE) |>
      layout(title = "Simulated VAR(1) components")
  })
  
  output$sim_var_crosscorr <- renderPlotly({
    req(sim_var())
    X <- sim_var()$X
    lag_max <- input$sim_var_lag
    df <- crosscorr_df(X[,1], X[,2], lag_max = lag_max)
    plot_ly(df, x = ~lag, y = ~value, type = "bar") |>
      layout(title = "Cross-correlation: corr(X1[t+h], X2[t]) (positive h = X1 leads X2)",
             xaxis = list(title = "lag h"), yaxis = list(title="corr"), bargap = 0.2)
  })
  
  sim_dcc <- eventReactive(input$sim_dcc_btn, {
    validate(need(input$sim_dcc_alpha + input$sim_dcc_beta < 1, "Need alpha + beta < 1."))
    simulate_dcc11_2d(
      n = input$sim_dcc_n,
      alpha = input$sim_dcc_alpha,
      beta = input$sim_dcc_beta,
      rho_longrun = input$sim_dcc_rho,
      seed = input$sim_dcc_seed
    )
  }, ignoreInit = TRUE)
  
  output$sim_dcc_check <- renderPrint({
    cat("alpha + beta =", round(input$sim_dcc_alpha + input$sim_dcc_beta, 4), "\n")
    cat("Constraint: alpha+beta < 1\n")
  })
  
  output$sim_dcc_rho_path <- renderPlotly({
    req(sim_dcc())
    rho_t <- sim_dcc()$rho_t
    df <- data.frame(t = seq_along(rho_t), rho = rho_t)
    plot_ly(df, x = ~t, y = ~rho, type="scatter", mode="lines") |>
      layout(title="Dynamic correlation path ρ_t", xaxis=list(title="t"), yaxis=list(title="ρ_t"))
  })
  
  output$sim_dcc_y <- renderPlotly({
    req(sim_dcc())
    y <- sim_dcc()$y
    df <- data.frame(t = seq_len(nrow(y)), Y1 = y[,1], Y2 = y[,2])
    p1 <- plot_ly(df, x = ~t, y = ~Y1, type="scatter", mode="lines", name="Y1")
    p2 <- plot_ly(df, x = ~t, y = ~Y2, type="scatter", mode="lines", name="Y2")
    subplot(p1, p2, nrows = 2, shareX = TRUE, titleY = TRUE) |>
      layout(title = "Simulated devolatilized shocks (Y)")
  })
  
}

shinyApp(ui, server)
