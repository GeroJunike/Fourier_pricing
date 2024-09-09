
#This code implements the COS method, the Carr-Madan formula and the Lewis formula to numerically approximate the price, Delta and Gamma of a European Call option in the Variance-Gamma model.
#The code complements the paper Behrens, T., Junike, W. and Schoutens (2024).
#Authors: Tobias Behrens, Gero Junike (gero.junike at uol.de, ORCID: 0000-0001-8686-2661).

#The COS method was first introduced by  Fang and Oosterlee (2009). The implementation is based on Appendix A in Junike and Pankrashkin (2022); and by Theorem 5.2 in Junike (2024). 
#The Carr-Madan formula was first introduced by Carr and Madan (1999). The implementation is based on pp. 54-59 in Madan and Schoutens (2016).
#The implementation of the Lewis formula is based on Theorem 3.2, Section 4 and Example 5.2 in Eberlein, Glau, and Papapantoleon (2010). The integral for the Lewis formula is solved numerically by Gauss-Laguerre quadrature.

#References:
#Behrens, T., Junike and Schoutens W. (2024) "Failure of Fourier pricing techniques to approximate the Greeks", https://arxiv.org/pdf/2306.08421
#Carr, P. and Madan D. (1999). “Option valuation using the fast Fourier transform”. In: Journal of computational finance 2.4, pp. 61–73. 
#Eberlein, E., Glau K., and Papapantoleon, A. (2010). “Analysis of Fourier transform valuation formulas and applications”. In: Applied Mathematical Finance 17.3, pp. 211–240.
#Fang, F. and Oosterlee, C. W. (2009) "A novel pricing method for European options based on Fourier-cosine series expansions", SIAM J. Sci. Comp. 31 826–848. 
#Junike, G. and Pankrashkin, K. (2022). “Precise option pricing by the COS method–How to choose the truncation range”. In: Applied Mathematics and Computation 421, p. 126935.
#Junike, G. (2024). “On the number of terms in the COS method for European option pricing”. In: Numerische Mathematik 156.2, pp. 533–564.
#Madan, D. and Schoutens W. (2016). "Applied conic finance". Cambridge University Press.

##############################
#### Variance Gamma model ####
##############################

# Input: Fourier transform variable u, asset-price today S0, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Characteristic function of log(ST).
psiLogST <- function(u, S0, mat, r, p) {
  sigma <- p[1]; nu <- p[2]; theta <- p[3]
  m <- (1 / nu) * log(1 - theta * nu - 0.5 * sigma ^ 2 * nu)
  exp(1i * u * (log(S0) + (r + m) * mat)) * (1 / (1 - 1i * u * theta * nu + sigma ^ 2 * nu * u ^ 2 * 0.5)) ^ (mat / nu)
}

# Input: Fourier transform variable u, maturity mat, risk-free rate r, vector of VG parameter p = (sigma, nu, theta). 
# Output: Characteristic function of log(ST_hat) that does not depend on S0, i.e., ST = S_0 * ST_hat.
psiLogST_hat <- function(u, mat, r, p) { psiLogST(u, 1, mat, r, p) }

# Input: Asset-price today S0, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta). 
# Output: Expectation of log(ST).
ElogST <- function(S0, mat, r, p) {
  sigma <- p[1]; nu <- p[2]; theta <- p[3]
  m <- (1 / nu) * log(1 - theta * nu - 0.5 * sigma ^ 2 * nu)
  log(S0) + (r + m + theta) * mat 
}

# Input: Fourier transform variable u, maturity mat, vector of VG parameter p = c(sigma, nu, theta). 
# Output: Characteristic function of log(ST) - E[log(S_T)]
psiX <- function(u, mat, p) {
  sigma <- p[1]; nu <- p[2]; theta <- p[3]
  (1 / (1 - 1i * u * theta * nu + sigma ^ 2 * nu * u ^ 2 * 0.5)) ^ (mat / nu) * exp(-1i * u * theta * mat)
}

####################
#### COS method ####
####################

# Input: Number of terms N, truncation range for the density L, asset-price today S0, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Fourier coefficient of the centralized density.
ck <- function(N, L, S0, mat, r, p) {
  res <- 1 / L * Re(psiX((0:N) * pi / (2 * L), mat, p) * exp(1i * (0:N) * pi / 2))
  res[1] <- 0.5 * res[1]
  res
}

# Input: Number of terms N, truncation range for the density L,  asset-price today S0, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Fourier coefficients of the first derivative of the centralized density.
ck1 <- function(N, L, S0, mat, r, p) {
  res <- 1 / L * Re(-1i * ((0:N) * pi / (2 * L)) * psiX((0:N) * pi / (2 * L), mat, p) * exp(1i * (0:N) * pi / 2))
  res[1] <- 0.5 * res[1]
  res
}

# Input: Number of terms N, truncation range for the density L,  asset-price today S0, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Fourier coefficients of the second derivative of the centralized density.
ck2 <- function(N, L, S0, mat, r, p) {
  res <- 1 / L * Re((-1i * (0:N) * pi / (2 * L)) ^ 2 * psiX((0:N) * pi / (2 * L), mat, p) * exp(1i * (0:N) * pi / 2))
  res[1] <- 0.5 * res[1]
  res
}

# Input: Number of terms N, truncation range for the density L, truncation range for the payoff M (usually equal to L),  asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# output: Cosine coefficients of a put option.
vk_put <- function(N, L, M, S0, K, mat, r, p) {
  d <- min(log(K) - ElogST(S0, mat, r, p), M) 
  psi0 <- 2 * L / ((0:N) * pi) * (sin((0:N) * pi * (d + L) / (2 * L)) - sin((0:N) * pi * (-M + L) / (2 * L)))
  psi0[1] <- d + M
  psi1 <- 1 / (1 + ((0:N) * pi / (2 * L)) ^ 2) * (exp(d) * ((0:N) * pi / (2 * L) * sin((0:N) * pi * (d + L) / (2 * L)) + cos((0:N) * pi *(d + L) / (2 * L)))
                                                  - exp(-M) * ((0:N) * pi / (2 * L) * sin((0:N) * pi * (-M + L) / (2 * L)) + cos((0:N) * pi * (-M + L) / (2 * L))))
  
  exp(-r * mat) * K * psi0 - exp(-r * mat) * exp(ElogST(S0, mat, r, p)) * psi1
}

# Input: Number of terms N, truncation range for the density L, truncation range for the payoff M (usually equal to L),  asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Price of a put option by the COS method.
cos_put <- function(N, L, M, S0, K, mat, r, p) {
  sum(ck(N, L, S0, mat, r, p) * vk_put(N, L, M, S0, K, mat, r, p))
}

# Input: Number of terms N, truncation range for the density L, truncation range for the payoff M (usually equal to L),  asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Delta of a put option by the COS method.
cos_put_delta <- function(N, L, M, S0, K, mat, r, p) {
  sum(-1 / S0 * ck1(N, L, S0, mat, r, p) * vk_put(N, L, M, S0, K, mat, r, p))
}

# Input: Number of terms N, truncation range for the density L, truncation range for the payoff M (usually equal to L),  asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Gamma of a put option by the COS method.
cos_put_gamma <- function(N, L, M, S0, K, mat, r, p) {
  sum(1 / S0 ^ 2 * (ck1(N, L, S0, mat, r, p) + ck2(N, L, S0, mat, r, p)) * vk_put(N, L, M, S0, K, mat, r, p))
}

# Input: Number of terms N, truncation range for the density L, truncation range for the payoff M (usually equal to L),  asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Price of a call option by the COS method.
cos_call <- function(N, L, M, S0, K, mat, r, p) {
  cos_put(N, L, M, S0, K, mat, r, p) + S0 - K * exp(-r * mat)
}

# Input: Number of terms N, truncation range for the density L, truncation range for the payoff M (usually equal to L),  asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Delta of a call option by the COS method.
cos_call_delta <- function(N, L, M, S0, K, mat, r, p) {
  1 + cos_put_delta(N, L, M, S0, K, mat, r, p)
}

# Gamma is equal for call and put option.
cos_call_gamma <- cos_put_gamma

############################
#### Carr-Madan Formula ####
############################

# Input: Number of grid points N, damping factor cm_alpha, Fourier truncation range cm_trunc, asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: price of a call option by Carr-Madan.
cm_call <- function(cm_N, cm_alpha = 0.1, cm_trunc, S0, K, mat, r, p) {
  cm_eta <- cm_trunc / (cm_N-1)
  vj <- cm_eta * (0:(cm_N - 1))
  simpson <- 1 + 1 / 3 * (-1) ^ (1:cm_N)
  simpson[1] <- 1 / 3
  h <- exp(-1i * vj * log(K)) * psiLogST_hat(vj - 1i * (cm_alpha + 1), mat, r, p) * exp((cm_alpha + 1 + 1i * vj) * log(S0)) / (cm_alpha ^ 2 + cm_alpha - vj ^ 2 + 1i * (2 * cm_alpha + 1) * vj)
  sumval <- Re(sum(h * cm_eta * simpson))
  exp(-cm_alpha * log(K)) / pi * exp(-r * mat) * sumval
}

# Input: Number of grid points N, damping factor cm_alpha, Fourier truncation range cm_trunc, asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Delta of a call option by Carr-Madan.
cm_call_delta <- function(cm_N, cm_alpha = 0.1, cm_trunc, S0, K, mat, r, p) {
  cm_eta <- cm_trunc / (cm_N - 1)
  vj <- cm_eta * (0:(cm_N - 1))
  simpson <- 1 + 1 / 3 * (-1) ^ (1:cm_N)
  simpson[1] <- 1 / 3
  h <- exp(-1i * vj * log(K)) * psiLogST_hat(vj - 1i * (cm_alpha + 1), mat, r, p) * exp((cm_alpha + 1 + 1i * vj) * log(S0)) / (S0 * (cm_alpha + 1i * vj))
  sumval <- Re(sum(h * cm_eta * simpson))
  exp(-cm_alpha * log(K)) / pi * exp(-r * mat) * sumval
}

# Input: Number of grid points N, damping factor cm_alpha, Fourier truncation range cm_trunc, asset-price today S0, strike K, maturity mat, risk-free rate r, vector of VG parameter p = c(sigma, nu, theta).
# Output: Gamma of call option by Carr-Madan.
cm_call_gamma <- function(cm_N, cm_alpha = 0.1, cm_trunc, S0, K, mat, r, p) {
  cm_eta <- cm_trunc / (cm_N - 1)
  vj <- cm_eta * (0:(cm_N - 1))
  simpson <- 1 + 1 / 3 * (-1) ^ (1:cm_N)
  simpson[1] <- 1 / 3
  h <- exp(-1i * vj * log(K)) * psiLogST_hat(vj - 1i * (cm_alpha + 1), mat, r, p) * exp((cm_alpha + 1 + 1i * vj) * log(S0)) / S0 ^ 2
  sumval <- Re(sum(h * cm_eta * simpson))
  exp(-cm_alpha * log(K)) / pi * exp(-r * mat) * sumval
} 

########################
#### Lewis Formula #####
########################

# Package is needed for the functions: lewis_price, lewis_delta, lewis_gamma. 
library(pracma)

# Input: Strike K, imaginary number z.
# Output: Fourier transform of a call option. 
w_hat_call <- function(K, z) { K ^ (1 + 1i * z) / ((1i * z) * (1 + 1i * z)) } 

# Gauss–Laguerre coefficients: Number of terms to apply Gauss-Laguerre quadrature is here 1000.
gLcoeff <- gaussLaguerre(1000, 0)

# Input: Maturity mat, strike K, asset-price today S0, risk-free rate r, characteristic function that does not depend on S0 FUN, Fourier transform the payoff Fourier_Payoff, vector of VG parameter p = c(sigma, nu, theta), damping factor lewis_alpha, list of Gauss-Laguerre coefficients gLcoeff.
# Output: price of a call option by Lewis.
lewis_price <- function(mat, K, S0, r, FUN, Fourier_payoff, p, lewis_alpha = 1.1, gLcoeff) {
  g <- function(v, lewis_alpha, FUN, Fourier_payoff) {
    Re(S0 ^ (lewis_alpha - 1i * v) * FUN(-v - 1i * lewis_alpha, mat, r, p) * Fourier_payoff(K, v + 1i * lewis_alpha))
  }
  gval <- g(gLcoeff$x, lewis_alpha, FUN, Fourier_payoff) * exp(gLcoeff$x)
  1 / pi * exp(-r * mat) * Re(sum(gLcoeff$w * gval, na.rm = TRUE))
}

# Input: Maturity mat, strike K, asset-price today S0, risk-free rate r, characteristic function that does not depend on S0 FUN, Fourier transform the payoff Fourier_Payoff, vector of VG parameter p = c(sigma, nu, theta), damping factor lewis_alpha, list of Gauss-Laguerre coefficients gLcoeff.
# Output: Delta of a call option by Lewis.
lewis_delta <- function(mat, K, S0, r, FUN, Fourier_payoff, p, lewis_alpha = 1.1, gLcoeff) {
  g <- function(v, lewis_alpha, FUN, Fourier_payoff) {
    Re(S0 ^ (lewis_alpha - 1 - 1i * v) * (lewis_alpha - 1i * v) * FUN(-v - 1i * lewis_alpha, mat, r, p) * Fourier_payoff(K, v + 1i * lewis_alpha))
  }
  gval <- g(gLcoeff$x, lewis_alpha, FUN, Fourier_payoff) * exp(gLcoeff$x)
  1 / pi * exp(-r * mat) * Re(sum(gLcoeff$w * gval, na.rm = TRUE))
}

# Input: Maturity mat, strike K, asset-price today S0, risk-free rate r, characteristic function that does not depend on S0 FUN, Fourier transform the payoff Fourier_Payoff, vector of VG parameter p = c(sigma, nu, theta), damping factor lewis_alpha, list of Gauss-Laguerre coefficients gLcoeff. 
# Output: Gamma of a call option by Lewis.
lewis_gamma <- function(mat, K, S0, r, FUN, Fourier_payoff, p, lewis_alpha = 1.1, gLcoeff) {
  g <- function(v, lewis_alpha, FUN, Fourier_payoff) {
    Re(S0 ^ (lewis_alpha - 2 - 1i * v) * (lewis_alpha - 1i * v) * (lewis_alpha - 1 - 1i * v) * FUN(-v - 1i * lewis_alpha, mat, r, p) * Fourier_payoff(K, v + 1i * lewis_alpha))
  }
  gval <- g(gLcoeff$x, lewis_alpha, FUN, Fourier_payoff) * exp(gLcoeff$x)
  1 / pi * exp(-r * mat) * Re(sum(gLcoeff$w * gval, na.rm = TRUE))
}

##################
#### Examples ####
##################

# Price of a call option: Should be equal to 0.0295437
cos_call(N = 10 ^ 5, L = 30, M = 30, S0 = 0.75, K = 0.75, mat = 1, r = 0, p = c(0.1, 0.1, 0))
cm_call(cm_N = 2 ^ 17, cm_alpha = 0.5, cm_trunc = 4800, S0 = 0.75, K = 0.75, mat = 1, r = 0, p = c(0.1, 0.1, 0))
lewis_price(mat = 1, K = 0.75, S0 = 0.75, r = 0, FUN = psiLogST_hat, Fourier_payoff = w_hat_call, p = c(0.1, 0.1, 0), lewis_alpha = 1.1, gLcoeff)

# Delta of a call option: Should be equal to 0.5186603
cos_call_delta(N = 10 ^ 5, L = 30, M = 30, S0 = 0.75, K = 0.75, mat = 1, r = 0, p = c(0.1, 0.1, 0))
cm_call_delta(cm_N = 2 ^ 17, cm_alpha = 0.5, cm_trunc = 4800, S0 = 0.75, K = 0.75, mat = 1, r = 0, p = c(0.1, 0.1, 0))
lewis_delta(mat = 1, K = 0.75, S0 = 0.75, r = 0, FUN = psiLogST_hat, Fourier_payoff = w_hat_call, p = c(0.1, 0.1, 0), lewis_alpha = 1.1, gLcoeff)

# Gamma of a call option: Should be equal to 5.521535
cos_call_gamma(N = 10 ^ 5, L = 30, M = 30, S0 = 0.75, K = 0.75, mat = 1, r = 0, p = c(0.1, 0.1, 0))
cm_call_gamma(cm_N = 2 ^ 17, cm_alpha = 0.5, cm_trunc = 4800, S0 = 0.75, K = 0.75, mat = 1, r = 0, p = c(0.1, 0.1, 0))
lewis_gamma(mat = 1, K = 0.75, S0 = 0.75, r = 0, FUN = psiLogST_hat, Fourier_payoff = w_hat_call, p = c(0.1, 0.1, 0), lewis_alpha = 1.1, gLcoeff)
