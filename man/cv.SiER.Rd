\name{cv.SiER}
\alias{cv.SiER}
\title{Cross-validation for high-dimensional multivariate regression
  %%  ~~function to do ... ~~
}
\description{
  Conduct the cross-validation and build the final
  model for the following high dimensional multivariate regression model:
  \deqn{Y= \mu+X\beta+\epsilon,}{Y= \mu+X\beta+\epsilon,}
  where \eqn{Y}{Y} is the \eqn{n\times q}{n*q} response matrix with \eqn{q\ge  1},
\eqn{X}{X} is the \eqn{n\times p}{n*p} predictor matrix, and
\eqn{\epsilon}{\epsilon} is the noise matrix.  The coefficient matrix
\eqn{\beta}{\beta} is \eqn{p\times q}{p*q} and  \eqn{\mu}{\mu} is the
intercept.  The number of predictors \eqn{p} can be much larger than the
sample size \eqn{n}. The response is univariate if
\eqn{q=1} and  multivariate if \eqn{q>1}.
}
\usage{
cv.SiER(X, Y, K.cv = 5, upper.comp = 10, thresh = 0.01)
}
\arguments{
  \item{X}{the \eqn{n\times p}{n*p} predictor matrix.
%%     ~~Describe \code{X} here~~
}
  \item{Y}{the \eqn{n\times q}{n*q} response matrix, where \eqn{q\ge 1} is
    the number of response variables.
%%     ~~Describe \code{Y} here~~
}
  \item{K.cv}{ the number of CV sets. Default is 5.
%%     ~~Describe \code{K.cv} here~~
}
  \item{upper.comp}{the upper bound for the maximum number of components to be calculated. Default is 10.
%%     ~~Describe \code{upper.comp} here~~
}
  \item{thresh}{a number between 0 and 1 specifying the minimum proportion of variation to be explained by each selected component relative to all the selected components. It is used to determine the maximum number of components to be calculated in the CV procedure. The optimal number of components will be selected from the integers from 1 to the minimum of upper.comp and this maximum number. A smaller thresh leads to a larger maximum number of components and a longer running time. A larger thresh value leads to a smaller running time, but may miss some important components and lead to a larger prediction error. Default is 0.01.
}
}
\details{
  Based on the best rank \eqn{K} approximation to \eqn{X\beta}, the  coefficient matrix has decomposition  \eqn{\beta=\sum \alpha_k w_k    ^T}{\alpha_1 w_1 ^T+\alpha_2 w_2 ^T+...}, where \eqn{\alpha_k} is  the vector so that \eqn{X\alpha_k} has the maximum correlation with  \eqn{Y} under the restriction that  \eqn{X\alpha_k} has unit variance and is uncorrelated  with   \eqn{X\alpha_1},..., \eqn{X\alpha_{k-1}}. We estimate  \eqn{\alpha_k} by solving a penalized generalized eigenvalue problem  with penalty \eqn{\tau||\alpha_k||_{\lambda}^2} where  \eqn{||\alpha_k||_{\lambda}^2=(1-\lambda)||\alpha_k||_2^2+\lambda||\alpha_k||_1^2}  is a mixture of the squared \eqn{l_2} and squared \eqn{l_1} norms. The \eqn{w_k} is  estimated by regressing \eqn{Y} on \eqn{X\alpha_k}.
}
\value{A fitted CV-object, which is used in the function \code{\link{pred.SiER}}() for prediction and \code{\link{getcoef.SiER}}() for extracting the estimated coefficient matrix.
\item{mu}{the estimated intercept vector.}
\item{beta}{the estimated slope coefficient matrix.}
\item{min.error}{minimum CV error.}
\item{scale.x}{the maximum absolute value of X used to scale X.}
\item{X}{the input X.}
\item{Y}{the input Y.}
\item{params.set}{a 9*2 matrix specifying the set of values of \eqn{tau} and \eqn{lambda} used in CV.}
\item{error}{a list for CV errors.}
\item{opt.K}{optimal number of components to be selected.}
\item{opt.tau}{optimal value for \eqn{tau}.}
\item{opt.lambda}{optimal value for \eqn{lambda}.}
%\item{is.univariate}{logic value specifying whether Y is univariate.}
}
\references{Ruiyan Luo and Xin Qi (2017) Signal extraction approach for
  sparse multivariate response regression, Journal of Multivariate
  Statistics. 153: 83-97.
}
\author{Ruiyan Luo and Xin Qi
%%  ~~who you are~~
}
\examples{
# q=1
library(MASS)
nvar=100
nvarq <- 1
sigmaY <- 0.1
sigmaX=0.1
nvar.eff=15
rho <- 0.3
Sigma=matrix(0,nvar.eff,nvar.eff)
for(i in 1:nvar.eff){
    for(j in 1:nvar.eff){
        Sigma[i,j]=rho^(abs(i-j))
    }
}

betas.true <- matrix(0, nvar, 1)
betas.true[1:15,1]=rep(1,15)/sqrt(15)

ntest <- 100
ntrain <- 90
ntot <- ntest+ntrain
X <- matrix(0,ntot,nvar)
X[,1:nvar.eff] <- mvrnorm(n=ntot, rep(0, nvar.eff), Sigma)
X[,-(1:nvar.eff)] <- matrix(sigmaX*rnorm((nvar-nvar.eff)*dim(X)[1]),
                            dim(X)[1],(nvar-nvar.eff))
Y <- X\%*\%betas.true
Y <- Y+rnorm(ntot, 0, sigmaY)

X.train <- X[1:ntrain,]
Y.train <- Y[1:ntrain,]
X.test <- X[-(1:ntrain),]
Y.test <- Y[-(1:ntrain),]

cv.fit <- cv.SiER(X.train,Y.train, K.cv=5)

Y.pred=pred.SiER(cv.fit, X.test)
error=sum((Y.pred-Y.test)^2)/ntest
print(c("predict error=", error))
coefs=getcoef.SiER(cv.fit)

\donttest{
#q>1
library(MASS)
total.noise <- 0.1
rho <- 0.3
rho.e <- 0.2
nvar=500
nvarq <- 3
sigma2 <- total.noise/nvarq
sigmaX=0.1
nvar.eff=150

Sigma=matrix(0,nvar.eff,nvar.eff)
for(i in 1:nvar.eff){
    for(j in 1:nvar.eff){
        Sigma[i,j]=rho^(abs(i-j))
    }
}
Sigma2.y <- matrix(sigma2*rho.e,nvarq, nvarq)
diag(Sigma2.y) <- sigma2

betas.true <- matrix(0, nvar, 3)
betas.true[1:15,1]=rep(1,15)/sqrt(15)
betas.true[16:45,2]=rep(0.5,30)/sqrt(30)
betas.true[46:105,3]=rep(0.25,60)/sqrt(60)

ntest <- 500
ntrain <- 90
ntot <- ntest+ntrain
X <- matrix(0,ntot,nvar)
X[,1:nvar.eff] <- mvrnorm(n=ntot, rep(0, nvar.eff), Sigma)
X[,-(1:nvar.eff)] <- matrix(sigmaX*rnorm((nvar-nvar.eff)*dim(X)[1]),
                           dim(X)[1],(nvar-nvar.eff))
Y <- X\%*\%betas.true
Y <- Y+mvrnorm(n=ntot, rep(0,nvarq), Sigma2.y)

X.train <- X[1:ntrain,]
Y.train <- Y[1:ntrain,]
X.test <- X[-(1:ntrain),]
Y.test <- Y[-(1:ntrain),]

cv.fit <- cv.SiER(X.train,Y.train, K.cv=5)

Y.pred=pred.SiER(cv.fit, X.test)
error=sum((Y.pred-Y.test)^2)/ntest
print(c("predict error=", error))
}
}