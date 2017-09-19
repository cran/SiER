\name{pred.SiER}
\alias{pred.SiER}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{Prediction for high-dimensional multivariate regression
%%  ~~function to do ... ~~
}
\description{Make prediction for the univariate or multivariate response based on new observations of predictors from the CV object obtained by \code{\link{cv.SiER}}.
}
\usage{
pred.SiER(cv.fit, X.new)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{cv.fit}{the CV object obtained by \code{\link{cv.SiER}}().
%%     ~~Describe \code{CV.fit} here~~
}
  \item{X.new}{a new data matrix for predictors. The number of columns equals to the number of variables.
}
}
%\details{
%%  ~~ If necessary, more details than the description above ~~
%}
\value{A matrix containing the predicted response for new observations. The number of rows is equal to the number of observations in the new data set, and the number of columns is equal to the number of the responses.
}
%\references{
%% ~put references to the literature/web site here ~
%}
\author{Ruiyan Luo and Xin Qi
%%  ~~who you are~~
}
%\note{
%%  ~~further notes~~
%}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{\code{\link{cv.SiER}}
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{#See the examples in cv.SiER().}
