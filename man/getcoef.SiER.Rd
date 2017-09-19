\name{getcoef.SiER}
\alias{getcoef.SiER}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{Get the estimated intercept and coefficient.
}
\description{Get the estimates for \eqn{\mu, \beta}{\mu, \beta} based on the object obtained from \code{\link{cv.SiER}}().
}
\usage{
getcoef.SiER(cv.fit)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{cv.fit}{the object obtained from \code{\link{cv.SiER}}().}
%  \item{...}{other arguments, not used.}
%%     ~~Describe \code{CV.fit} here~~
}
\value{a list containing
\item{mu }{the vector of estimated \eqn{\mu}.}
\item{beta }{the estimated matrix for \eqn{\beta}.}
\item{nonzero.ind }{the vector of indices for selected variables.}
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
\examples{#See the examples in cv.Sier().
}
