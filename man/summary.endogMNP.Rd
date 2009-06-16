\name{summary.endogMNP}

\alias{summary.endogMNP}
\alias{print.summary.endogMNP}

\title{Summarizing the results for the Multinomial Probit Models with Endogeneity}

\description{
  \code{summary} method for class \code{endogMNP}.
}

\usage{
  \method{summary}{endogMNP}(object, CI=c(2.5, 97.5), discard=1, ...)

  \method{print}{summary.endogMNP}(x, digits = max(3, getOption("digits") - 3), ...)
}

\arguments{
  \item{object}{An output object from \code{endogMNP}.}
  \item{CI}{A 2 dimensional vector of lower and upper bounds for the
    credible intervals used to summarize the results. The default is the
    equal tail 95 percent credible interval.}
\item{discard}{Discard the observations before \code{discard} as burn-in.}
  \item{x}{An object of class \code{summary.endogMNP}.}
  \item{digits}{the number of significant digits to use when printing.}
  \item{...}{further arguments passed to or from other methods.}
}

\value{
  \code{summary.endogMNP} yields an object of class \code{summary.endogMNP}
  containing the following elements:
  \item{call}{The call from \code{endogMNP}.}
\item{selBase}{The base category for the selection model.}
\item{outBase}{The base category for the outcome model.}
  \item{n.obs}{The number of observations.}
  \item{n.param}{The number of estimated parameters (including fixed 
	elements of the covariance).}
  \item{n.draws}{The number of Gibbs draws stored.}
  \item{coef.table}{The summary of the posterior distribution of the
    coefficients. }
  \item{cov.table}{The summary of the posterior distribution of the
    covariance matrix.}
  This object can be printed by \code{print.summary.enodgMNP}
}

\seealso{\code{endogMNP}}

\author{
  Lane Burgette, Department of Statistics, University of Wisconsin,
  \email{burgette@stat.wisc.edu}
}

\keyword{methods}
