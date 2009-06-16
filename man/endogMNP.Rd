\name{endogMNP}

\alias{endogMNP}
\alias{endogMNP}

\title{Fitting the Multinomial Probit Model with Endogenous Selection via Markov chain Monte Carlo} 

\description{
  \code{endogMNP} is used to fit a Bayesian multinomial probit
  model with endogenous selection 
	via Markov chain Monte Carlo.  The computation
  uses the efficient partial marginal data augmentation algorithm that is
  developed by Burgette and Nordheim (2009), which is an extension of the
	sampler of Imai and van Dyk (2005).
}

\usage{
endogMNP(selForm, outForm, dataSet = parent.frame(),
                selBase = NULL, outBase = NULL, latent=FALSE, 
                invcdf = FALSE, n.draws = 5000, p.var = "Inf",
                p.df = n.dim+1, p.scale = 1, coef.start = 0,
                cov.start = 1, burnin = 0, thin = 0, verbose = FALSE,
		minConst=TRUE)}


\arguments{
  \item{selForm}{A symbolic description of the selection model portion of 	the model where the left-hand side indicates the category into 
	which each observation has been selected.}
  \item{outForm}{A symbolic description of the outcome equation.  The 
	left-hand side is the response of interest.} 

  \item{dataSet}{An optional data frame in which to interpret the variables
    in \code{selForm} and \code{outForm}. The default is the environment
    in which \code{endogMNP} is called.
  }
  \item{selBase}{The name of the base category for the selection equation. 	The default is the lowest level of the
    selection variable. 
  }
  \item{outBase}{The name of the base category for the outcome equation. 	The default is the lowest level of the
    response variable. 
  }

\item{latent}{Logical. Store latent vectors?}
  \item{invcdf}{Logical. If \code{TRUE}, then the inverse cdf method is
    used for truncated normal sampling. If \code{FALSE}, then the
    rejection sampling method is used. The default is \code{FALSE}.
  }
  \item{n.draws}{A positive integer. The number of MCMC draws. The
    default is \code{5000}.
  }
  \item{p.var}{A positive definite matrix. The prior variance of the
    coefficients.  A scalar input can set the prior variance to the
    diagonal matrix whose diagonal element is equal to that value. The
    default is \code{"Inf"}, which represents an improper noninformative
    prior distribution on the coefficients.
  }
  \item{p.df}{A positive integer greater than the dimension of the 
	implied covariance matrix. The prior
  degrees of freedom parameter for the covariance matrix. The default is
    the dimension of the covariance matrix plus one.
  }
  \item{p.scale}{A block-diagonal, positive definite matrix whose leading  	diagonal elements
    are set to \code{1}. The first block has the size of the selection
	covariance matrix, and the other blocks are of the size of the
	outcome
	covariance matrices.  This is the prior scale matrix for the
	covariance
    matrix. A scalar input can be used to set the
    scale matrix to a diagonal matrix with diagonal elements equal to
    the scalar input value, except that the first element in each block is
    set to one. The default is \code{1}. 
  }
  \item{coef.start}{A vector. The starting values for the coefficients.
    A scalar input sets the starting values for all the coefficients
    equal to that value.  The default is \code{0}.
  }
  \item{cov.start}{A positive definite matrix.  The first elements in the
	blocks determined by the selection and outcome sizes should be set
	to \code{1}. This is the starting value for the covariance
    matrix. The leading diagonal elements are set to 1 if they are not
    already. A scalar input can be used to set the starting
    value to a diagonal matrix with diagonal elements equal to the scalar
    input value, except those of the leading diagonal elements are set to
    one. The default is \code{1}. 
  }
  \item{burnin}{A positive integer. The burn-in interval for the Markov
    chain.  It is the number of initial Gibbs draws that should not be
    stored. The default is \code{0}. 
  }
  \item{thin}{A positive integer. The thinning interval for the Markov
    chain. This is the number of Gibbs draws between the recorded values
    that are skipped. The default is \code{0}. 
  }
  \item{verbose}{Logical. If \code{TRUE}, messages along with
    a progress report of the Gibbs sampling are printed.
    The default is \code{FALSE}.
  }
\item{minConst}{Logical. If \code{TRUE}, the covariance matrix is 
	minimally constrained, which is to say only enough of the 
	elements of the covariance matrix are constrained to be 1
	in order to make the model identifiable.  If \code{FALSE},
	all of the diagonal elements of the covariance matrix are
	constrained to be 1.  This can improve convergence in some cases.}
}

\details{
  To fit the multinomial probit model when only the most
  preferred choice is observed, use the syntax for the formula, 		\code{outForm = y ~ x1 + x2}, where \code{y} is a factor variable 	indicating the most
  preferred choice and \code{x1} and \code{x2} are individual-specific
  covariates. The selection process is modeled by 
	\code{selForm = y2 ~ x3 + x4} where \code{y2} contains 
	the selection category.
}
  




\value{
  An object of class \code{endogMNP} containing the following elements:
  \item{call}{The matched call.}
  \item{param}{A matrix of the Gibbs draws for each parameter; i.e., the
    coefficients and covariance matrix. For the covariance matrix, the
    elements on or above the diagonal are returned.
  }
  \item{x}{The matrix of covariates.}
  \item{y}{The vector matrix of the selection and response variables.}
\item{n.dim}{The number of columns in the covariance matrix.}
\item{n.obs}{The number of observations.}
\item{coefnames}{The names of the coefficients.}
  \item{W}{The three dimensional array of the latent variable, W. The
    first dimension represents the alternatives, and the second
    dimension indexes the observations. The third dimension represents
    the Gibbs draws. Note that the latent variables for the base categories 
    are set to 0, and therefore omitted from the output.}
\item{p.scale}{The prior scale of the covariance.}
\item{n.cov}{The number of covariates.}
\item{nu0}{The prior degrees of freedom.}
\item{p.var}{The prior variance.}
\item{n.param}{The number of parameters in the fit model.}
\item{minConst}{Indicator of whether the covariance matrix was minimally
	constrained.}
\item{n.dim1}{The number of dimensions for the selection equation.}
\item{n.dim2}{The number of dimensions of each outcome equation.}
\item{n.rep}{The number of stored Gibbs iterations.}
\item{selForm}{The symbolic selection equation formula.}
\item{outForm}{The symbolic outcome equation formula.}
\item{dataSet}{The data-set.}
\item{selBase}{The base category for the selection model.}
\item{outBase}{The base category for the outcome.}
}


\references{
Burgette, Lane F. and Erik V. Nordheim (2009). \dQuote{A Full Gibbs Sampler	for a Multinomial Probit Model with Endogeneity.}  Available from
	the first author's homepage.

Imai, Kosuke and David A. van Dyk (2005). \dQuote{A Bayesian Analysis of 
	the Multinomial Probit Model Using Data Augmentation.} Journal
	of Econometrics.  124(2): 311-34.
}

\author{
Lane F. Burgette, Department of Statistics, University of Wisconsin-Madison
	\email{burgette@stat.wisc.edu}, 
	\url{http://www.stat.wisc.edu/~burgette}
}



\keyword{models}





