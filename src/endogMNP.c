 /******************************************************************
  This file is a part of endogMNP: R Package for Estimating 
  Multinomial Probit Models with Endogeneity by Lane Burgette.  
 Based on MNP code by Kosuke Imai and David A. van Dyk.
  Copyright: GPL version 2 or later.
*******************************************************************/

#include <string.h>
#include <stddef.h>
#include <stdio.h> 
#include <stdlib.h>
#include <math.h>
#include <assert.h>
#include <Rmath.h>
#include <R_ext/Utils.h>
#include <R_ext/Lapack.h>
#include <R.h>
#include "vector.h"
#include "subroutines.h"
#include "rand.h"

void cMNPgibbs(int *piNDim, int *piNCov, int *piP1, int *piP2, int *piNSamp, int *piNGen, 
	       double *b0,    /* prior mean for beta */
	       double *pdA0, int *piNu0, int *nSelCov, int *nOutCov, double *pdS, double *pdX, 
	       int *y,        /* response variable: -1 for missing */
	       double *pdbeta, double *pdSigma, int *piImp, 
	       int *invcdf,   /* use inverse cdf for TruncNorm? */
	       int *piBurnin, /* the number of burnin */
	       int *piKeep,
	       int *verbose,  /* 1 if extra print is needed */ 
	       int *latent,   /* 1 if W is stored */
			   int *piCase1, /* 1 if cov matrix is minimally constrained*/
	       double *pdStore){

	
  /* paramerters from R */
  int n_samp = *piNSamp; /* sample size */
  int n_gen = *piNGen;   /* number of gibbs draws */
  int n_cov = *piNCov;   /* The number of covariates */
	int n_cov1 = *nSelCov; /* number of covariates for selection (added) */
	int n_cov2 = *nOutCov; /* number of covaariates for outcome (added) */
	int n_dim1 = *piP1;
	int n_dim2 = *piP2;
  int n_dim = *piNDim;   /* The number of indentifiable dimension (p-1) */
  int nu0 = *piNu0;      /* nu0: degree of freedom, S: scale matrix */
  int imp = *piImp;      /* 0: improper prior for beta - algorithms 1 & 2 
			    1: proper prior for beta */
	int case1 = *piCase1;	/* minimally constrained */
  int keep = 1;          /* counter for keep */
  int progress = 1;      /* counter for progress report */
  double *beta;	         /* The model parameters */
  double **Sigma;        /* The unidentifiable variance matrix */
  double **X;            /* The covariates and outcome var */
  double **A0;           /* prior precision for beta */
  double **S;            /* The prior parameters for Sigma */

  /* model parameters */
  int **Y;                   /* The response variable */
  double **W;                /* The missing data! */
  double cmean;  	     /* The conditional mean for Wij */
  double cvar;               /* The conditional variance for Wij */
  double maxw=0.0, minw=0.0; /* used for sampling W */
	double holdAlpha = 0.0; /* used to sample alpha2*/
	double trHold = 0.0;   /* used to calculated sub-traces */
	int *bkVec;		/* used to hold breaks between different alpha parts */
	int *alphaBkVec; /* used to hold breaks between different parts of beta */
  int *maxy;
  double **Xbeta;
  double ***PerSig;          /* Permuted Sigma for sampling W */
  int kindx, lindx;          /* Indexes for the permutation of Sigma */
  double *mbeta;             /* Posterior mean of beta */
  double **Vbeta;   	     /* The var of beta, given Yaug */
  double **Xstar;            /* L*X where L is the Chol factor of SigInv */
  double **SigInv;           /* The Inverse of Sigma */
  double *epsilon;           /* The error term */
  double **R;                /* Sum of squares matrix e'e */
  double **SS;	             /* Sum of squares for sweep operator */
  double *alpha2;             /* alpha^2: Inv-chisq df=nu0   turned to vector*/
  double ss;                 /* scale parameter for alpha^2 */
	double *betHold;
  int i, j, k, l, main_loop; /* used for loops */

  /* temporay storages */
  int itemp, itemp2, itempMax, itempMin, *ivtemp, itempS = 0, itempP=ftrunc((double) n_gen/10); 
  double *vtemp,*SSigInvDiag;
  double **mtemp,**mtemp1,**mtemp2;

  /** get random seed **/
  GetRNGstate();
  /** defining vectors and matricies **/
  Y = intMatrix(n_samp, (n_dim1+2)); 
  W = doubleMatrix(n_samp, n_dim);
  X = doubleMatrix(n_samp*n_dim+n_cov, n_cov+1);
  Xbeta = doubleMatrix(n_samp, n_dim);
  SS = doubleMatrix(n_cov+1, n_cov+1);
  Sigma = doubleMatrix(n_dim, n_dim);
  SigInv = doubleMatrix(n_dim, n_dim);
  epsilon = doubleArray(n_samp*n_dim);
  R = doubleMatrix(n_dim, n_dim);
  beta = doubleArray(n_cov);
	betHold = doubleArray(n_cov);
  mbeta = doubleArray(n_cov);
  Vbeta = doubleMatrix(n_cov, n_cov);
  A0 = doubleMatrix(n_cov, n_cov);
  S = doubleMatrix(n_dim, n_dim);
  vtemp = doubleArray(n_dim-1);
	SSigInvDiag = doubleArray(n_dim);	
  maxy = intArray(n_samp);
  ivtemp = intArray(n_dim+1);
  Xstar = doubleMatrix(n_samp*n_dim+n_cov, n_cov+1);
  mtemp = doubleMatrix(n_cov, n_cov);
  mtemp1 = doubleMatrix(n_dim, n_dim);
  mtemp2 = doubleMatrix(n_dim, n_dim);
  PerSig = doubleMatrix3D(n_dim, n_dim, n_dim);
	alpha2=doubleArray(n_dim); 
	bkVec = intArray(n_dim1+3); /* Used to sample W_i-- tells what elements of W_i mean */ 
	alphaBkVec = intArray(n_dim+1); /* for going from beta-tild to beta */


  /** Packing Y, X, A0, S, beta, Sigma  **/
	/** Take vector y, transform to matrix Y */
	itemp = 0;
	for (j=0; j<(n_dim1 + 2); j++)
		for (i=0; i < n_samp; i++) Y[i][j] = y[itemp++]; 
	
	/*PintMatrix(Y, 5,4);*/
 
	itemp = 0;
	for (j=0; j<n_cov; j++)
	for (i=0; i < (n_samp * n_dim); i++)
			X[i][j] = pdX[itemp++];
    
/*	PdoubleMatrix(X, n_cov*3, n_cov);*/
	
  itemp = 0;
  for (k = 0; k < n_cov; k++) 
    for (j = 0; j < n_cov; j++)	A0[j][k] = pdA0[itemp++];


  itemp = 0;
  for (k = 0; k < n_dim; k++) 
	  for (j = 0; j < n_dim; j++) S[j][k] = pdS[itemp++];
	
/*	PdoubleMatrix(S, n_dim, n_dim);*/
	
	
  itemp = 0;
  for (j=0; j<n_cov;j++) 
    beta[j]=pdbeta[itemp++];


	
  itemp = 0;
  for (k = 0; k < n_dim; k++) 
    for (j = 0; j < n_dim; j++) 
      Sigma[j][k] = pdSigma[itemp++];
  dinv(Sigma,n_dim,SigInv); 
	
/** Add bkVec-- gives breaks for components of W_i
 of the form c(0, n_dim1, n_dim1+n_dim_2, ..., n_dim) **/
		
	bkVec[0]=0;
	bkVec[1]=n_dim1;
	for(k=2; k<n_dim1+3; k++){
		bkVec[k] = n_dim1+(k-1)*n_dim2;
	}
	
	/*PintArray(bkVec, n_dim1+3);	*/
	
/* Add alphaBkVec to change from beta to betaTilde
 of the form c(0, n_cov1, 2*n_cov1, ... , n_cov)*/	
	itemp=0;
	alphaBkVec[0]=0;
	for(k=1; k<= n_dim1; k++){
		alphaBkVec[k] = n_cov1*k;
		itemp++;
	}
	for(k=(itemp +1); k< (n_dim +1); k++){
		alphaBkVec[k] = n_cov1*itemp + (k-itemp)*n_cov2;
	}
/*	PintArray(alphaBkVec, n_dim+1);*/
	
  /** add prior information as additional data points **/
  if(imp){
    for(j=0;j<n_cov;j++)
      for(k=0;k<=n_cov;k++)
	Xstar[n_samp*n_dim+j][k]=0;
  }
  else{
    dcholdc(A0,n_cov,mtemp); /* Cholesky decomposition */
    for(j=0;j<n_cov;j++){
      Xstar[n_samp*n_dim+j][n_cov]=b0[j];
      for(k=0;k<n_cov;k++){ 
	Xstar[n_samp*n_dim+j][n_cov]+=mtemp[j][k]*b0[k]; 
	Xstar[n_samp*n_dim+j][k]=mtemp[j][k];
      }
    }
  }
	
	
  /** starting values for W **/
  for(i=0;i<n_samp;i++) {
    for(j=0;j<n_dim;j++){
      Xbeta[i][j]=0;
      for (k=0;k<n_cov;k++) Xbeta[i][j] += X[i*n_dim+j][k]*beta[k];
	/* shouldn't need to start with correct order -- but can
	 
	W[i][j] = TruncNorm(-1000,0,0,.5,*invcdf); 
	  if(Y[i][0] > 0){
	  W[i][Y[i][0]-1] = TruncNorm(0,1000,0,.5,*invcdf); }
		if(Y[i][Y[i][0] + 1] >0){
		W[i][n_dim1 -1 + Y[i][0] * n_dim2 + Y[i][Y[i][0] + 1]] = TruncNorm(0,1000,0,.5,*invcdf);}*/
	W[i][j] = Xbeta[i][j] + norm_rand(); 
  }
  }

/*	PdoubleMatrix(W, 20, n_dim+1);
	PintMatrix(Y, 20, 4);	*/
	
	
  /*** GIBBS SAMPLER! ***/
  for(main_loop=1; main_loop<=n_gen; main_loop++){
	  	  		  
	  
    /* for Algorithm 1 (Scheme 1), draw alpha2 first */

	  /* draw different alpha  
    ss=0;
    for(j=0;j<n_dim;j++)      
      for(k=0;k<n_dim;k++) mtemp1[j][k]=0;
    for(i=0;i<n_dim;i++)
      for(j=0;j<n_dim;j++)
	for(k=0;k<n_dim;k++) mtemp1[j][k]+=S[j][i]*SigInv[i][k];
    for(j=0;j<n_dim;j++) ss+=mtemp1[j][j];
    alpha2=ss/(double)rchisq((double)nu0*n_dim);
	 */

	  if(case1 == 1){
		  for(j=0; j<n_dim; j++){
			  SSigInvDiag[j]=0;
			  for(k=0; k<n_dim; k++){
			  SSigInvDiag[j] += S[j][k]*SigInv[k][j];}}
		  
		  trHold=0;
		  for(k=0; k<n_cov1; k++){
			  trHold+=SSigInvDiag[k];}
	alpha2[0] = 1/((double)rgamma(((double)(nu0*n_dim1))/2.0, 2.0/trHold));
		  for(j=1; j<n_dim1; j++){
		  alpha2[j]=alpha2[0];}
		  
		  for(i=1; i<(n_dim1 +2); i++){
			  trHold = 0;
			  for(j=bkVec[i]; j<bkVec[i+1]; j++){
				  trHold += SSigInvDiag[j];
			  }
			  alpha2[bkVec[i]] = 1/((double)rgamma(((double)(nu0*n_dim2))/2.0, 2.0/trHold));
			  for(j=bkVec[i]; j<bkVec[i+1]; j++){
				  alpha2[j] = alpha2[bkVec[i]];
			  }
		  }}
	  else{
	  for(j=0; j<n_dim;j++){
		  alpha2[j]=1/((double)rgamma(((double)nu0)/2.0, 2.0/SigInv[j][j]));
	  }}
	  
	/*  if(main_loop % 100 == 0){
		  Rprintf("first alpha2\n");
	  PdoubleArray(alpha2, n_dim); */
		/*  PdoubleMatrix(SigInv, n_dim, n_dim);
	  }*/
    /** permutation of Sigma **/
    for(j=0;j<n_dim;j++){
      kindx = 0;
      for(k=0;k<n_dim;k++){ 
	lindx=0;
	for(l=0;l<n_dim;l++){ 
	  if(j!=k)
	    if(j!=l)
	      PerSig[j][k+kindx][l+lindx]=Sigma[k][l];
	    else{
	      lindx=-1;
	      PerSig[j][k+kindx][n_dim-1]=Sigma[k][l];
	    }
	  else{
	    kindx=-1;
	    if(j==l){
	      lindx=-1;
	      PerSig[j][n_dim-1][n_dim-1]=Sigma[j][j];
	    }
	    else
	      PerSig[j][n_dim-1][l+lindx]=Sigma[k][l];
	  }
	}
      }
      dinv(PerSig[j],n_dim,PerSig[j]);
    }

	  
	  
	  
    /** Truncated Multinomial Normal Sampling for W **/
   
      for(i=0;i<n_samp;i++){
		  for(j=0;j<n_dim;j++) {
			  Xbeta[i][j]=0;
		  for(k=0;k<n_cov;k++) Xbeta[i][j]+=X[i*n_dim+j][k]*beta[k];}}
		  
		  /* new version */
	  if(main_loop == 1){  /* do this twice for the first loop-- get correct orderings for first loop*/	  
	  for(i=0; i<n_samp; i++){
		  for(l=0; l < (n_dim1 + 2); l++){
			  for(j = bkVec[l]; j<bkVec[l+1]; j++){
				  maxw=0.0; 
				  for(k=bkVec[l];k<bkVec[l+1];k++) {	  		  		  
					  if(k!=j) {
						  maxw = fmax2(maxw, W[i][k]);
					  }}
				  
				  itemp=0; 
				  for(k=0; k<n_dim; k++) {
					  if(k!=j) {
						  vtemp[itemp++]=W[i][k]-Xbeta[i][k];
					  }}
				  
				  cmean=Xbeta[i][j];
				  cvar=1/PerSig[j][n_dim-1][n_dim-1];
				  
				  for(k=0;k<(n_dim-1);k++) 
					  cmean-=PerSig[j][n_dim-1][k]*vtemp[k]*cvar;
				  /* sampling each W[i][j] conditionally on the other elements */
				  if(Y[i][l]==-1)
					  W[i][j]=cmean+norm_rand()*sqrt(cvar);
				  else if(Y[i][l]==(j+1-bkVec[l])) 
					  W[i][j]=TruncNorm(maxw,cmean+1000,cmean,cvar,*invcdf); 
				  else
					  W[i][j]=TruncNorm(cmean-1000,maxw,cmean,cvar,*invcdf);
				  
				  /*X[i*n_dim+j][n_cov]*=sqrt(alpha2[j]); */
				  /*  if(cvar < .001){
				   Rprintf("%f cvar, %f maxw, %f cmean \n\n", cvar, maxw, cmean);}*/
				  /*if(main_loop == 1){
				   Rprintf("j is %d\n", j);}*/ 
			  }}}}
	  
	  for(i=0; i<n_samp; i++){
		  for(l=0; l < (n_dim1 + 2); l++){
			  for(j = bkVec[l]; j<bkVec[l+1]; j++){
				  maxw=0.0; 
				  for(k=bkVec[l];k<bkVec[l+1];k++) {	  		  		  
					  if(k!=j) {
						  maxw = fmax2(maxw, W[i][k]);
					  }}
					  
					  itemp=0; 
					  for(k=0; k<n_dim; k++) {
						  if(k!=j) {
							  vtemp[itemp++]=W[i][k]-Xbeta[i][k];
						  }}
					  
					  cmean=Xbeta[i][j];
					  cvar=1/PerSig[j][n_dim-1][n_dim-1];
					  
					  for(k=0;k<(n_dim-1);k++) 
						  cmean-=PerSig[j][n_dim-1][k]*vtemp[k]*cvar;
					  /* sampling each W[i][j] conditionally on the other elements */
					  if(Y[i][l]==-1)
						  W[i][j]=cmean+norm_rand()*sqrt(cvar);
					  else if(Y[i][l]==(j+1-bkVec[l])) 
						  W[i][j]=TruncNorm(maxw,cmean+1000,cmean,cvar,*invcdf); 
					  else
						  W[i][j]=TruncNorm(cmean-1000,maxw,cmean,cvar,*invcdf);
					  
				
				  X[i*n_dim+j][n_cov]=W[i][j]* sqrt(alpha2[j]);
					  /*X[i*n_dim+j][n_cov]*=sqrt(alpha2[j]); */
					  /*  if(cvar < .001){
					   Rprintf("%f cvar, %f maxw, %f cmean \n\n", cvar, maxw, cmean);}*/
					  /*if(main_loop == 1){
					  Rprintf("j is %d\n", j);}*/ 
				  }}}
	  
	  
/*	  if(main_loop % 100 == 0){
	  PdoubleMatrix (W, n_dim*4,8);}*/
/*	  if(main_loop % 100 == 50){
		  PintMatrix(Y, 10,4);
		  PdoubleMatrix(W, 10, 8); 
	  }*/
	  
	/*  PintArray(bkVec, (n_dim1+3)); */
		  
    
    /* trace(S*SigInv) -- Shouldn't need this*/
/*    ss=0;*/
	/* change to Sigma-tilde -- because need sigTild to get betaTild here */
		for(j=0;j<n_dim;j++){
		  for(k=0;k<n_dim;k++) {
			  Sigma[j][k]*=(sqrt(alpha2[j])*sqrt(alpha2[k]));
			  SigInv[j][k]/= (sqrt(alpha2[j])*sqrt(alpha2[k]));
		  }}  
	  
    
    /* multiply X and W by the Inverse of the Cholesky factor of SigmaTilde*/
    dcholdc(SigInv,n_dim,mtemp1);
/*	  if(main_loop ==5){
		  Rprintf("chol is \n");
		  PdoubleMatrix(mtemp1, n_dim, n_dim);
		  Rprintf("SigInv is \n");
		  PdoubleMatrix(SigInv, n_dim, n_dim);
	  }*/
    for(i=0;i<n_samp*n_dim;i++)
      for(j=0;j<=n_cov;j++) Xstar[i][j]=0;
    for(i=0;i<n_samp;i++)
      for(j=0;j<n_dim;j++)
	for(k=0;k<n_dim;k++) 
	  for(l=0;l<=n_cov;l++)
	    Xstar[i*n_dim+k][l]+=mtemp1[j][k]*X[i*n_dim+j][l];
		  

 	  
	  
    /* construct SS matrix for SWEEP */
    for(j=0;j<=n_cov;j++)
      for(k=0;k<=n_cov;k++) SS[j][k]=0;
    for(i=0;i<n_samp;i++)
      for(j=0;j<n_dim;j++)
	for(k=0;k<=n_cov;k++)
	  for(l=0;l<=n_cov;l++) 
	    SS[k][l]+=Xstar[i*n_dim+j][k]*Xstar[i*n_dim+j][l];
    for(j=0;j<n_cov;j++)
      for(k=0;k<=n_cov;k++)
	for(l=0;l<=n_cov;l++) 
	  SS[k][l]+=Xstar[n_samp*n_dim+j][k]*Xstar[n_samp*n_dim+j][l];
    
    /* SWEEP to get posterior mean and variance for beta */
    for(j=0;j<n_cov;j++) SWP(SS,j,n_cov+1);
	  
	  
    /* draw alpha2 given Sigma and W */
   /* ss+=SS[n_cov][n_cov];   */
    /* alpha2=ss/(double)rchisq((double)(n_samp+nu0)*n_dim); removed-- can't sample beta and A together*/
    
    /* draw beta given Sigma and W */

    for(j=0;j<n_cov;j++){ 
      mbeta[j]=SS[j][n_cov];
      for(k=0;k<n_cov;k++) Vbeta[j][k]=-SS[j][k]; 
    }
	  
/*	  Shouldn't need this since we used SigmaTilde:
 for(i=0; i<n_dim; i++){
		  for(j=0; j<n_dim; j++){
			  Vbeta[alphaBkVec[i]][alphaBkVec[j]] *= (sqrt(alpha2[i])*sqrt(alpha2[j]));
		  }
	  }*/
 
	  
	  
    rMVN(beta,mbeta,Vbeta,n_cov);  
	  
    /* draw Sigma given betaTilde and W */
	  for(i=0;i<n_samp;i++){
      for(j=0;j<n_dim;j++){
	epsilon[i*n_dim+j]=X[i*n_dim+j][n_cov]; 
	for(k=0;k<n_cov;k++)
	  epsilon[i*n_dim+j]-=X[i*n_dim+j][k]*beta[k];
      }}
	  
	  for(j=0;j<n_dim;j++){
		  for(k=0;k<n_dim;k++){ 
		  R[j][k]=0;}}
	  for(i=0;i<n_samp;i++){
		  for(j=0;j<n_dim;j++){
			  for(k=0;k<n_dim;k++){ 
				  R[j][k]+= (epsilon[i*n_dim+j]*epsilon[i*n_dim+k]);
			  }}}
	  for(j=0;j<n_dim;j++){
		  for(k=0;k<n_dim;k++){ 
		  mtemp1[j][k]=S[j][k]+R[j][k];}}
	  
/*	  if(main_loop %100 == 0){
		  PdoubleArray(epsilon, 100);
	  }*/
	/*  if(main_loop % 100 == 0){
	  Rprintf("S is \n");
	  PdoubleMatrix(S, n_dim, n_dim);}*/
/*	  
	  if(main_loop %100 == 0){
		  PdoubleMatrix(R, n_dim, n_dim);
	  PdoubleArray(epsilon, 16);}*/
/*	  ss=mtemp1[0][0];
	  
	  for(j=0; j<n_dim; j++){
		  for(k=0; j<n_dim; k++){
			  mtemp1[j][k] /= ss;
		  }}*/
			  
/*	  PdoubleMatrix(R, n_dim, n_dim); 
	  PdoubleMatrix(S, n_dim, n_dim);*/
    dinv(mtemp1,n_dim,mtemp2);
	  
/*	  for(j=0; j<n_dim; j++){
		  for(k=0; j<n_dim; k++){
			  mtemp2[j][k] /= ss;
		  }} */
	  
/*	  if(main_loop %100 == 0){
	  PdoubleMatrix(mtemp1, n_dim, n_dim);
	  PdoubleMatrix(mtemp2, n_dim, n_dim);}*/
/* draw SigInv as Wishart, then invert to get Sigma*/	  
	  
    rWish(SigInv,mtemp2,nu0+n_samp,n_dim);
    dinv(SigInv,n_dim,Sigma);
	  
	  
/*	  if(main_loop % 100 == 0){
		  Rprintf("mtemp1 is \n");
	  PdoubleMatrix(mtemp1, n_dim, n_dim);}*/
	  
	  
	/*  if(main_loop % 100 == 0){
	  PdoubleMatrix(Sigma, n_dim, n_dim);}*/
    
    /* recompute some quantities using the updated alpha2 */
	  
	  
	  for(k=0; k<n_dim; k++){
		  for(j=alphaBkVec[k]; j<alphaBkVec[k+1]; j++){
		betHold[j] =  beta[j]/sqrt(alpha2[k]);
		  }}
	  
/*	  for(k=0; k<n_dim; k++){
		  for(j=alphaBkVec[k]; j<alphaBkVec[k+1]; j++){
			  beta[j] =  beta[j]/sqrt(alpha2[k]);
		  }}*/
	  
	  for(j=0;j<n_dim; j++)
		  alpha2[j]=Sigma[j][j];
	  
	if(case1==1){
		for(j=1; j<n_dim1; j++){
			alpha2[j]=alpha2[0];
		}
		
		for(k=1; k<n_dim1+2; k++){
		for(j=bkVec[k]; j<bkVec[k+1]; j++){
		alpha2[j]=alpha2[bkVec[k]];
		}
		}}
	  
		
	  for(j=0;j<n_dim;j++){
      for(k=0;k<n_dim;k++) {
	Sigma[j][k]/= (sqrt(alpha2[j])*sqrt(alpha2[k]));
	SigInv[j][k]*= (sqrt(alpha2[j])*sqrt(alpha2[k]));
      }}
	  
	  
	  for(k=0; k<n_dim; k++){
		  for(j=alphaBkVec[k]; j<alphaBkVec[k+1]; j++){
			  beta[j]/=sqrt(alpha2[k]);
		  }}
	  
/*	  if(main_loop % 100 == 50){
		  Rprintf("second beta\n");
		  PdoubleArray(beta, n_cov);
		  Rprintf("alpha \n");
		  PdoubleArray(alpha2, n_dim);
	  }*/
	  
	  
	  for(i=0;i<n_samp;i++){
		  for(j=0;j<n_dim;j++){
		  W[i][j]=X[i*n_dim+j][n_cov]/sqrt(alpha2[j]);}}

    /* print Gibbs draws */
    R_CheckUserInterrupt();
    if(main_loop > *piBurnin) {
      if(keep==*piKeep) {
	for(j=0;j<n_cov;j++) 
	  pdStore[itempS++]=betHold[j];
	for(j=0;j<n_dim;j++) 
	  for(k=0;k<n_dim;k++) 
	    if(j<=k) 
	      pdStore[itempS++]=Sigma[j][k];
	if (*latent) 
	  for (i=0;i<n_samp;i++) 
	    for (j=0;j<n_dim;j++) 
	      pdStore[itempS++]=W[i][j];

		  
	keep=1;
      }
      else
	keep++;
    }
    if(*verbose) {
      if(main_loop == itempP) {
	Rprintf("%3d percent done.\n", progress*10);
	itempP+=ftrunc((double) n_gen/10); progress++;
	R_FlushConsole(); 
      }
    }
	  } /* end of Gibbs sampler */
  
  /** write out the random seed **/
  PutRNGstate();
  
  /** freeing memory **/
  FreeintMatrix(Y, n_samp);
  FreeMatrix(W, n_samp);
  FreeMatrix(X, n_samp*n_dim+n_cov);
  FreeMatrix(Xbeta, n_samp);
  FreeMatrix(SS, n_cov+1);
  FreeMatrix(Sigma, n_dim);
  FreeMatrix(SigInv, n_dim);
  free(epsilon);
  FreeMatrix(R, n_dim);
  free(beta);
	free(betHold);
  free(mbeta);
	free(alpha2);	
  FreeMatrix(Vbeta, n_cov);
  FreeMatrix(A0, n_cov);
  FreeMatrix(S, n_dim);
  free(vtemp);
  free(maxy);
  free(ivtemp);
  FreeMatrix(Xstar, n_samp*n_dim+n_cov);
  FreeMatrix(mtemp, n_cov);
  FreeMatrix(mtemp1, n_dim);
  FreeMatrix(mtemp2, n_dim);
  Free3DMatrix(PerSig, n_dim, n_dim);
	free(SSigInvDiag);
	free(bkVec);
	free(alphaBkVec);
	

} /* main */



