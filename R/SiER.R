#' @importFrom stats rnorm lm

constMin1 <- function(a, mu)
  # max  a'x such that ||x||_mu \e 1.
{
  nvar <- length(a)
  x <- rep(1,nvar)
  aa <- abs(a)
  aa.sort <- sort(aa, decreasing=T, index.return=T, method="quick")
  aas <- aa.sort$x
  aas.sum <- sum(aas)
  aas.cum <- cumsum(aas)
  flag <- c(aas<=mu*aas.cum/(1+(1:nvar-1)*mu), TRUE)
  mc <- which(flag)[1]-1

  tmp <- mu * aas.cum[mc] / (1+(mc-1)*mu)
  x <- c(aas[1:mc] - tmp, rep(0, nvar-mc))

  b <- sort(aa.sort$ix, index.return=T)
  x <- x[b$ix]

  norm= sqrt(mu*(sum(abs(x)))^2+(1-mu)*sum(x^2))
  x <- as.numeric(lapply(a,sign)) * x / norm

  return(list(x=x, norm=norm, m=mc,I=sort(aa.sort$ix[1:mc])))
}





constOpt2.luo <- function(gamma, Psi, t0, nvar, tau, mu, tol=10^(-12))
  #find t to minimize H, or find t so that f(gamma+Psi %*% t) is orthogonal to the space spanned by columns in Psi.
  # f(gamma + Psi %*% t) is solution to problem (7.10) in paper.
{
  Psi=as.matrix(Psi)
  t=as.vector(t0) #added
  dim.old <- dim(Psi)[2]

  temp=as.vector(gamma+Psi %*% t)   #gamma.orthogonal
  d=length(temp)
  Psi.1=Psi[1:(d-nvar),]
  Psi.2=Psi[-(1:(d-nvar)),]
  b=temp[1:(d-nvar)]
  a=temp[-(1:(d-nvar))]

  ret <- constMin1(a,mu)
  x<- ret$x              # correspond to x(t) in proof of theorem 2.6
  nu <- ret$norm / 2
  m <- ret$m
  h <- as.vector((tau*t(b)%*%Psi.1+(2*nu/(1-mu))*t(x)%*%Psi.2))
  H <- sum(h^2)
  alpha <- mu / (1+(m-1)*mu)

  count1 <- 0


  while(H>tol){
    count1 <- count1+1
    #print(c(207,count1, H))

    if(count1 > 100){
      break;
    }

    I=which(x!=0)
    signx <- sign(x[I])
    if(length(I)<(nvar/2))
    { NNPsi <- Psi.2[I,]
    K <- NNPsi - alpha * (signx %*% (t(signx) %*% NNPsi))
    A=(tau*t(Psi.1)%*%Psi.1+t(K)%*%NNPsi/(1-mu))
    }else{
      NNPsi <- Psi.2[-I,]
      if((nvar-length(I))==1){NNPsi=(t(as.matrix(NNPsi)))}
      temp=t(Psi.2[I,])%*%signx
      A=((tau-1/(1-mu))*t(Psi.1)%*%Psi.1+(diag(dim.old)-t(NNPsi)%*%NNPsi-alpha*temp%*%t(temp))/(1-mu))
    }
    A <- (A+t(A))/2
    deriv.1 <- 2*A %*% h
    if(count1==1)
    {diag.delta=0.01*max(eigen(A)$values)
    ll=dim(A)[1]
    }
    t.inc=-solve(A+diag.delta*diag(ll), h)

    t.new <- as.vector(t + t.inc)

    temp=as.vector(gamma+tcrossprod(Psi, t(t.new)))
    b=temp[1:(d-nvar)]
    a=temp[-(1:(d-nvar))]
    ret <- constMin1(a,mu)
    x.new<- ret$x              # correspond to x(t) in proof of theorem 2.6
    nu.new <- ret$norm / 2
    m.new <- ret$m
    alpha.new <- mu / (1+(m.new-1)*mu)
    h.new <- as.vector((tau*t(b)%*%Psi.1+(2*nu.new/(1-mu))*t(x.new)%*%Psi.2))
    H.new <- sum(h.new^2)
    count2=0
    #print(c("range eigen of A=",range(eigen(A)$values)))
    # print(t(t.inc)%*%(A%*%h))
    while(((H.new>tol)&(H.new>H+(1e-4)*t(t.inc)%*%deriv.1))&(count2<5)){

      #print(sqrt(sum(t.inc^2)))
      count2 <- count2+1
      t.inc <- 0.3 * t.inc
      t.new <- as.vector(t + t.inc)
      #    print(c("count2=", count2))
      if(count2 > 4){
        temp=rnorm(length(t),0,1)
        t.new=t+0.1*temp/sqrt(sum(temp^2))
      }


      temp=as.vector(gamma+Psi %*% t.new)
      b=temp[1:(d-nvar)]
      a=temp[-(1:(d-nvar))]
      ret <- constMin1(a,mu)
      x.new<- ret$x              # correspond to x(t) in proof of theorem 2.6
      nu.new <- ret$norm / 2
      m.new <- ret$m
      alpha.new <- mu / (1+(m.new-1)*mu)
      h.new <- as.vector((tau*t(b)%*%Psi.1+(2*nu.new/(1-mu))*t(x.new)%*%Psi.2))
      H.new <- sum(h.new^2)
    }
    #print(c("count2=", count2))
    t <- t.new
    h=h.new
    nu=nu.new
    H <- H.new
    x <- x.new
    m=m.new
    alpha <- alpha.new
  } # end of while(H>tol)


  t1=2*nu/(1-mu)
  t2=tau*sum(b^2)
  v=c((sqrt(tau)/sqrt(t1^2+t2))*b, t1*x/sqrt(tau*(t1^2+t2)))
  return(list(x=v, t=t,count1=count1))
}


determineMaxKcomp <- function(X, Y, params.set, upper.comp, thresh)
{
  repeat.solution=1
  tol=1e-12
  tol.1=10^{-8}
  p=dim(params.set)[1]
  nobs=dim(X)[1]
  nvar <- dim(X)[2]
  nvarY <- dim(Y)[2]
  max.m=min(upper.comp,nvarY)
  K.comp <- rep(max.m,p)
  x <- X
  y <- Y
  nobs <- dim(x)[1]
  muy <- drop(rep(1,nobs) %*% y) / nobs
  z.y <- scale(y,muy,scale=FALSE)
  mux <- drop(rep(1,nobs) %*% x) / nobs
  z.x <- scale(x,mux,scale=FALSE)

  Lambda.mtx <- cbind(diag(nobs),-z.x)
  Psi.0 <- svd(Lambda.mtx,nu=0)$v
  sigma.xy <- crossprod(z.x, z.y)/sqrt(nobs)
  sigma.yx <- t(sigma.xy)
  sigma.xx <- crossprod(z.x, z.x)

  obj.vals <- matrix(0,p,max.m)
  for(j in 1:p)
  {
    tau=params.set[j,1]
    mu=params.set[j,2]

    Beta=NULL
    Psi=Psi.0

    for(ncomp in 1:max.m)
    {
      if(!is.null(Beta))
      {
        temp <- rbind(matrix(0,nobs,1),sigma.xx %*% beta)
        tt <- temp-Psi%*%(t(Psi)%*%temp)
        Psi <- cbind(Psi, tt/sqrt(sum(tt^2)))
      }

      qq=rep(0,repeat.solution)
      mqq=0
      for(jj in 1:repeat.solution)
      {
        gamma=rnorm(nobs+nvar,0,1)
        gamma.old=rep(0, nobs+nvar)
        count=0
        value=sum((sigma.yx%*%gamma[-(1:nobs)])^2)
        value.old=0
        while((value>value.old)&(min(t(gamma-gamma.old)%*%(gamma-gamma.old), t(gamma+gamma.old) %*% (gamma+gamma.old)) > sum(gamma^2)*tol.1))
        { if(count>0){value.old=value}
          count=count+1
          temp=sigma.xy %*% (sigma.yx %*%gamma[-(1:nobs)])
          t0=-crossprod(Psi, gamma)
          temp.1=temp/sqrt(sum(temp^2))

          ret=constOpt2.luo(c(rep(0,nobs),temp.1), Psi, t0, nvar, tau, mu)
          gamma.old=gamma
          gamma=ret$x
          value=sum((sigma.yx%*%gamma[-(1:nobs)])^2)
        }
        qq[jj]=value
        #print(c("value, qq[jj], tau, mu=", value, qq[jj], tau, mu))
        if(qq[jj]>mqq)
        {
          mqq=qq[jj]
          beta=gamma[-(1:nobs)]
        }
      }
      obj.vals[j,ncomp] <- mqq
      Beta=cbind(Beta,beta)
      #print(c("mqq=",mqq))
      if(mqq/sum(obj.vals[j,])<thresh){
        K.comp[j] <- ncomp
        break;
      }
    }#end of for(ncomp in 1:(nvarY-1))
  }

  return(list( obj.vals=obj.vals, max.K=K.comp))
}



getAllComponents <- function(x, y, K.comp, tau, mu, tol=10^(-12), repeat.solution=1, tol.1=10^{-8})
{
  nvar <- dim(x)[2]
  nobs <- dim(x)[1]
  muy <- drop(rep(1,nobs) %*% y) / nobs
  z.y <- scale(y,muy,scale=FALSE)
  mux <- drop(rep(1,nobs) %*% x) / nobs
  z.x <- scale(x,mux,scale=FALSE)
  Lambda.mtx <- cbind(diag(nobs),-z.x)
  Psi.0 <- svd(Lambda.mtx,nu=0)$v

  sigma.xy <- t(z.x) %*% z.y/sqrt(nobs)
  sigma.yx <- t(sigma.xy)
  sigma.xx <- t(z.x) %*% z.x

  Beta=NULL
  Psi=Psi.0
  for(ncomp in 1:K.comp){
    #         Lambda=Lambda.0
    #        print(c("ncomp=",ncomp))
    if(!is.null(Beta))
    {
      temp <- rbind(matrix(0,nobs,1),sigma.xx %*% beta)
      tt <- temp-Psi%*%(t(Psi)%*%temp)
      Psi <- cbind(Psi, tt/sqrt(sum(tt^2)))
      #             print(Psi[,-(1:100)])
    }

    qq=rep(0,repeat.solution)
    mqq=0
    for(jj in 1:repeat.solution)
    {
      pt <- proc.time()
      gamma=rnorm(nobs+nvar,0,1)
      gamma.old=rep(0, nobs+nvar)
      count=0
      value=sum((sigma.yx%*%gamma[-(1:nobs)])^2)
      value.old=0

      while((value>value.old)&(min(t(gamma-gamma.old)%*%(gamma-gamma.old), t(gamma+gamma.old) %*% (gamma+gamma.old)) > sum(gamma^2)*tol.1))
      { if(count>0)
        value.old=value
      count=count+1

      temp=sigma.xy %*% (sigma.yx %*%gamma[-(1:nobs)])
      t0=-t(Psi)%*%gamma
      temp.1=temp/sqrt(sum(temp^2))

      ret=constOpt2.luo(c(rep(0,nobs),temp.1), Psi,t0, nvar, tau, mu)

      gamma.old=gamma
      gamma=ret$x
      value=sum((sigma.yx%*%gamma[-(1:nobs)])^2)
      }
      qq[jj]=value
      #print(c("value, qq[jj], tau, mu=", value, qq[jj], tau, mu))
      if(qq[jj]>mqq)
      {mqq=qq[jj]
      beta=gamma[-(1:nobs)]
      }
      #             print(c(ncomp, proc.time()-pt, count, mqq, value))
    }
    Beta=cbind(Beta,beta)
  }
  return(list(z.x=z.x, z.y=z.y, mux=mux, muy=muy, Beta=Beta))
}




getError <- function(x,y,x.test,y.test,W)
{
  t.mtx <- x %*% W
  q.mtx <- as.matrix(lm(y~t.mtx-1)$coef)
  error <- sum((y.test-x.test %*% W %*% q.mtx)^2)
  return(error)
}

getErrors <- function(x,y,x.test,y.test,W)
{
  error <- rep(0,dim(W)[2])
  coefnorm <- matrix(0, dim(W)[2], dim(W)[2])
  for(i in 1:dim(W)[2]){
    t.mtx <- x %*% W[,1:i]
    q.mtx <- as.matrix(lm(y~t.mtx-1)$coef)
    coefnorm[i,1:i] <- diag(q.mtx %*% t(q.mtx))
    error[i] <- sum((y.test-x.test %*% W[,1:i] %*% q.mtx)^2)
  }
  #    print(coefnorm)
  return(error)
}

cv.folds=function (n, folds = 10)
{
  split(sample(1:n), rep(1:folds, length = n))
}


#' @export
cv.SiER <- function(X, Y,   K.cv=5, upper.comp=10, thresh=0.01)
  # randomly partion X into x (training data) and x.valid (validation data)
{
  is.univariate=FALSE
  if(!is.matrix(Y))
  {
#    Y=cbind(Y,Y)
      Y=as.matrix(Y, ncol=1)
    is.univariate=TRUE
  }
  repeat.solution=1
  tol=10^(-12)
  tol.1=10^{-8}
  params.set <- cbind(c(0.0005, 0.001, 0.005, 0.01,  0.05, 0.1, 0.5, 1, 5),
                  c(0.005, 0.01, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35))
  p=dim(params.set)[1]

  scale.x=max(abs(X))
  X=X/scale.x
  print("Calculate the maximum components for each of all combinations of tuning parameters")
  max.K <- determineMaxKcomp(X, Y, params.set, upper.comp, thresh)$max.K
  errors=list()
  for(j in 1:p)
    errors[[j]]= rep(0,max.K[j])
  nvar <- dim(X)[2]
  all.folds <- cv.folds(dim(Y)[1],K.cv)
  print("Starting the cross-validation procedure:")
  for(i in seq(K.cv))
  {
    print(paste0("fold ", i))
    omit <- all.folds[[i]]
    x <- X[-omit,]
    y <- Y[-omit,]
    x.valid <- X[omit,]
    y.valid <- Y[omit,]
    nobs <- dim(x)[1]
    muy <- drop(rep(1,nobs) %*% y) / nobs
    z.y <- scale(y,muy,scale=FALSE)
    z.y.valid <- scale(y.valid,muy,scale=FALSE)
    mux <- drop(rep(1,nobs) %*% x) / nobs
    z.x <- scale(x,mux,scale=FALSE)
    z.x.valid <- scale(x.valid,mux,scale=FALSE)

    Lambda.mtx <- cbind(diag(nobs),-z.x)
    Psi.0 <- svd(Lambda.mtx,nu=0)$v
    ### ignoring the diagonal elements from svd, which was Lambda in Xin's code


    sigma.xy <- crossprod(z.x, z.y)/sqrt(nobs)
    sigma.yx <- t(sigma.xy)
    sigma.xx <- crossprod(z.x, z.x)

    for(j in 1:p)
    {
      tau=params.set[j,1]
      mu=params.set[j,2]
      K.comp <- max.K[j]

      #print(c(tau,mu))
      Beta=NULL
      Psi=Psi.0
      for(ncomp in 1:K.comp)
      {
        if(!is.null(Beta))
        {
          temp <- rbind(matrix(0,nobs,1),sigma.xx %*% beta)
          tt <- temp-Psi%*%(t(Psi)%*%temp)
          #                  Psi=cbind(Psi,svd(t(tt),0)$v)
          Psi <- cbind(Psi, tt/sqrt(sum(tt^2)))
        }

        qq=rep(0,repeat.solution)
        mqq=0
        for(jj in 1:repeat.solution)
        {
          gamma=rnorm(nobs+nvar,0,1)
          gamma.old=rep(0, nobs+nvar)
          count=0
          value=sum((sigma.yx%*%gamma[-(1:nobs)])^2)
          value.old=0
          while((value>value.old)&(min(t(gamma-gamma.old)%*%(gamma-gamma.old), t(gamma+gamma.old) %*% (gamma+gamma.old)) > sum(gamma^2)*tol.1))
          { if(count>0){value.old=value}
            count=count+1
            temp=sigma.xy %*% (sigma.yx %*%gamma[-(1:nobs)])
            t0=-t(Psi)%*%gamma
            temp.1=temp/sqrt(sum(temp^2))

            ret=constOpt2.luo(c(rep(0,nobs),temp.1), Psi, t0, nvar, tau, mu)
            gamma.old=gamma
            gamma=ret$x
            value=sum((sigma.yx%*%gamma[-(1:nobs)])^2)
          }
          qq[jj]=value
          #print(c("value, qq[jj], tau, mu=", value, qq[jj], tau, mu))

          if(qq[jj]>mqq)
          {
            mqq=qq[jj]
            beta=gamma[-(1:nobs)]
          }
        }
        Beta=cbind(Beta,beta)
      }#end of for(ncomp in 1:(K.comp-1))

      Beta <- matrix(Beta, nrow=nvar, ncol=K.comp)
      errors[[j]]=errors[[j]]+getErrors(z.x,z.y,z.x.valid, z.y.valid, Beta)
    }
  }

  min.error=rep(0,p)
  for(j in 1:p)
    min.error[j]=min(errors[[j]],na.rm = TRUE)
  temp=which.min(min.error)
  min.tau1 <- params.set[temp,1]
  min.mu1 <- params.set[temp,2]
  opt.K1=which.min(errors[[temp]])


  alltrain10.ret1 <- getAllComponents(X, Y, opt.K1, min.tau1, min.mu1)
  X=alltrain10.ret1$z.x
  Y=alltrain10.ret1$z.y
  muy=alltrain10.ret1$muy
  t.mtx <- X %*% alltrain10.ret1$Beta
  q.mtx <- as.matrix(lm(Y~t.mtx-1)$coef)
  beta=alltrain10.ret1$Beta %*% q.mtx
  ind=which(apply(beta^2,1,sum)!=0)
  X.new=matrix(0,length(ind),dim(beta)[1])
  X.new[,ind]=diag(length(ind))
  X.0=rep(0,dim(beta)[1])
  X.test=rbind(X.0, X.new)
  X.test=X.test/scale.x
  z.x.test <- scale(X.test, alltrain10.ret1$mux, scale=FALSE)
  tmp.1= z.x.test %*% alltrain10.ret1$Beta %*% q.mtx
  Y.pred <- scale(tmp.1, -muy, scale=FALSE)
  mu=Y.pred[1,]
  tmp=as.matrix(Y.pred[-1,])
  beta[ind,]=t(sapply(1:dim(tmp)[1],function(k){tmp[k,]-mu}))

  return(list(mu=mu, beta=beta, min.error=min(min.error,na.rm = TRUE), scale.x=scale.x,  X=X,Y=Y, params.set=params.set, error=errors, opt.K=opt.K1, opt.tau=min.tau1, opt.lambda=min.mu1)) #, is.univariate=is.univariate))
}

#' @export
pred.SiER<- function(cv.fit, X.new)
{
  if(!is.matrix(X.new)){
      X.new=t(as.matrix(X.new))
  }
  mu=cv.fit$mu
  tmp=X.new%*%cv.fit$beta
  Y.pred=t(sapply(1:dim(tmp)[1], function(k){mu+tmp[k,]}))
#  if(cv.fit$is.univariate){Y.pred=Y.pred[,1]}
  return(Y.pred)
}

#' @export
getcoef.SiER<- function(cv.fit)
{
  mu=cv.fit$mu
  beta=cv.fit$beta
  nonzero.ind=which(apply(beta^2,1,sum)!=0)
#  if(cv.fit$is.univariate){beta=beta[,1]}
  return(list(mu=mu, beta=beta, nonzero.ind=nonzero.ind))
}




