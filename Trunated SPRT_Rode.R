cs<-function(s,r,n){      										
  covmat <-matrix(NA,n,n)													
  for(i in 1:n){											
    for(j in 1:n){											
      if(i==j)									
      {covmat[i,j]<-s}								
      else{covmat[i,j]<-r}									
    }									
  }										
  return(covmat)													
}											

ar1<-function(s,r,n){  												
  covmat <-matrix(NA,n,n)													
  for(i in 1:n){											
    for(j in 1:n){											
      if(i==j)									
      {covmat[i,j]<-s}								
      else{covmat[i,j]<-r^abs(j-i)}									
    }									
  }										
  return(covmat)													
}													

library(mnormt)

#Homogeneous Multivariate Normal Case

tsprt<-function(m0,m1,cov,c10,c01,cn0,cn1,pi1,method,detail,int) {
  m0<-as.vector(m0)
  m1<-as.vector(m1)
  cov<-as.matrix(cov)
  K<-length(m0)
  m<-K-1
  ## Default input setting
  if(missing(pi1)||is.null(pi1)) {pi1<-0.5}
  pi0=1-pi1
  if(missing(method)||is.null(method)) {method<-1}
  if(missing(detail)||is.null(detail)) {detail<-FALSE}

  ## Stop and print error
  if(K==1)
  {stop("The maximum stage should be at least 2")}
  if(length(m1)!=K||length(c10)!=K||length(c01)!=K||nrow(cov)!=K)
  {stop("All input vectors should be the same lengths")}
  if(length(c01)<m||length(cn0)<m)
  {stop("lengths of cn0 and cn1 should be K-1")}
  for(i in 1:m){
    if(min(c10[i],c01[i])<=max(cn0[i],cn1[i]))
    {stop("c10 and c01 should be greater than cn0 and cn1")}
  }
 
  ## Create Weight matrix W
  weight<-function(n){          								
    w<-matrix(NA,n,n)													
    for(i in 1:n){											
      for(j in 1:n){											
        if(i<j)									
        {w[i,j]<-0}								
        else									
        {c<-t(m1-m0)[1:i]%*%solve(cov[1:i,1:i])								
         w[i,j]<-c[j]}								
      }				
    }										
    return(w)													
  }	
  
  ## Density of weighted sum
  W<-weight(K)																		
  s_cov<-W%*%cov%*%t(W)									
  s_m0<-as.vector(t(W%*%m0))								
  s_m1<-as.vector(t(W%*%m1))
  
  ## Set 'llim' and 'ulim'to make the posterior probabilities vary in the interval (0,1).
  ## Choose llim and ulim to be the minimum and maximum values of 'S'
  ###for which the marginal density is greater than zero (>1e-310)
  
  margin<-function(k,L){              						
    s<-t(m1-m0)[1:k]%*%solve(cov[1:k,1:k])%*%(m1+m0)[1:k]/2+log(pi0/pi1)+log(L/(1-L))	
    mar<-dnorm(s,mean=s_m0[k],sd=s_cov[k,k]^0.5)*pi0+dnorm(s,mean=s_m1[k],sd=s_cov[k,k]^0.5)*pi1
    return(mar)}
  
  llim<-as.vector(rep(c(NA),2*m))
  ulim<-as.vector(rep(c(NA),2*m))
  tol<-1e-06
  for (k in m:1){   
    if(margin(k,tol)>tol||margin(k,1-tol)>tol) { 
      llim[k]<-tol
      llim[k+m]<-tol
      ulim[k]<-1-tol
      ulim[k+m]<-1-tol
    }else{
      for(i in 1:999){ 
        L<-i/1000
        if(margin(k,L)>1e-310)break
      }
      llim[k]<-L
      llim[k+m]<-L
      for(i in 999:1){ 
        U<-L+(1-L)*i/1000
        if(margin(k,U)>1e-310)break
      }
      ulim[k]<-U
      ulim[k+m]<-U
      if(llim[k]==ulim[k]){
        llim[k]<-tol
        llim[k+m]<-tol
        ulim[k]<-1-tol
        ulim[k+m]<-1-tol
      }
    }             
  }
  

   
  ## Function for evaluating stopping boundaries
  ## Detail=c(FALSE,TRUE)
  evaluation<-function(L0,L1,detail){
    
    Cost<-as.vector(rep(NA,K))
    errorrate10<-as.vector(rep(0,K))
    errorrate01<-as.vector(rep(0,K)) 
    stoprate0<-as.vector(rep(0,K))
    stoprate1<-as.vector(rep(0,K)) 
    stoprate<-as.vector(rep(0,K))
    stoptime<-as.vector(rep(0,K))
    nz0<-as.vector(rep(0,K))
    nz1<-as.vector(rep(0,K))    
    rL0<-as.vector(rep(0,K))
    rL1<-as.vector(rep(0,K))    
    
    #Define domain of integration for evaluating EC
    for(j in 1:K){
      rL0[j]<-t(m1-m0)[1:j]%*%solve(cov[1:j,1:j])%*%(m1+m0)[1:j]/2+log(pi0/pi1)+ log(L0[j]/(1-L0[j]))                  					
      rL1[j]<-t(m1-m0)[1:j]%*%solve(cov[1:j,1:j])%*%(m1+m0)[1:j]/2+log(pi0/pi1)+ log(L1[j]/(1-L1[j]))
      
      lower_10<-as.vector(rep(NA,j))
      lower_n<-as.vector(rep(NA,j))
      lower_01<-as.vector(rep(NA,j))    
      upper_10<-as.vector(rep(NA,j))
      upper_n<-as.vector(rep(NA,j))
      upper_01<-as.vector(rep(NA,j))
      
      for(i in 1:j){
        
        if(i<j){  
          lower_10[i]<-rL0[i]
          lower_01[i]<-rL0[i]
          lower_n[i]<-rL0[i]
          upper_10[i]<-rL1[i]
          upper_n[i]<-rL1[i]
          upper_01[i]<-rL1[i]
        } else if(i!=K){    
          lower_10[i]<-rL1[i]
          lower_01[i]<--Inf
          lower_n[i]<-rL0[i]
          upper_10[i]<-Inf
          upper_n[i]<-rL1[i]
          upper_01[i]<-rL0[i]
        } else {                 
          lower_10[i]<-rL1[i]
          lower_01[i]<--Inf
          lower_n[i]<-0
          upper_10[i]<-Inf
          upper_n[i]<-0
          upper_01[i]<-rL0[i]
        }            
      }
      
      if(j==K){
        Cost[j]<-c10[j]*sadmvn(lower=lower_10,upper=upper_10, mean=s_m0[1:j], varcov=s_cov[1:j,1:j])*pi0+      									
          c01[j]*sadmvn(lower=lower_01,upper=upper_01, mean=s_m1[1:j], varcov=s_cov[1:j,1:j])*pi1											
        
      }else{
        Cost[j]<-c10[j]*sadmvn(lower=lower_10,upper=upper_10, mean=s_m0[1:j], varcov=s_cov[1:j,1:j])*pi0+      									
          c01[j]*sadmvn(lower=lower_01,upper=upper_01, mean=s_m1[1:j], varcov=s_cov[1:j,1:j])*pi1+												
          cn0[j]*sadmvn(lower=lower_n,upper=upper_n, mean=s_m0[1:j], varcov=s_cov[1:j,1:j])*pi0+												
          cn1[j]*sadmvn(lower=lower_n,upper=upper_n, mean=s_m1[1:j], varcov=s_cov[1:j,1:j])*pi1	         
      }
      nz0[j]<-sadmvn(lower=lower_n,upper=upper_n, mean=s_m0[1:j], varcov=s_cov[1:j,1:j])
      nz1[j]<-sadmvn(lower=lower_n,upper=upper_n, mean=s_m1[1:j], varcov=s_cov[1:j,1:j])  					
      
      if(j==1){
        stoprate0[j]<-1-nz0[j]
        stoprate1[j]<-1-nz1[j]
        stoprate[j]<-stoprate0[j]*pi0+stoprate1[j]*pi1
        stoptime[j]<-j*stoprate0[j]*pi0+j*stoprate1[j]*pi1
        errorrate10[j]<-sadmvn(lower=lower_10,upper=upper_10, mean=s_m0[1:j], varcov=s_cov[1:j,1:j])  										
        errorrate01[j]<-sadmvn(lower=lower_01,upper=upper_01, mean=s_m1[1:j], varcov=s_cov[1:j,1:j])
        
      }else{
        stoprate0[j]<-nz0[j-1]-nz0[j]
        stoprate1[j]<-nz1[j-1]-nz1[j]
        stoprate[j]<-stoprate[j-1]+stoprate0[j]*pi0+stoprate1[j]*pi1
        stoptime[j]<-j*stoprate0[j]*pi0+j*stoprate1[j]*pi1
        errorrate10[j]<-errorrate10[j-1]+sadmvn(lower=lower_10,upper=upper_10, mean=s_m0[1:j], varcov=s_cov[1:j,1:j])    									
        errorrate01[j]<-errorrate01[j-1]+sadmvn(lower=lower_01,upper=upper_01, mean=s_m1[1:j], varcov=s_cov[1:j,1:j])
      }
    }
    if(detail==FALSE){
      list(error10=errorrate10[K],error01=errorrate01[K],stoptime=sum(stoptime),EC=sum(Cost))
    }else{
      list(error10=errorrate10,error01=errorrate01,stoprate=stoprate,stoptime=sum(stoptime),EC=Cost)
    }
  }
  
  ## Create vectors of stopping boundaries
  sol.L0<-as.vector(rep(NA,K))
  sol.L1<-as.vector(rep(NA,K)) 
  
  
  ## tsprt solution by recursive algorithm (method 1)
  if(method=="recursive"|method==1){
    
    #Soution of the final stage K
    sol.L0[K]<-c10[K]/(c01[K]+c10[K])
    sol.L1[K]<-c10[K]/(c01[K]+c10[K])
    
    #Define future risk for group 0(errortype=10) or 1(errortype=01).
    risk<-function(k,L,errortype){    
      u<-k+1
      n<-K-k
      L0<-as.vector(rep(NA,n))
      L1<-as.vector(rep(NA,n))
      rL0<-as.vector(rep(NA,n))
      rL1<-as.vector(rep(NA,n))
      sumr<-0    
      s<-t(m1-m0)[1:k]%*%solve(cov[1:k,1:k])%*%(m1+m0)[1:k]/2+log(pi0/pi1)+log(L/(1-L))  
      
      for (j in 1:n){
        l<-j+k
        L0[j]<-sol.L0[l]				
        L1[j]<-sol.L1[l]
        rL0[j]<-t(m1-m0)[1:l]%*%solve(cov[1:l,1:l])%*%(m1+m0)[1:l]/2+log(pi0/pi1)+ log(L0[j]/(1-L0[j]))												
        rL1[j]<-t(m1-m0)[1:l]%*%solve(cov[1:l,1:l])%*%(m1+m0)[1:l]/2+log(pi0/pi1)+ log(L1[j]/(1-L1[j]))
        con_m0<-s_m0[u:l]+s_cov[u:l,k]/s_cov[k,k]*(s-s_m0[k])												
        con_s0<-s_cov[u:l,u:l]-s_cov[u:l,k]%*%solve(s_cov[k,k])%*%s_cov[k,u:l]
        con_m1<-s_m1[u:l]+s_cov[u:l,k]/s_cov[k,k]*(s-s_m1[k])												
        con_s1<-s_cov[u:l,u:l]-s_cov[u:l,k]%*%solve(s_cov[k,k])%*%s_cov[k,u:l]
        
        lower_10<-as.vector(rep(NA,j))
        lower_n<-as.vector(rep(NA,j))
        lower_01<-as.vector(rep(NA,j))
        upper_10<-as.vector(rep(NA,j))
        upper_n<-as.vector(rep(NA,j))
        upper_01<-as.vector(rep(NA,j))     
        
        for(i in 1:j){
          
          if(i<j){   
            lower_10[i]<-rL0[i]
            lower_01[i]<-rL0[i]
            lower_n[i]<-rL0[i]
            upper_10[i]<-rL1[i]
            upper_n[i]<-rL1[i]
            upper_01[i]<-rL1[i]
          } else if(i!=n){  
            lower_10[i]<-rL1[i]
            lower_01[i]<--Inf
            lower_n[i]<-rL0[i]
            upper_10[i]<-Inf
            upper_n[i]<-rL1[i]
            upper_01[i]<-rL0[i]
          } else {              
            lower_10[i]<-rL1[i]
            lower_01[i]<--Inf
            lower_n[i]<-0
            upper_10[i]<-Inf
            upper_n[i]<-0
            upper_01[i]<-rL0[i]
          }       
        }
        #Compute Risk(L,errotype==10)
        if(errortype==10){
          r<-c10[j]*sadmvn(lower=lower_10,upper=upper_10, mean=con_m0[1:j], varcov=con_s0)+																								
            cn0[j]*sadmvn(lower=lower_n,upper=upper_n, mean=con_m0[1:j], varcov=con_s0)												       
          sumr<-sumr+r[1]        
        } else{
          #Compute Risk(L,errotype==01)         
          r<-c01[j]*sadmvn(lower=lower_01,upper=upper_01, mean=con_m1[1:j], varcov=con_s1)+												
            cn1[j]*sadmvn(lower=lower_n,upper=upper_n, mean=con_m1[1:j], varcov=con_s1)        
          sumr<-sumr+r[1]        
        }              
      }
      return(sumr)
    }
    
    ## Backward induction from stage K-1 to stage 1 
    for (k in m:1){    
      ## PEL(0)-PEL(N): equation for L0k
      solve_L0<-function(L){          								
        s<-t(m1-m0)[1:k]%*%solve(cov[1:k,1:k])%*%(m1+m0)[1:k]/2+log(pi0/pi1)+log(L/(1-L))	
        px0<-dnorm(s,mean=s_m0[k],sd=s_cov[k,k]^0.5)*pi0
        px1<-dnorm(s,mean=s_m1[k],sd=s_cov[k,k]^0.5)*pi1
        px<-px0+px1
        pel0<-c01[k]*px1/px
        pel1<-c10[k]*px0/px
        peln<-((cn1[k]+risk(k,L,01))*px1+(cn0[k]+risk(k,L,10))*px0)/px
        I_0<-pel0-peln 
        return(I_0)												
      }
      ## ## PEL(1)-PEL(N): equaiton for L1k											
      solve_L1<-function(L){    											
        s<-t(m1-m0)[1:k]%*%solve(cov[1:k,1:k])%*%(m1+m0)[1:k]/2+log(pi0/pi1)+log(L/(1-L))	
        px0<-dnorm(s,mean=s_m0[k],sd=s_cov[k,k]^0.5)*pi0
        px1<-dnorm(s,mean=s_m1[k],sd=s_cov[k,k]^0.5)*pi1
        px<-px0+px1
        pel0<-c01[k]*px1/px
        pel1<-c10[k]*px0/px
        peln<-((cn1[k]+risk(k,L,01))*px1+(cn0[k]+risk(k,L,10))*px0)/px
        I_1<-pel1-peln
        return(I_1)												
      } 
      ## If llim and ulim return the same sign, then L0k=0 and L1k=1
      if (solve_L0(llim[k])*solve_L0(ulim[k])>0){
        root.L0<-llim[k]
      }else{
        root.L0<-uniroot(solve_L0,lower=llim[k],upper=ulim[k])$root}
      if (solve_L1(llim[k])*solve_L1(ulim[k])>0){
        root.L1<-ulim[k]
      }else{
        root.L1<-uniroot(solve_L1,lower=llim[k+m],upper=ulim[k+m])$root}
      ## If L0k>L1k, then the current stage become the final stage
      if(root.L0>root.L1){
        K<-k
        sol.L0<-as.vector(rep(NA,K))
        sol.L1<-as.vector(rep(NA,K))  
        sol.L0[k]<-c10[k]/(c01[k]+c10[k])      										
        sol.L1[k]<-c10[k]/(c01[k]+c10[k])
        
      } else {
        sol.L0[k]<-root.L0
        sol.L1[k]<-root.L1
      }   
    }
    
  }else if(method=="simultaneous"|method==2){
    
    joint_boundary<-function(thresholds) {  
      L0<-as.vector(rep(c(NA),m))
      L1<-as.vector(rep(c(NA),m))  
      L<- thresholds[2*m+1]
      detail<-FALSE
      for(j in 1:m){										
        L0[j]<-thresholds[j]											
        L1[j]<-thresholds[j+m]
      }  
      return(evaluation(c(L0,L),c(L1,L),detail=FALSE)$EC)
    }
    lim<-c10[1:m]/(c01[1:m]+c10[1:m]) 
    # If 'int' is default, use the following initial values 
    if(missing(int)||is.null(int)){
      int0<-cn0[1:m]/(c01[1:m]-cn1[1:m]+cn0[1:m])
      int1<-1-cn1[1:m]/(c10[1:m]-cn0[1:m]+cn1[1:m])
      int<-c(int0,int1,c10[K]/(c01[K]+c10[K]))
    }    

    a<-m+1
    b<-2*m+1
    result<-optim(int, joint_boundary, method = "L-BFGS-B",
                  lower=c(llim[1:m],lim,llim[m]),upper=c(lim,ulim[a:b],ulim[m]))

    sol.L0=c(result$par[1:m],result$par[b])
    sol.L1=result$par[a:b]
    
  }else if(method=="tsprt3"|method==3){
    
    Fixed_boundary<-function(thresholds) {  
      L0<-as.vector(rep(c(NA),m))
      L1<-as.vector(rep(c(NA),m))  
      
      L0[1:m]<-thresholds[1]    									
      L1[1:m]<-thresholds[2]
      L<-thresholds[3]
      return(evaluation(c(L0,L),c(L1,L),detail=FALSE)$EC)
    }
    if(missing(int)||is.null(int)){
      int<-c(cn0[m]/c01[K],1-cn1[m]/c10[K],c10[K]/(c01[K]+c10[K]))
    }       
    lim<-c10[K]/(c01[K]+c10[K])
    
    if(int[1]<=llim[m]||int[1]>=ulim[m]){
      int[1]<-llim[m]+0.1*(ulim[m]-llim[m])
      lim<-0.5*(ulim[m]+llim[m])}
    if(int[2]<=llim[m]||int[2]>=ulim[m]){
      int[2]<-ulim[m]-0.1*(ulim[m]-llim[m])
      lim<-0.5*(ulim[m]+llim[m])}
    
    result<-optim(int,Fixed_boundary, method = "L-BFGS-B",lower=c(llim[m],lim),upper=c(lim,ulim[m]))
    sol.L0=c(rep(result$par[1],m),result$par[3])
    sol.L1=c(rep(result$par[2],m),result$par[3])
    
  }
  if (method=="single"|method==4){
    L<-c10[K]/(c01[K]+c10[K])
    rL<-t(m1-m0)%*%solve(cov)%*%(m1+m0)/2+log(pi0/pi1)+ log(L/(1-L))      									
    sol.L0<-c(rep(0,m),L)
    sol.L1<-c(rep(1,m),L)
    Cost<-c10[K]*(1-pnorm(rL, mean=s_m0[K], sd=s_cov[K,K]^.5))*pi0+    										
      c01[K]*pnorm(rL, mean=s_m1[K], sd=s_cov[K,K]^.5)*pi1+sum(cn0[1:m])*pi0+sum(cn1[1:m])*pi1
    error10<-(1-pnorm(rL, mean=s_m0[K], sd=s_cov[K,K]^.5))
    error01<-pnorm(rL, mean=s_m1[K], sd=s_cov[K,K]^.5)
    if(detail==FALSE){
      list(L0=sol.L0,L1=sol.L1,EC=Cost[1,1],stoptime=K,error10=error10[1,1],error01=error01[1,1])
    }else{     
      list(L0=sol.L0,L1=sol.L1,EC=Cost[1,1],stoptime=K,error10=c(rep(0,m),error10[1,1]),error01=c(rep(0,m),error01[1,1]),stoprate=c(rep(0,m),1))
    }
  }else{  
    ev<-evaluation(sol.L0,sol.L1,detail)   
    if(detail==FALSE){
      list(L0=sol.L0,L1=sol.L1,EC=ev$EC,EN=ev$stoptime,error10=ev$error10,error01=ev$error01)
    }else{     
      list(L0=sol.L0,L1=sol.L1,EC=ev$EC,EN=1-ev$stoprate,error10=ev$error10,error01=ev$error01)
    }
    
  }  
}

#Heterogeneous Multivariate Normal Case

utsprt<-function(m0,m1,cov0,cov1,c10,c01,cn0,cn1,pi1,method, detail,int,nsim){
  
  m0<-as.vector(m0)
  m1<-as.vector(m1)
  cov<-as.matrix(cov)
  K<-length(m0)
  m<-K-1
  ## Default input setting
  if(missing(pi1)||is.null(pi1)) {pi1<-0.5}
  pi0=1-pi1
  if(missing(method)||is.null(method)) {method<-1}
  if(missing(detail)||is.null(detail)) {detail<-FALSE}
  if(missing(nsim)||is.null(nsim)) {nsim<-5000}
  
  eval<-function(L0,L1,detail){    
    errorrate10<-as.vector(rep(0,K))
    errorrate01<-as.vector(rep(0,K)) 
    stoprate0<-as.vector(rep(0,K))
    stoprate1<-as.vector(rep(0,K)) 
    stoprate<-as.vector(rep(0,K))
    stoptime<-as.vector(rep(0,K))
    Cost<-as.vector(rep(0,K))
    
    p0<-ratio(L0,L1,0)
    p1<-ratio(L0,L1,1)
    
    for(j in 1:K){
      if(j==K){
        Cost[j]<-c10[j]*p0$pr1[j]*pi0+c01[j]*p0$pr1[j]*pi1                
      }else{
        Cost[j]<-c10[j]*p0$pr1[j]*pi0+cn0[j]*p0$prN[j]*pi0+
          c01[j]*p1$pr0[j]*pi1+cn1[j]*p1$prN[j]*pi1   
      }
      if(j==1){
        stoprate0[j]<-1-p0$prN[j]
        stoprate1[j]<-1-p1$prN[j]
      }else{
        stoprate0[j]<-p0$prN[j-1]-p0$prN[j]
        stoprate1[j]<-p1$prN[j-1]-p1$prN[j]
      }
      stoprate[j]<-stoprate0[j]*pi0+stoprate1[j]*pi1
      stoptime[j]<-j*stoprate0[j]*pi0+j*stoprate1[j]*pi1
      errorrate10[j]<-p0$pr1[j]            
      errorrate01[j]<-p1$pr0[j]
    }
    if(detail==FALSE){
      list(EC=sum(Cost),stoptime=sum(stoptime),error10=sum(errorrate10),error01=sum(errorrate01))
    }else{
      list(EC=Cost,stoprate=stoprate,stoptime=sum(stoptime),error10=errorrate10,error01=errorrate01)
    }  
  }
  
  ratio<-function (L0,L1,group){
    if(group==0){
      mm=m0
      cov=cov0
    }else{
      mm=m1
      cov=cov1
    }
    class<-NULL
    
    for(k in 1:K){
      pr0<-rep(0,K)
      pr1<-rep(0,K)
      prN<-rep(0,K)      
      for(j in 1:nsim){
        x<-rmnorm(1, mean=mm[1:K], varcov=cov[1:K,1:K])
        i<-1
        obs<-x[1:i]
        px<-(dmnorm(obs,m0[1:i],cov0[1:i,1:i])*pi0+dmnorm(obs,m1[1:i],cov1[1:i,1:i])*pi1)
        pos<-dmnorm(obs,m1[1:i],cov1[1:i,1:i])*pi1/px 
        ifelse(is.numeric(px),px,0)
        if(pos<=L0[i]){class<-0
        }else{
          if(pos>L0[i] && pos<L1[i]){class<-"N"}
          else class<-1}  
        
        while(i<K && class=="N"){
          i<-i+1
          obs<-x[1:i]
          px<-dmnorm(obs,m0[1:i],cov0[1:i,1:i])*pi0+dmnorm(obs,m1[1:i],cov1[1:i,1:i])*pi1
          pos<-dmnorm(obs,m1[1:i],cov1[1:i,1:i])*pi1/px 
          ifelse(is.numeric(px),px,0)
          if(pos<=L0[i]){class<-0
          }else{
            if(pos>L0[i] && pos<L1[i]){class<-"N"}
            else class<-1}  
        }
        stage<-i
        pr0[i]<-pr0[i]+ifelse(pos<=L0[i],1,0)
        pr1[i]<-pr1[i]+ifelse(pos>=L1[i],1,0)
        if(i==1){prN[i]<-prN[i]} else{
          prN[1:i-1]<-prN[1:i-1]+rep(1,length=i-1)
        }
      }
    }
    list(pr0=pr0/nsim,pr1=pr1/nsim,prN=prN/nsim) 
  } 
  
  lim<-c10[K]/(c01[K]+c10[K])
  llim<-as.vector(rep(c(1e-06),2*m))
  ulim<-as.vector(rep(c(1-1e-06),2*m))
  
  sol.L0<-as.vector(rep(NA,K))
  sol.L1<-as.vector(rep(NA,K)) 
  m<-K-1
  
  if(method=="tsprt"|method==1){
    lim<-c10[1:m]/(c01[1:m]+c10[1:m]) 
    if(missing(int)||is.null(int)){
      int0<-cn0[1:m]/(c01[1:m]-cn1[1:m]+cn0[1:m])
      int1<-1-cn0[1:m]/(c10[1:m]-cn0[1:m]+cn1[1:m])
      int<-c(int0,int1)
    }    
    
    sprt_boundary<-function(thresholds) { 
      a<-m+1
      b<-2*m
      l0<-thresholds[1:m]
      l1<-thresholds[a:b]
      L<-c10[K]/(c01[K]+c10[K])
      return(eval(c(l0,L),c(l1,L),detail=FALSE)$EC)
    } 
    
    result<-optim(int, sprt_boundary, method = "L-BFGS-B",
                  lower=c(llim,lim),upper=c(lim,ulim))
    a<-m+1
    b<-2*m
    L<-c10[K]/(c01[K]+c10[K])
    sol.L0=c(result$par[1:m],L)
    sol.L1=c(result$par[a:b],L)
  }
  else if(method=="tsprt3"|method==2){  
    sprt3_boundary<-function(thresholds) {  
      L0<-as.vector(rep(c(NA),m))
      L1<-as.vector(rep(c(NA),m))  
      
      L0[1:m]<-rep(thresholds[1],m)       
      L1[1:m]<-rep(thresholds[2],m)
      L<-c10[K]/(c01[K]+c10[K])
      return(eval(c(L0,L),c(L1,L),detail=FALSE)$EC)
    }
    
    if(missing(int)||is.null(int)){
      int<-c(cn0[K]/c01[K],1-cn1[K]/c10[K])
    }       
    
    result<-optim(int,sprt3_boundary, method = "L-BFGS-B",lower=c(llim[m],lim),upper=c(lim,ulim[m]))
    L<-c10[K]/(c01[K]+c10[K])
    sol.L0=c(rep(result$par[1],m),L)
    sol.L1=c(rep(result$par[2],m),L)   
  }else if(method=="single"|method==3){
    sol.L0[1:m]<-rep(0,m)
    sol.L1[1:m]<-rep(1,m)
    sol.L0[K]<-c10[K]/(c01[K]+c10[K])
    sol.L1[K]<-c10[K]/(c01[K]+c10[K])      
  }
  
  if(method<=2){
    ev<-eval(sol.L0,sol.L1,detail)
    list(L0=sol.L0,L1=sol.L1,EC=ev$EC,EN=ev$stoptime,p10=ev$error10,p01=ev$error01,counts=result$counts,message=result$message)  
  }else{
    ev<-eval(sol.L0,sol.L1,detail)
    list(L0=sol.L0,L1=sol.L1,EC=ev$EC,EN=ev$stoptime,p10=ev$error10,p01=ev$error01)  
  }
}


