/*
 * This code implements the classical and the damped COS method and is based on the paper
 * Junike, Gero, and Hauke Stier. "From characteristic functions to multivariate distribution functions and European option prices by the damped COS method." arXiv preprint arXiv:2307.12843 (2025). https://arxiv.org/pdf/2307.12843
 * 
 * The code is written in C++ and can be called from R via the package Rcpp. Examle: To price the basket option 
 * max(K - (S_1(T)+S_1(T)), 0) 
 * on two underlyings S_1 and S_2 and strike K under the Black-Scholes or the Variance Gamma model, 
 * or, a digital put option with payoff 
 * 1_{S_1(T)<K_1} * 1_{S_2(T)<K_2}
 * do the following in R:
 * 
  library("Rcpp")
  sourceCpp('cos.cpp')

  #Price of arithmetic basket put or digital put options in BS model by COS method and Monte Carlo
  d=2
  Ks=rep(100*d,d)
  mat=0.5
  r=0.1
  S0=rep(100,d)
  Ns=rep(100,d)
  Sigma=diag(d)
  Sigma[1,1]=0.2^2
  Sigma[2,2]=0.4^2
  Sigma[1,2]=0.5*sqrt(Sigma[1,1]*Sigma[2,2])
  Sigma[2,1]=Sigma[1,2];
  Ls=c(3.9, 7.9)
  U = 1000000
  A = chol(Sigma)
  pricing_by_COS_cpp(Ks, Ls, mat, r, S0, Ns,alpha=rep(-7,d), Sigma,model=0,payoff = 1) #10.10347, basket option by COS
  put_MC_cpp_BS(Ks,mat, S0, r, U, Sigma, A, payoff=1) #10.10, basket option by MC
  pricing_by_COS_cpp(Ks, Ls, mat, r, S0, Ns,alpha=rep(0,d), Sigma,model=0,payoff = 0) #0.9437506, digital option by COS
  put_MC_cpp_BS(Ks,mat, S0, r, U, Sigma, A, payoff=0) #0.94, digital option by MC
  
  
  
  
  #Price of arithmetic basket put or digital put options in VG model by COS method and Monte Carlo
  d=2
  Ks=rep(50*d,d)
  mat=0.5
  r=0.1
  S0=rep(50,d)
  Ns=rep(100,d)
  sigma=rep(0.2,d)
  nu=0.1
  theta=rep(-0.03,d)
  Ls=c(3, 3)
  U = 1000000
  pricing_by_COS_cpp(Ks, Ls, mat, r, S0, Ns, alpha=rep(-4,d), diag(sigma^2),theta, nu,model=3,payoff = 1) #1.885268, basket option by COS
  put_MC_cpp_VG(Ks,mat,S0,r, U, sigma, theta, nu, payoff=1)  #1.88, basket option by MC
  pricing_by_COS_cpp(Ks/d, Ls, mat, r, S0, Ns, alpha=rep(0,d), diag(sigma^2),theta, nu,model=3,payoff = 0) #0.1368683, digital option by COS
  put_MC_cpp_VG(Ks/d,mat,S0,r, U, sigma, theta, nu, payoff=0)  #0.1371093, digital option by MC
  

  
 */

#include <Rcpp.h>
#include <random>
#include <Rmath.h>
#include <cmath>
#include <chrono>
#include <thread>

using namespace Rcpp;
using namespace std::complex_literals;
const double pi=3.141592653589793115997963468544185161590576171875;

//gamma function with complex arguments, see https://en.wikipedia.org/wiki/Lanczos_approximation
// [[Rcpp::export]]
std::complex<double> gamma_complex(std::complex<double> z){
  double g = 7.0;
  NumericVector p=(9);
  p(0)= 0.99999999999980993;
  p(1)=    676.5203681218851;
  p(2)= -1259.1392167224028;
  p(3)= 771.32342877765313;
  p(4)= -176.61502916214059;
  p(5)=    12.507343278686905;
  p(6)=    -0.13857109526572012;
  p(7)=    9.9843695780195716e-6;
  p(8)=    1.5056327351493116e-7;
  std::complex<double> y = 0.0;
  if(z.real() < 0.5){
      y = pi / (sin(pi * z) * gamma_complex(1.0 - z));  // Reflection formula
  }
  else{
        z = z - 1.0;
        std::complex<double> x = p(0);
        for(int i=1;i<9;i++)
            x = x + p(i) / (z + (double)i);
        std::complex<double> t = z + g + 0.5;
        y = pow(2 * pi,0.5) * std::pow(t,(z + 0.5)) * exp(-t) * x; 
  }
  return y;
}

/* payoff==0 corresponds to a digital cash-or-nothing put option.
 * payoff==1 corresponds to a basket put option
*/
double get_vk(double (&u)[], std::complex<double> &expipi, int d, int (&ks)[], double (&myLs)[], double (&myMs)[], double (&myKs)[], double (&mus)[],double lambda, int payoff, double (&myalpha)[], bool alphaIsZero){
  //classical COS method
  double vk=0.0;
  if(alphaIsZero){ //classical COS method
    if(payoff==0){ //Example 5.1 
          double tmp=1.0;
          for(int h=0;h<d;h++){
            double gamma=log(myKs[h])-mus[h];
            if(gamma>myMs[h])
              gamma=myMs[h];
            if(gamma < -myMs[h])
              return 0.0;
            if(ks[h]>0)
              tmp=tmp*2.0*myLs[h]/(ks[h]*pi)*(sin(ks[h]*pi*(gamma+myLs[h])
                        /(2.0*myLs[h]))-sin(ks[h]*pi*(-myMs[h]+myLs[h])/(2.0*myLs[h])));
            else
              tmp=tmp*(gamma+myMs[h]);
          }
          vk=tmp/lambda;
    }
  }
  else{ //damped COS method
    std::complex<double> v_hat=0.0;
    //get payoff coefficients and vk
    //damped COS method
    std::complex<double> w_hat=1.0; //w_hat is w_hat(u+1i*alpha)
    double u_mus =0.0;
    for(int i=0;i<d;i++)
      u_mus=u_mus+u[i]*mus[i];

    if(payoff==0){ //digital put, Example 5.2
      for(int i=0;i<d;i++)
        w_hat=w_hat*std::pow(myKs[i],1i*(u[i]+1i*myalpha[i]))/(1i*(u[i]+1i*myalpha[i]));
    }
    else if(payoff==1){ //basket, Examples 5.3
      std::complex<double> sum_z=0.0;
      for(int h=0;h<d;h++){
        sum_z=sum_z+u[h]+1i*myalpha[h];
        w_hat=w_hat*gamma_complex(1i*(u[h]+1i*myalpha[h]));
      }
      w_hat=w_hat*std::pow(myKs[0],1.0+1i*sum_z)/(gamma_complex(1i*sum_z+2.0)+1e-15);
    }
    else
      w_hat =0.0;
    v_hat = 1.0/lambda*exp(-1i*u_mus)*w_hat;
    vk=(v_hat*expipi).real(); 
  }
  return vk;
}

/* model==0 corresponds to the BS model
 * model==3 coreesponds to the VG model
 * 
 * This code implements the characteristic Function of the BS and the VG model and returns 
  $\Re\left\{ \widehat{f}\left(\frac{\pi}{2}\frac{\boldsymbol{sk}}{\boldsymbol{L}}\right)\exp\left(i\frac{\pi}{2}\boldsymbol{s}\cdot\boldsymbol{k}\right)\right\} $
 */
double get_ck(double (&u)[], std::complex<double> &expipi, double u_Sigma_u, int d, double (&mus)[], int model,double mat,double (&mySigmaDiag)[],double (&mytheta)[], double nu, double (&myalpha)[]){
  std::complex<double> CF=0.0;
  if(model==0) //Normal distribution
    CF=exp( -0.5*mat*u_Sigma_u ); 
  if(model==3){ //VG distribution
    double thetaSigmaAlphaU=0.0;
    double zeta=1.0;
    for(int i=0;i<d;i++){
      thetaSigmaAlphaU = thetaSigmaAlphaU + (mytheta[i]+mySigmaDiag[i]*myalpha[i])*u[i];
      zeta=zeta-nu*mytheta[i]*myalpha[i]-0.5*nu*myalpha[i]*myalpha[i]*mySigmaDiag[i];
    }
    CF = exp(-1i*mat/zeta*thetaSigmaAlphaU)*
      std::pow(1.0-1i*nu/zeta*thetaSigmaAlphaU+0.5*nu/zeta*u_Sigma_u,-mat/nu);
  }
  return((CF*expipi).real());
}

//
// [[Rcpp::export]]
double pricing_by_COS_cpp(
  NumericVector Ks, //strikes of the payoff
  NumericVector Ls, //truncation range for damped density
  double mat, //maturity of payoff
  double r, //interest rates
  NumericVector S0, //stock prices today
  IntegerVector Ns, //number of terms
  NumericVector alpha, //damping factor. Choose alpha such that the damped payoff function v and the damped density f are integrable.
  NumericMatrix Sigma,  //In BS model is Sigma covariation matrix. In VG model is Sigma diagonal matrix (sigma_1^2,...,sigma_d^2. Sigma must be symmetric.
  NumericVector theta = 0.0, //additional parameters of the VG model. Default= (0.0,...,0.0)
  double nu =1.0, //additional parameters of the VG mode, Default: 1.0.
  int model = 0, //identifier of the model: model 0,3 corresponds to BS, VG 
  int payoff = 0, //payoff 0 is cash-or-nothing put, payoff 1 is basket put
  NumericVector Ms = 0.0 //default: Ms=Ls. Ms is only used if alpha=(0.0,...,0.0)
  
){
    int d=Ls.length();
    bool symmetric = false; //if the characteristic function of the shifted and damped density is real, set symmetric to true, to speed up the COS method by the factor two
    
    //use array instead of vectors for performance. The are allocated on stack, which is much faster.
    double myLs[d];
    double myMs[d];
    double myKs[d];
    double mytheta[d];
    double myalpha[d];
    double mySigmaDiag[d];
    double mySigma[d][d];

    for(int i=0;i<d;i++){
      myLs[i]=Ls(i);
      myKs[i]=Ks(i);
      if(i<theta.length() && theta.length()==d){
        mytheta[i]=theta(i);
      }
      else
        mytheta[i]=0.0;
      if(i<Ms.length() && Ms(i)>0)
        myMs[i]=Ms(i);
      else
        myMs[i]=myLs[i];
      mySigmaDiag[i]=Sigma(i,i);
      myalpha[i]=alpha[i];
    }
    
    bool alphaIsZero=true;
    for(int i=0;i<d;i++)
      if(abs(alpha(i))>0.000000000001 )
        alphaIsZero=false;
    for(int i=0;i<d;i++){
      for(int j=0;j<d;j++){
        mySigma[i][j]=Sigma(i,j);
      }
    }
    //Set lambda, mus and eta, See Junike & Stier (2024, Section 4).
    double eta[d];
    double mus[d];
    double lambda=1.0;
    double alpha_mySigma_alpha=0.0;
    for(int i=0;i<d;i++)
      for(int j=0;j<d;j++)
        alpha_mySigma_alpha=alpha_mySigma_alpha+mySigma[i][j]*myalpha[i]*myalpha[j]; //sum(alpha*Sigma%*%alpha)
    double mySigma_myalpha[d];
    for(int i=0;i<d;i++)
      mySigma_myalpha[i]=0.0;
    for(int i=0;i<d;i++)
      for(int h=0;h<d;h++)
          mySigma_myalpha[i]=mySigma_myalpha[i]+mySigma[i][h]*myalpha[h]; //Simga%*%alpha
    if(model==0){ //BS
      for(int i=0;i<d;i++)
        eta[i]=log(S0(i))+(r-0.5*mySigmaDiag[i])*mat;
      double eta_myalpha=0.0;
      for(int i=0;i<d;i++)
        eta_myalpha=eta_myalpha+eta[i]*myalpha[i]; //sum(eta*alpha)
      lambda=exp(-eta_myalpha-mat/2.0*alpha_mySigma_alpha);
      for(int i=0;i<d;i++){
        mus[i]=eta[i]+mat*mySigma_myalpha[i];
      } 
      symmetric = true; 
    }
    if(model==3){ //VG
      for(int i=0;i<d;i++)
        eta[i]=log(S0(i))+(r+1.0/nu*log(1.0-0.5*mySigmaDiag[i]*nu-mytheta[i]*nu))*mat;
      double zeta = 0.0;
      for(int i=0;i<d;i++)
        zeta=zeta+mytheta[i]*myalpha[i]; //sum(theta*alpha)
      zeta=1.0-nu*zeta-0.5*nu*alpha_mySigma_alpha;
      if(zeta <= 0.0){
        Rcerr << "Error message: Damping factor alpha is not admissible.\n";
        return std::numeric_limits<double>::quiet_NaN();
      }
      double eta_myalpha=0.0;
      for(int i=0;i<d;i++)
        eta_myalpha=eta_myalpha+eta[i]*myalpha[i]; //sum(eta*alpha)
      lambda=exp(-eta_myalpha)*pow(zeta,mat/nu);
      for(int i=0;i<d;i++)
        mus[i]=eta[i]+mat/zeta*(mytheta[i]+mySigma_myalpha[i]);
      symmetric = false;

    }
    //Compute COS method for various dimensions.
    double res=0.0;
    int inkrementer=2;
    double s[d];
    s[0]=1.0;
    double u[d];
    int ks[d];
    std::complex<double> expipi=0.0;
    std::complex<double> CF=0.0;
    std::complex<double> v_hat=0.0;
    /*
     * compute sum over 0<=k1<=N1,...,0<=k2<=N2 over ck*vk. The Factors 1/2^(d-1) for vk_tilde if alpha!=0 and 
     * the factor 1/(2^(d-1)*prod(Ls)) for ck are handled at the return statement at the end of the function.
     * 
     * To get ck, compute sum over s \in {1,\pm 1,...,\pm 1}
     * If alpha!=0: get vk, by computing the sum over s \in {1,\pm 1,...,\pm 1}
     * if alpha==0 (and payoff==0): get vk directly.
     */
    if(d==2){
      // These loops compute several nested sums
      for(int k1=0;k1<=Ns(0);k1++){
        for(int k2=0;k2<=Ns(1);k2++){
          ks[0]=k1;
          ks[1]=k2;
          if(!symmetric || (k1+k2)%2==0){
              double ck =0.0;
              double vk=0.0;
              if(alphaIsZero)
                vk=get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);
              //For-loop computes $\sum_{\boldsymbol{s}=(1,\pm1,...,\pm1)\in\mathbb{R}^{d}}$
              for(int s2=-1;s2<=1;s2+=inkrementer){
                s[1]=(double)s2;
                for(int h=0;h<d;h++)
                  u[h]=s[h]*(double)ks[h]/myLs[h]*pi/2.0;
                double sk =0.0;
                for(int h=0;h<d;h++)
                    sk=sk+s[h]*(double)ks[h];
                expipi=exp(1i*pi/2.0*sk);
                double u_Sigma_u=0.0; //u%*%Sigma%*%u
                for(int i=0; i<d;i++){
                    for(int j=0; j<d;j++)
                        u_Sigma_u=u_Sigma_u+mySigma[i][j]*u[i]*u[j];
                }
                ck=ck+get_ck(u, expipi, u_Sigma_u, d, mus, model,mat,mySigmaDiag,mytheta, nu, myalpha); 
                if(!alphaIsZero)
                  vk=vk+get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);
              }
              double factor=1.0;
              for(int h=0;h<d;h++){
                if(ks[h]==0)
                  factor=factor*0.5;
              }
              res=res+ck*vk*factor;
          }
        }
      }
    }
    if(d==3){
      for(int k1=0;k1<=Ns(0);k1++){
        for(int k2=0;k2<=Ns(1);k2++){
            for(int k3=0;k3<=Ns(2);k3++){
              ks[0]=k1;
              ks[1]=k2;
              ks[2]=k3;
              if(!symmetric || (k1+k2+k3)%2==0){
                double ck =0.0;
                double vk=0.0;
                if(alphaIsZero)
                  vk=get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);

                for(int s2=-1;s2<=1;s2+=inkrementer){
                  for(int s3=-1;s3<=1;s3+=inkrementer){
                    s[1]=(double)s2;
                    s[2]=(double)s3;
                    for(int h=0;h<d;h++)
                      u[h]=s[h]*(double)ks[h]/myLs[h]*pi/2.0;
                    double sk =0.0;
                    for(int h=0;h<d;h++)
                        sk=sk+s[h]*(double)ks[h];
                    expipi=exp(1i*pi/2.0*sk);
                    double u_Sigma_u=0.0; //u%*%Sigma%*%u
                    for(int i=0; i<d;i++){
                        for(int j=0; j<d;j++)
                            u_Sigma_u=u_Sigma_u+mySigma[i][j]*u[i]*u[j];
                    }
                    ck=ck+get_ck(u, expipi, u_Sigma_u, d, mus, model,mat,mySigmaDiag,mytheta, nu, myalpha); 
                    if(!alphaIsZero)
                      vk=vk+get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);
                  }
                }
                double factor=1.0;
                for(int h=0;h<d;h++){
                  if(ks[h]==0)
                    factor=factor*0.5;
                }
                res=res+ck*vk*factor;
              }
            }
        }
      }
    }
    if(d==4){
      for(int k1=0;k1<=Ns(0);k1++){
        for(int k2=0;k2<=Ns(1);k2++){
            for(int k3=0;k3<=Ns(2);k3++){
                for(int k4=0;k4<=Ns(3);k4++){
                  ks[0]=k1;
                  ks[1]=k2;
                  ks[2]=k3;
                  ks[3]=k4;
                  
                  if(!symmetric || (k1+k2+k3+k4)%2==0){
                    double ck =0.0;
                    double vk=0.0;
                    if(alphaIsZero)
                      vk=get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);

                      for(int s2=-1;s2<=1;s2+=inkrementer){
                        for(int s3=-1;s3<=1;s3+=inkrementer){
                          for(int s4=-1;s4<=1;s4+=inkrementer){
                            s[1]=(double)s2;
                            s[2]=(double)s3;
                            s[3]=(double)s4;
                            for(int h=0;h<d;h++)
                              u[h]=s[h]*(double)ks[h]/myLs[h]*pi/2.0;
                            double sk =0.0;
                            for(int h=0;h<d;h++)
                                sk=sk+s[h]*(double)ks[h];
                            expipi=exp(1i*pi/2.0*sk);
                            double u_Sigma_u=0.0; //u%*%Sigma%*%u
                            for(int i=0; i<d;i++){
                                for(int j=0; j<d;j++)
                                    u_Sigma_u=u_Sigma_u+mySigma[i][j]*u[i]*u[j];
                            }
                            ck=ck+get_ck(u, expipi, u_Sigma_u, d, mus, model,mat,mySigmaDiag,mytheta, nu, myalpha);
                            if(!alphaIsZero)
                              vk=vk+get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);
                          }
                        }
                      }
                      double factor=1.0;
                      for(int h=0;h<d;h++){
                        if(ks[h]==0)
                          factor=factor*0.5;
                      }
                      res=res+ck*vk*factor;
                  }
                }
            }
        }
      }
    }
    if(d==5){
      for(int k1=0;k1<=Ns(0);k1++){
        for(int k2=0;k2<=Ns(1);k2++){
            for(int k3=0;k3<=Ns(2);k3++){
                for(int k4=0;k4<=Ns(3);k4++){
                    for(int k5=0;k5<=Ns(4);k5++){
                      ks[0]=k1;
                      ks[1]=k2;
                      ks[2]=k3;
                      ks[3]=k4;
                      ks[4]=k5;
                      
                      if(!symmetric || (k1+k2+k3+k4+k5)%2==0){
                        double ck =0.0;
                        double vk=0.0;
                        if(alphaIsZero)
                          vk=get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);

                          for(int s2=-1;s2<=1;s2+=inkrementer){
                            for(int s3=-1;s3<=1;s3+=inkrementer){
                              for(int s4=-1;s4<=1;s4+=inkrementer){
                                for(int s5=-1;s5<=1;s5+=inkrementer){
                                    s[1]=(double)s2;
                                    s[2]=(double)s3;
                                    s[3]=(double)s4;
                                    s[4]=(double)s5;
                                    for(int h=0;h<d;h++)
                                      u[h]=s[h]*(double)ks[h]/myLs[h]*pi/2.0;
                                    double sk =0.0;
                                    for(int h=0;h<d;h++)
                                        sk=sk+s[h]*(double)ks[h];
                                    expipi=exp(1i*pi/2.0*sk);
                                    double u_Sigma_u=0.0; //u%*%Sigma%*%u
                                    for(int i=0; i<d;i++){
                                        for(int j=0; j<d;j++)
                                            u_Sigma_u=u_Sigma_u+mySigma[i][j]*u[i]*u[j];
                                    }
                                    ck=ck+get_ck(u, expipi, u_Sigma_u, d, mus, model,mat,mySigmaDiag,mytheta, nu, myalpha);       
                                    if(!alphaIsZero)  
                                      vk=vk+get_vk(u, expipi, d, ks, myLs,myMs, myKs, mus,lambda, payoff, myalpha,alphaIsZero);
                                  } 
                                }
                              }
                            }
                            double factor=1.0;
                            for(int h=0;h<d;h++){
                              if(ks[h]==0)
                                factor=factor*0.5;
                            }
                            res=res+ck*vk*factor;
                        }
                      }
                    }
                }
            }
        }
    }
    //return the price of the option
    double prodLs=1.0;
    for(int i=0;i<d;i++)
      prodLs=prodLs*myLs[i];
    if(alphaIsZero)
      return res/(pow(2.0,(d-1))*prodLs)*exp(-r*mat);
    else
      return res/(pow(2.0,2*(d-1))*prodLs)*exp(-r*mat);
}



//price of digital put option and basket option by Monte Carlo Simulation for BS
// [[Rcpp::export]]
/* One could replace the NumericVector by a C-array. However, there is only a little speed gain.
*/
double put_MC_cpp_BS(NumericVector Ks, //strikes of the payoff
                     double mat, //maturity of the payoff
                     NumericVector S0, //stock price today
                     double r, //intterest rates
                     unsigned long long int U, //number of runs
                     NumericMatrix Sigma, //Sigma covariation matrix
                     NumericMatrix A, //A=chol(Sigma), i.e., Cholesky decomposition of Sigma
                     int payoff=0) //payoff 0 is cash-or-nothing put, payoff 1 is basket put
{
  std::random_device rd{};
  std::mt19937 gen{rd()};
  std::normal_distribution<double> nd(0.0,1.0);
  
  int d=Ks.length();
  NumericVector res=(d);
  NumericVector Z =(d);
  NumericVector X=(d); //=log(ST)
  NumericVector eta=(d);
  for(int h=0;h<d;h++){
    eta(h)=log(S0(h))+(r-0.5*Sigma(h,h))*mat; 
  }
  double z=0;
  for(unsigned long long int u=0;u<U;u++){
    for(int h=0;h<d;h++){
      Z(h)=nd(gen);
    }
    //X=add(eta,matvec(A,Z)*sqrt(mat)); //A =chol(Sigma).
    for(int i=0;i<d;i++){
      X(i)=eta(i);
      for(int j=0;j<d;j++){
        X(i)=X(i)+A(j,i)*Z(j)*sqrt(mat); //X=eta+A%*%Z *sqrt(mat) 
      }
    }
    
    if(payoff==0){
      double Y=1.0;
      for(int h=0;h<d;h++){
        if(X(h)>log(Ks(h))){
          Y=0.0;
          break;
        }
      }
      z=z+Y;
    }
    if(payoff==1){
      double Y=0.0;
      for(int h=0;h<d;h++)
          Y=Y+exp(X(h));
      if(Y<Ks(0))
        z=z+Ks(0)-Y;
    }
  }
  return( z*exp(-r*mat)/((double)U) ); 
}


//price of digital put option and basket option by Monte Carlo Simulation for VG
// [[Rcpp::export]]
double put_MC_cpp_VG(NumericVector Ks, //strikes of the payoff
                     double mat, //maturity of the payoff
                     NumericVector S0, //stock price today
                     double r, //intterest rates
                     unsigned long long int U, //number of runs
                     NumericVector sigma, //parameters of the VG model.
                     NumericVector theta, //additional parameters of the VG model.
                     double nu, //additional parameters of the VG mode
                     int payoff=0) //payoff 0 is cash-or-nothing put, payoff 1 is basket put
{
  std::random_device rd{};
  std::mt19937 gen{rd()};
  std::this_thread::sleep_for(std::chrono::milliseconds(1));
  std::mt19937 gen2{rd()};
  std::normal_distribution<double> mygauss(0.0,1.0);
  std::gamma_distribution<> mygamma(mat/nu, nu);
  
  int d=Ks.length();
  NumericVector res=(d);
  NumericVector W=(d);
  NumericVector X=(d); //=log(ST)
  NumericVector eta=(d);
  NumericVector logS0=(d);
  for(int h=0;h<d;h++){
    eta(h)=1/nu*log(1.0-0.5*sigma(h)*sigma(h)*nu-theta(h)*nu); 
    logS0(h)=log(S0(h));
  }
  double z=0;
  for(unsigned long long int u=0;u<U;u++){
    for(int h=0;h<d;h++){
      W(h)=mygauss(gen);
    }
    double G=mygamma(gen2);
    for(int h=0;h<d;h++){
      X(h)=logS0(h)+(r+eta(h))*mat+theta(h)*G+sigma(h)*sqrt(G)*W(h);
    }
    
    if(payoff==0){
      double Y=1.0;
      for(int h=0;h<d;h++){
        if(X(h)>log(Ks(h))){
          Y=0.0;
          break;
        }
      }
      z=z+Y;
    }
    if(payoff==1){
      double Y=0.0;
      for(int h=0;h<d;h++)
          Y=Y+exp(X(h));
      if(Y<Ks(0))
        z=z+Ks(0)-Y;
    }
  }
  return( z*exp(-r*mat)/((double)U) ); 
}
 

