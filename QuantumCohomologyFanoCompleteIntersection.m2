-- -*- coding: utf-8 -*-
newPackage(
  "QuantumCohomologyFanoCompleteIntersection",
      Version => "1.0", 
      Date => "June 20, 2021",
      Authors => {{Name => "Xiaowen Hu", 
      Email => "huxw06@gmail.com", 
      HomePage => ""}},
      Headline => "generating function of genus 0 ambient Gromov-Witten invariants of Fano complete intersections in P^n",
      DebuggingMode => false
      )

export {"functionMu","fanoIndex","indexSet1","indexSet2","invariantTwoPoints",
"zeroVector","unitVector","matrixCoeffW","matrixW","matrixCoeffM","matrixM",
"EulerVectorFieldCoeff","ambientCorrelatorInTauCoord1","ambientCorrelatorInTauCoord",
"sfb","inversePairingInTauCoord","functionC","ringOfTCoord","ringOfTauCoord","ringOfTCoordAndS","ringOfTauCoordAndS",
"ambientGeneratingFuncInTauCoordOfDegreeB",
"ambientGeneratingFuncOfDegreeUpToB","lowerLists","binomOfLists","minPositiveIndex","ellD",
"constantTermOfF2","correlatorOfSOrderOneInTauCoord","correlatorOfSOrderTwoInTauCoord","correlatorInTauCoord", "correlAfterSqrtRecursionInTauCoord", "dimPrimCoh",
"equationOfConstTerm","equationOfConstTerm2","sqrtRecursion","generatingFuncOfGivenSOrderInTauCoordUpToDegreeBNotCubic","generatingFuncOfGivenSOrderInTCoordUpToDegreeBNotCubic","generatingFuncOfDegreeUpToBNotCubic",
"correlatorCubicHypersurfaceInTauCoord0","correlatorCubicHypersurfaceInTauCoord","generatingFuncOfGivenSOrderInTauCoordUpToDegreeBofCubicHypersurface","generatingFuncOfGivenSOrderInTCoordUpToDegreeBofCubicHypersurface","generatingFuncOfDegreeUpToBofCubicHypersurface",
"generatingFuncOfDegreeUpToB",
"correlatorOddDimIntTwoQuadricsInTauCoord",
"correlatorEvenIntersecTwoQuadricsRecursionInTauCoord","unknownInvInTermsOfSis","coefficientProductOfSisClass"}


l=getSymbol "l";
t=getSymbol "t";
tau=getSymbol "tau";
s=getSymbol "s";
x=getSymbol "x";
y=getSymbol "y";
z=getSymbol "z";





functionA0 =memoize (L ->(                          --definition of the function A
  N:=L#0;
  p:=#(L#1);
  A:=0;
  B:=0;
  C:=1;
  D:=0;
  for i from 0 to p-1 do (
    B=0;
    for j from 1 to p-i do 
      B=B+L#1#(j-1);
    C=1;
    for j from 2 to p-i do (
      D=0;
      for k from j to p-i do 
        D=D+L#1#(k-1);
      C=C*D;
      ); 
    for j from p-i+1 to p do (
      D=0;
      for k from p-i+1 to j do 
        D=D+L#1#(k-1);
      C=C*D;
      );  
  A=A+(-1)^i*B^(N+p-1)/C;
  );
  A
)
)



functionAMod = memoize (L->(               --a quick way to compute the function A
  N:=L#0#0;
  a:=L#0#1;
  p:=#(L#1);
  M:={};
  K:=0;           --the number of zeros in L#1
  S:=0;
  if N==0 then S=1
  else (
    eps:=1/(N*(a-2)^N*a^(N-1)*2^(a-1));
    for i from 0 to p-1 do (
      if L#1#i==0 then (
        K=K+1;
        M=append(M,eps);
        ) 
      else M=append(M,L#1#i); 
      );
    if K==0 then S=functionA0({N,L#1})
    else if K==p then S=0
    else S=floor functionA0({N,M});
  );
  S
)
)


functionMu = memoize (L->(
  d:=L#0;
  k:=L#1;
  A:=0;
  Mu:=0;
  if d<k then Mu=0
  else if  k==0 then Mu=1 
  else if d==1 and k==1 then Mu=1
  else if k>=1 and d>=k then (
    A=0;
    for i from 0 to d-k do 
      A=A+functionMu({d-i-1,k-1})/(d-i);
    Mu=A;
    );
  Mu  
)
)





indexSet1 =memoize(L->(                               --the set of indices in the first summation in invariantTwoPointsFanoIndexAtLeastTwo
  l:=L#0;
  n:=L#1;
  A:={};
  S:={};
  if l==0 then S={}
  else if l==1 then S={{n}}
  else if l>=2 then (
    for i from 0 to n do (
      for j from 0 to #(indexSet1({l-1,n-i}))-1 do (
        A=append(A,append((indexSet1({l-1,n-i}))#j,i));
        );    
    );
    S=A
  );
  S
) 
)




indexSet2 =memoize(L->(                                                 --the set of indices in the second summation in invariantTwoPointsFanoIndexAtLeastTwo
  p:=L#0;
  f:=L#1; --Fano index
  S:={};
  A:={};
  c:=0;
  if p==1 then (
    if f==1 then S={{1,2},{1,1},{1,0}}
    else if f==2 then S={{1,2},{1,0}}
    else if f>=3 then S={{1,2}};
    )
  else if p>=2 then (
    for i from 0 to #(indexSet2({p-1,f}))-1 do (
      c=1+(indexSet2({p-1,f}))#i#(-1);
      for j from 0 to floor(c/f) do 
        A=append(A,append((indexSet2({p-1,f}))#i,c-j*f));
      );
    S=A 
    );
  S 
)
)



invariantTwoPointsFanoIndexAtLeastTwo =memoize(L->(  --
  a:=L#0;           --the first insertion is h_a
  b:=L#1;           --the second insertion is h_a \times \psi^c
  c:=L#2;
  n:=L#3;           --dimension
  d:=L#4;           --multidegree of the target manifold
  r:=#d;
  D:=1;
  for i from 0 to r-1 do 
    D=D*(d#i);        --product of the components of the multidegree
  Inv:=0;           --the value of the GW invariant
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;          --Fano index
  beta:=(a+b+c-n+1)/f;    --degree

  if (not beta==floor(beta)) or beta<=0 then Inv=0
  else if f<2 then print "The Fano index is <2"
  else (
    beta=lift(beta,ZZ);
    B:=1;
    Sum1:=0;

    for i from 1 to r do (
      B=B*(d#(i-1))*(((d#(i-1))*beta)!)
      );
    B=B*beta^a/(beta!)^(n+r+1);
    I:=indexSet1({beta+r,n-b});
    P1:=1;
    for j from 0 to #(I)-1 do (
      P1=binomial(a-n-r-1,I#j#(beta-1))*beta^(-I#j#(beta-1));
      for l from 1 to beta-1 do 
        P1=P1*binomial(-n-r-1,I#j#(l-1))*l^(-I#j#(l-1));
      for i from 1 to r do
        P1=P1*(d#(i-1))^(I#j#(beta+i-1))*functionMu({d#(i-1)*beta,I#j#(beta+i-1)});
      Sum1=Sum1+P1;
      );
    B=B*Sum1;

    Sum2:=0;
    J:={};
    P2:=1;
    M:={};
    FAV:=0;
    for p from 1 to a-1 do (
      J=indexSet2({p,f});
      for k from 0 to #J-1 do if (not J#k#p==a) and (beta>(p+1-J#k#p)/f) then (
        M={};
        for i from 1 to p do 
          M=append(M,(1+J#k#(i-1)-J#k#i)/f);
        FAV=(functionAMod({{a-1-p,a},M}));
        P2=FAV;
        for i from 1 to p do (
          if 1+J#k#(i-1)>J#k#i then 
            P2=P2/D*(1+J#k#(i-1)-J#k#i)/f*invariantTwoPointsFanoIndexAtLeastTwo({J#k#(i-1),n-J#k#i,0,n,d});
          );
        P2=P2*invariantTwoPointsFanoIndexAtLeastTwo({J#k#p,b,a+c-p-1,n,d});
        Sum2=Sum2+P2;
      );  
    );
    Inv=B-Sum2; 
    );
  Inv
)
)



invariantTwoPointsFanoIndexOne =memoize(L->(
  a:=L#0;           --the first insertion is h_a
  b:=L#1;           --the second insertion is h_b \times \psi^c
  c:=L#2;
  n:=L#3;           --dimension
  d:=L#4;           --multidegree of the target manifold
  r:=#d;
  D:=1;
  for i from 0 to r-1 do 
    D=D*(d#i);        --product of the components of the multidegree
  Inv:=0;           --the value of the GW invariant
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;          --Fano index
  beta:=(a+b+c-n+1)/f;    --degree

  if (not beta==floor(beta)) or beta<=0 then Inv=0
  else if f>=2 then print "The Fano index is >=2"
  else (
    beta=lift(beta,ZZ);
    Sum1:=0;
    B:=0;
    ell:=1;
    B0:=0;
    B1:=0;
    B2:=0;
    P0:=0;
    P11:=0;
    P12:=0;
    Sum0:=0;
    Sum11:=0;
    for i from 0 to r-1 do
      ell=ell*((d#i)!);

    for l from 0 to beta do (
      B0=(-ell)^beta/((beta-l)!);
      Sum0=0;

      I01:=indexSet1({l+1,a-l});
      I02:=indexSet1({l+1,n-b});

        
      for i from 0 to #(I01)-1 do
      for j from 0 to #(I02)-1 do (
        if I01#i#0==I02#j#0 then (
          P0=1;
          for k from 1 to l do (
            P0=P0*binomial(I01#i#k,I02#j#k);
            P0=P0*k^(I01#i#k-I02#j#k);
            );
        )
        else P0=0;
        Sum0=Sum0+P0;   
      );
      Sum1=Sum1+B0*Sum0;  
    );      

    for xi from 1 to beta do 
      for l from 0 to beta-xi do (
        B1=(-ell)^(beta-xi)/((beta-l-xi)!);
        for i from 0 to r-1 do 
          B1=B1*(((d#i)*xi)!);
        B1=B1/((xi!)^(n+r+1));

        Sum11=0;
        for p from 0 to n-b do (
          I1:=indexSet1({l+1,a-l});
          I2:=indexSet1({l+1,p});

          B2=0;
          for i from 0 to #(I1)-1 do
          for j from 0 to #(I2)-1 do (
            P11=1;
            for k from 0 to l do (
              P11=P11*binomial(I1#i#k,I2#j#k);
              P11=P11*(xi+k)^(I1#i#k-I2#j#k);
              );  
            B2=B2+P11;    
          );

          I3:=indexSet1({xi+r,n-b-p});
          B3:=0;
          for j from 0 to #(I3)-1 do (
            P12=1;
            for e from 1 to xi do (
              P12=P12*binomial(-n-r-1,I3#j#(e-1));
              P12=P12*e^(-I3#j#(e-1))
              );
            for i from 0 to r-1 do (
              P12=P12*(d#i)^(I3#j#(xi+i));
              P12=P12*functionMu({(d#i)*xi,I3#j#(xi+i)});
              );
            B3=B3+P12;  
            );
          Sum11=Sum11+B2*B3;  
          );
        Sum1=Sum1+B1*Sum11; 
    );
    B=D*Sum1;

    

    Sum2:=0;
    J:={};
    P2:=1;
    M:={};
    FAV:=0;
    for p from 1 to a-1 do (
      J=indexSet2({p,f});
      for k from 0 to #J-1 do if (not J#k#p==a) and (beta>(p+1-J#k#p)/f) then (
        M={};
        for i from 1 to p do 
          M=append(M,(1+J#k#(i-1)-J#k#i)/f);
        FAV=(functionAMod({{a-1-p,a},M}));
        P2=FAV;
        for i from 1 to p do (
          if 1+J#k#(i-1)>J#k#i then 
            P2=P2/D*(1+J#k#(i-1)-J#k#i)/f*invariantTwoPointsFanoIndexOne({J#k#(i-1),n-J#k#i,0,n,d});
          );
        P2=P2*invariantTwoPointsFanoIndexOne({J#k#p,b,a+c-p-1,n,d});
        Sum2=Sum2+P2;
      );  
    );
    Inv=B-Sum2; 
    );
  Inv
)
)



invariantTwoPoints =memoize(L->(
  n:=L#3;           --dimension
  d:=L#4;           --multidegree of the target manifold
  r:=#d;
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;          --Fano index
  inv:=0;
  if f<=0 then print "The Fano index is <=0"
  else if f>=2 then inv=invariantTwoPointsFanoIndexAtLeastTwo(L)
  else if f==1 then inv=invariantTwoPointsFanoIndexOne(L);
  inv
)
)



matrixCoeffW =memoize(L->(     --coefficient of the matrix W when Fano index >=1
  n:=L#0;
  d:=L#1;
  i:=L#2#0;
  j:=L#2#1;
  r:=#d;
  D:=1;
  S:={};
  B:=0;
  for i from 0 to r-1 do 
    D=D*(d#i);        --product of the components of the multidegree
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;          --Fano index
  if f<=0 then print "The Fano index is <=0"
  else (  W:=0;
      if i<0 or i>n or j<0 or j>n then W=0
      else if i==0 and j==0 then W=1
      else if i==0 and (not j==0) then W=0    
      else if i>0 and  j>i then W=0
      else if f>=2 then (
        if (not (i-j)/f==floor((i-j)/f)) then W=0
        else if i>0 and j==i then W=1
        else  ( S=matrixCoeffW({n,d,{i-1,j-1}});
            B=floor((i-j+1)/f);
            for k from 1 to B do (
            S=S+k*matrixCoeffW({n,d,{i-1,j-1+k*f}})*invariantTwoPoints({j-1+k*f,n-j,0,n,d})/D;
            );
            W=S;  
            );
        )
      else if f==1 then (
        ell:=1;
        for i from 0 to r-1 do
          ell=ell*((d#i)!);
        if i>0 and j==i then W=1
        else ( S=matrixCoeffW({n,d,{i-1,j-1}});
            for k from 1 to i-j+1 do (
            S=S+k*matrixCoeffW({n,d,{i-1,j-1+k}})*invariantTwoPoints({j-1+k,n-j,0,n,d})/D;
            );
            S=S+ell*matrixCoeffW({n,d,{i-1,j}});
            W=S;  
            );
        );
    );        
  W 
)
)


matrixW = memoize(L->(      --coefficient of the matrix W when Fano index >=1
  n:=L#0;
  d:=L#1;
  S:={};
  Row:={};
  W:={};
  for i from 0 to n do (
    Row={};
    for j from 0 to n do 
      Row=append(Row,matrixCoeffW({n,d,{i,j}}));
    S=append(S,Row)
    );
  W=matrix S; 
  W
)
)




matrixCoeffM =memoize(L->(
  n:=L#0;
  d:=L#1;
  i:=L#2#0;
  j:=L#2#1;
  r:=#d;
  D:=1;
  for i from 0 to r-1 do 
    D=D*(d#i);        --product of the components of the multidegree
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;          --Fano index
  B:=floor((i-j+1)/f);
  M:=0;
  if i<0 or i>n or j<0 or j>n then M=0
  else if i==0 and j==0 then M=1
  else if i==0 and (not j==0) then M=0    
  else if i>0 and  j>i then M=0
  else if (not (i-j)/f==floor((i-j)/f)) then M=0
  else if i>0 and j==i then M=1
  else  ( B=floor((i-j)/f);
      S:=0;
      for k from 1 to B do (
        S=S+matrixCoeffW({n,d,{i,i-k*f}})*matrixCoeffM({n,d,{i-k*f,j}})
        );
      M=-S; 
      );  
  M 
)
)



matrixM =memoize(L->(      --coefficient of the matrix M when Fano index >=1
  n:=L#0;
  d:=L#1;
  S:={};
  Row:={};
  M:={};
  for i from 0 to n do (
    Row={};
    for j from 0 to n do 
      Row=append(Row,matrixCoeffM({n,d,{i,j}}));
    S=append(S,Row)
    );
  M=matrix S; 
  M
)
)



EulerVectorFieldCoeff =memoize(L->(
  n:=L#0;
  d:=L#1;
  j:=L#2;
  k:=L#3;
  S:=0;
  for i from 0 to n do 
    S=S+(1-i)*matrixCoeffW({n,d,{j,i}})*matrixCoeffM({n,d,{i,k}});
  S
)
)



sfb =memoize(L->(  --the function \mathsf{b}(\mathbf{d}) of the multidegree d
  r:=#L;
  b:=1;
  for i from 0 to r-1 do
    b=b*(L#i)^(L#i);
  b
)
)



inversePairingInTauCoord =memoize(L->(
  n:=L#0;
  d:=L#1;
  i:=L#2#0;
  j:=L#2#1;
  r:=#d;
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;        --Fano index
  D:=1;
  for i from 0 to r-1 do 
    D=D*(d#i);        --product of the components of the multidegree
  eta:=0;
  if i>=0 and i<=n and j>=0 and j<=n then (if i+j==n-f then
      eta=-sfb(d)/D
  else if i+j==n then 
      eta=1/D;  
    );
  eta 
)
)


lengthThreeCorrelatorInTauCoord =memoize(L->(
  n:=L#0;
  d:=L#1;
  i:=L#2#0;
  j:=L#2#1;
  k:=L#2#2;
  r:=#d;
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;        --Fano index
  D:=1;
  for i from 0 to r-1 do 
    D=D*(d#i);        --product of the components of the multidegree
  inv:=0;
  b:=(i+j+k-n)/f;
  if i>=0 and i<=n and j>=0 and j<=n and k>=0 and k<=n and b>=0 and b==floor(b) then 
    inv=(sfb(d))^b*D;
  inv 
)
)



--lowerLists= method(TypicalValue=>List)
lowerLists =memoize(L->(
  r:=#L;
  M:={};
  T:={};
  S:={};
  if r==1 then (
    for i from 0 to (L#0) do
      S=append(S,{i})
    )
  else if r>=2 then (
    M=drop(L,-1);
    T=lowerLists(M);
    for j from 0 to #T-1 do
    for i from 0 to (L#(-1)) do 
      S=append(S,append(T#j,i));
    );
  S   
)
)
--lowerLists=memoize lowerLists

--binomOfLists= method(TypicalValue=>List)
binomOfLists =memoize(L->(
  I:=L#0;
  J:=L#1;
  r:=#I;
  s:=#J;
  B:=1;
  if (not r==s) then print "The two lists have different lenghts!"
  else (
    B=1;
    for i from 0 to r-1 do
      B=B*binomial(I#i,J#i);
    );
  B 
)
)
--binomOfLists=memoize binomOfLists

unitVector= method(TypicalValue=>List)
unitVector List:=L->(         --produce the unit vector of length n at the i-th direction
  n:=L#0;
  ui:=L#1;
  V:={};
  if ui>=0 and ui<=n-1 then (
  for j from -1 to ui-2 do 
    V=append(V,0);
  V=append(V,1);
  for j from ui+1 to n-1 do
    V=append(V,0);
  );
  V
)


zeroVector= method(TypicalValue=>ZZ)
zeroVector ZZ:=n->(           --produce a zero vector of length n
  V:={};
  for i from 0 to n-1 do
    V=append(V,0);
  V
)


minPositiveIndex= method(TypicalValue=>List)
minPositiveIndex List:=L->(        --produce the smallest k positive indices, with multiplicity
  M:=L#0;
  n:=#M;
  S:={};
  k:=L#1;
  for j from 1 to k do (
  for i from 0 to n-1 do  
    if (M#i)>0 then break (S=append(S,i);
      M=M-unitVector({n,i});
      );
  );
  S
)


fanoIndex = method(TypicalValue => List)
fanoIndex List:=L->(
  n:=L#0;
  d:=L#1;
  r:=#d;
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;  
  f
)



--ambientCorrelatorInTauCoord1=method(TypicalValue => List)
ambientCorrelatorInTauCoord1 =memoize(L->(           --correlator of length at least 3, in the tau coordinates, precheck the dimension constraint
  n:=L#0;
  d:=L#1;
  I0:=L#2;
  correl:=0;
  A:=sum(I0);
  Neg:=0;
  for i from 0 to n do 
    if I0#i<0 then break Neg=1;
  if Neg==0 then (
    if  A==3 then 
          correl=lengthThreeCorrelatorInTauCoord({n,d,minPositiveIndex({I0,3})})
    else if A>3 then (
    f:=fanoIndex({n,d});  
    D:=n-3+sum(I0);
    for i from 0 to n do 
      D=D+i*(I0#i);
    if D/f==floor(D/f) then (
        I:={};  
        Ijk:={};  
        S:=0;
        SUB:={};
        ijk:={};
        J:={};
        P:=1;
        S1:=0;
        S2:=0;
        i:=0;
        j:=0;
        k:=0;
        
        if I0#0>0 then correl=0
        else if I0#1 >0 then (
          I=I0- unitVector({n+1,1});
          S=0;
          for j from 0 to n do
          for k from 0 to n do (
            Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
            S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*ambientCorrelatorInTauCoord1({n,d,Ijk});
            );
          S=S+(3-n)*ambientCorrelatorInTauCoord1({n,d,I});
          correl=S/f; 
          )
        else if I0#1==0 then (
          S=0;
          P=1;
          ijk=minPositiveIndex({I0,3});
          i=ijk#0;
          j=ijk#1;
          k=ijk#2;
          I=I0- unitVector({n+1,i})-unitVector({n+1,j})-unitVector({n+1,k});
          SUB=lowerLists(I);
          for l from 0 to #SUB-1 do (
            J=SUB#l;
            if (not J==zeroVector(n+1)) then (
              S1=0;
              for a from 0 to n do
              for b from 0 to n do (
                P=1;
                P=P*ambientCorrelatorInTauCoord1({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                P=P*inversePairingInTauCoord({n,d,{a,b}});
                P=P*ambientCorrelatorInTauCoord1({n,d,I-J+unitVector({n+1,b})+unitVector({n+1,j})+unitVector({n+1,k})});
                S1=S1+P;
                );
              S=S-S1*binomOfLists({I,J}); 
              );
            S2=0;
            for a from 0 to n do 
            for b from 0 to n do (
              P=1;
              P=P*ambientCorrelatorInTauCoord1({n,d,J+unitVector({n+1,1})+unitVector({n+1,j})+unitVector({n+1,a})});
              P=P*inversePairingInTauCoord({n,d,{a,b}});
              P=P*ambientCorrelatorInTauCoord1({n,d,I-J+unitVector({n+1,b})+unitVector({n+1,i-1})+unitVector({n+1,k})});
              S2=S2+P;
              );
            S=S+S2*binomOfLists({I,J});   
            );
          correl=S; 
            );  
        );
      );
    );
  correl
)
)
--ambientCorrelatorInTauCoord1=memoize ambientCorrelatorInTauCoord1




--ambientCorrelatorInTauCoord=  method(TypicalValue => List)
ambientCorrelatorInTauCoord =memoize(L->(           --correlator of length at least 3, in the tau coordinates
  n:=L#0;
  d:=L#1;
  I0:=L#2;
  correl:=0;
  A:=sum(I0);
  Neg:=0;
  for i from 0 to n do 
    if I0#i<0 then break (correl=0;
      Neg=1;
      );
  f:=fanoIndex({n,d});  
  I:={};  
  Ijk:={};  
  S:=0;
  SUB:={};
  ijk:={};
  J:={};
  P:=1;
  S1:=0;
  S2:=0;
  i:=0;
  j:=0;
  k:=0;
  if Neg==0 then (if  A<3 then print "The length is <3."
  else if A==3 then 
    correl=lengthThreeCorrelatorInTauCoord({n,d,minPositiveIndex({I0,3})})
  else if A>3 then (
    if I0#0>0 then correl=0
    else if I0#1 >0 then (
      I=I0- unitVector({n+1,1});
      S=0;
      for j from 0 to n do
      for k from 0 to n do (
        Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
        S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*ambientCorrelatorInTauCoord({n,d,Ijk});
        );
      S=S+(3-n)*ambientCorrelatorInTauCoord({n,d,I});
      correl=S/f; 
      )
    else if I0#1==0 then (
      S=0;
      P=1;
      ijk=minPositiveIndex({I0,3});
      i=ijk#0;
      j=ijk#1;
      k=ijk#2;
      I=I0- unitVector({n+1,i})-unitVector({n+1,j})-unitVector({n+1,k});
      SUB=lowerLists(I);
      for l from 0 to #SUB-1 do (
        J=SUB#l;
        if (not J==zeroVector(n+1)) then (
          S1=0;
          for a from 0 to n do
          for b from 0 to n do (
            P=1;
            P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
            P=P*inversePairingInTauCoord({n,d,{a,b}});
            P=P*ambientCorrelatorInTauCoord({n,d,I-J+unitVector({n+1,b})+unitVector({n+1,j})+unitVector({n+1,k})});
            S1=S1+P;
            );
          S=S-S1*binomOfLists({I,J}); 
          );
        S2=0;
        for a from 0 to n do 
        for b from 0 to n do (
          P=1;
          P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,j})+unitVector({n+1,a})});
          P=P*inversePairingInTauCoord({n,d,{a,b}});
          P=P*ambientCorrelatorInTauCoord({n,d,I-J+unitVector({n+1,b})+unitVector({n+1,i-1})+unitVector({n+1,k})});
          S2=S2+P;
          );
        S=S+S2*binomOfLists({I,J});   
        );
      correl=S; 
      );  
    );
    );
  correl
)
)
--ambientCorrelatorInTauCoord=memoize ambientCorrelatorInTauCoord



functionC=method(TypicalValue => List)
functionC List:=L->(
  n:=L#0;
  d:=L#1;
  l:=L#2;
  f:=fanoIndex({n,d});
  S:=1;
  for i from 0 to l do
  for j from 0 to i do
    S=S+(i-j)*matrixCoeffM({n,d,{n-j*f,n-i*f}})*matrixCoeffW({n,d,{n,n-j*f}})*(sfb(d))^(-i);
  for i from 0 to l do
  for j from 0 to i do
    S=S-(i-j)*matrixCoeffM({n,d,{n-j*f,n-i*f}})*matrixCoeffW({n,d,{n-f,n-j*f}})*(sfb(d))^(1-i);
  S
)


--ellD=method(TypicalValue => List)
ellD =memoize(L->(
  r:=#L;
  P:=1;
  for i from 0 to r-1 do 
    P=P*(L#i)!;
  P
)
)
--ellD=memoize ellD




lengthOneCorrelator=method(TypicalValue => List)
lengthOneCorrelator List:=L->(
  n:=L#0;
  d:=L#1;
  r:=#d;
  a:=L#2;
  f:=fanoIndex({n,d});
  inv:=0;
  S:=0;
  if f==2 and a==n then 
    inv=ellD(d)*product(d);
  if f==1 and a==n-1 then (
    S=-n-r-1;
    for i from 0 to r-1 do 
      S=S+(d#i)*functionMu({d#i,1});
    inv=ellD(d)*product(d)*S;
    );
  if f==1 and a==n then (
    inv=product(d);
    inv=inv*(-1/2*(ellD(d))^2+2^(-n-r-1)*(ellD(2*d)));
    );
  inv 
)


lengthTwoCorrelator=method(TypicalValue => List)
lengthTwoCorrelator List:=L->(
  n:=L#0;
  d:=L#1;
  a:=L#2#0;
  b:=L#2#1;
  inv:=invariantTwoPoints {a,b,0,n,d};
  inv 
)


ringOfTCoord =memoize(n->(
  R:=QQ[t_0..t_n];
  R
))


ringOfTauCoord =memoize(n->(
  R:=QQ[tau_0..tau_n];
  R
))

ringOfTCoordAndS =memoize(n->(
  R:=QQ[t_0..t_n,s];
  R
))


ringOfTauCoordAndS =memoize(n->(
  R:=QQ[tau_0..tau_n,s];
  R
))



ambientGeneratingFuncInTauCoordOfDegreeB=method()
ambientGeneratingFuncInTauCoordOfDegreeB List:=L->(       --generating function in terms of tau, of degree B>=3
  n:=L#0;
  d:=L#1;
  B:=L#2;                 --degree of monomials
  R:=ringOfTauCoord n;
  S:=0; 
  M:=indexSet1({n+1,B});
  P:=1;
  for j from 0 to #M-1 do (
    P=1;
    for k from 0 to n do 
      P=P*(tau_k_R)^(M#j#k);
    P=P/ellD(M#j);
    P=P*ambientCorrelatorInTauCoord({n,d,M#j});
    S=S+P;
    );
  S 
)


ambientGeneratingFuncOfDegreeB=method()
ambientGeneratingFuncOfDegreeB List:=L->(    
  n:=L#0;
  d:=L#1;
  B:=L#2;                 --degree of monomials
  R:=ringOfTCoord n;
  f:={};

  S:=0;
  subk:=0;
  if B==0 then S=0
  else if B==1 then (
    S=0;
    for k from 0 to n do 
      S=S+lengthOneCorrelator({n,d,k})*t_k_R;)
  else if B==2 then (
    S=0;
    for a from 0 to n do
    for b from 0 to n do
      S=S+lengthTwoCorrelator({n,d,{a,b}})*(t_a_R)*(t_b_R);
    S=S/2;
    )
  else if B>=3 then (
    S=ambientGeneratingFuncInTauCoordOfDegreeB({n,d,B});
    R0:=ring S;
    SUB:={};
    for k from 0 to n do (
      subk=0;
      for j from 0 to n do
        subk=subk+matrixCoeffM({n,d,{j,k}})*t_j_R;
      SUB=append(SUB,subk);
      ); 
    f=map(R,R0,SUB);
    S=f(S);
  );
  S 
)   





ambientGeneratingFuncOfDegreeUpToB=method(TypicalValue => List)
ambientGeneratingFuncOfDegreeUpToB List:=L->(    
  n:=L#0;
  d:=L#1;
  B:=L#2;  
  S:=0;
  for i from 0 to B do
    S=S+ambientGeneratingFuncOfDegreeB({n,d,i});
  S 
)








--functionOfWM=method(TypicalValue => List)
functionOfWM =memoize(L->(
  n:=L#0;
  d:=L#1;
  r:=#d;
  f:=n+r+1; 
  for i from 0 to r-1 do 
    f=f-d#i;          --Fano index
  b:=1;
  for i from 0 to r-1 do
    b=b*(d#(i)^(d#(i)));
  l:=(n-1)/f;
  S:=0;
  S1:=0;
  S2:=0;
  if (not l==floor(l)) then S=0
  else (l=lift(l,ZZ);
    S1=0;
    for i from 0 to l do
      S1=S1+(1+f*i)*matrixCoeffM({n,d,{1+f*i,1}})*matrixCoeffW({n,d,{n,1+f*i}});
    S2=0;
    for i from 0 to l-1 do
      S2=S2+(1+f*i)*matrixCoeffM({n,d,{1+f*i,1}})*matrixCoeffW({n,d,{n-f,1+f*i}});
    S=-S1+b*S2;
    );
  S
)
)
--functionOfWM=memoize functionOfWM



--constantTermOfF2=method(TypicalValue => List)
constantTermOfF2 =memoize(L->(
  n:=L#0;
  d:=L#1;
  r:=#d;
  f:=fanoIndex L;
  ell:=ellD d;
  l:=(n-1)/f;
  P:=0;
  if l==1 then P=1
  else if (not l==1) then
  P=functionOfWM({n,d})/(f*product(d));
  P
)
)
--constantTermOfF2=memoize constantTermOfF2



--correlatorOfSOrderOneInTauCoord=method(TypicalValue => List)
correlatorOfSOrderOneInTauCoord =memoize(L->( 
    n:=L#0;
    d:=L#1;
    I0:=L#2;
    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
      if I0#i<0 then break (correl=0;
        Neg=1;
        );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    i:=0;
    if Neg>0 then correl=0 
    else if Neg==0 then (
    if  A==0 then (
        if f==1 then correl=-ellD(d)
        else if f>=2 then correl=0;
        )
    else if  A==1 then (
        if I0#0 ==1 then correl=1 
        else correl=0;
        )
    else if A>1 then (
      if I0#0>0 then correl=0
      else if I0#1 >0 then (
        I=I0- unitVector({n+1,1});
        S=0;
        for j from 0 to n do
        for k from 0 to n do (
          Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
          S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorOfSOrderOneInTauCoord({n,d,Ijk});
          );
        S=S+correlatorOfSOrderOneInTauCoord({n,d,I});
        correl=S/f; 
        )
      else if I0#1==0 then (
        S=0;
        P=1;
        i=(minPositiveIndex({I0,1}))#0;
        I=I0- unitVector({n+1,i});
        low=lowerLists(I);
        for l from 0 to #low-1 do (
          J=low#l;
          if (not J==zeroVector(n+1)) then (
            S1=0;
            for a from 0 to n do
            for b from 0 to n do (
              P=1;
              P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
              P=P*inversePairingInTauCoord({n,d,{a,b}});
              P=P*correlatorOfSOrderOneInTauCoord({n,d,I-J+unitVector({n+1,b})});
              S1=S1+P;
              );
            S=S-S1*binomOfLists({I,J}); 
            );
          P=1;
            P=P*correlatorOfSOrderOneInTauCoord({n,d,J+unitVector({n+1,1})});
            P=P*correlatorOfSOrderOneInTauCoord({n,d,I-J+unitVector({n+1,i-1})});
          S=S+P*binomOfLists({I,J});   
          );
        correl=S; 
        );  
      );
      );
    correl
)
)
--correlatorOfSOrderOneInTauCoord=memoize correlatorOfSOrderOneInTauCoord



--correlatorOfSOrderTwoInTauCoord=method(TypicalValue => List)
correlatorOfSOrderTwoInTauCoord =memoize(L->( 
    n:=L#0;
    d:=L#1;
    I0:=L#2;
    correl:=0;
    A:=sum(I0);
    Neg:=0;
    inv:=0;
    for i from 0 to n do 
      if I0#i<0 then break (inv=0;
        Neg=1;
        );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    i:=0;
    if Neg>0 then correl=0 
    else if Neg==0 then (
    if  A==0 then correl=constantTermOfF2 {n,d}
    else if A>0 then (
      if I0#0>0 then correl=0
      else if I0#1 >0 then (
        I=I0- unitVector({n+1,1});
        S=0;
        for j from 0 to n do
        for k from 0 to n do (
          Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
          S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorOfSOrderTwoInTauCoord({n,d,Ijk});
          );
        S=S+(n-1)*correlatorOfSOrderTwoInTauCoord({n,d,I});
        correl=S/f; 
        )
      else if I0#1==0 then (
        S=0;
        P=1;
        i=(minPositiveIndex({I0,1}))#0;
        I=I0- unitVector({n+1,i});
        low=lowerLists(I);
        for l from 0 to #low-1 do (
          J=low#l;
          if (not J==zeroVector(n+1)) then (
            S1=0;
            for a from 0 to n do
            for b from 0 to n do (
              P=1;
              P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
              P=P*inversePairingInTauCoord({n,d,{a,b}});
              P=P*correlatorOfSOrderTwoInTauCoord({n,d,I-J+unitVector({n+1,b})});
              S1=S1+P;
              );
          S=S-S1*binomOfLists({I,J}); 
          );
          P=1;
            P=P*correlatorOfSOrderOneInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})});
            P=P*correlatorOfSOrderTwoInTauCoord({n,d,I-J});
          S=S-P*2*binomOfLists({I,J}); 
          P=1;
            P=P*correlatorOfSOrderTwoInTauCoord({n,d,J+unitVector({n+1,1})});
            P=P*correlatorOfSOrderOneInTauCoord({n,d,I-J+unitVector({n+1,i-1})});
          S=S+P*binomOfLists({I,J});
          P=1;
            P=P*correlatorOfSOrderOneInTauCoord({n,d,J+unitVector({n+1,1})});
            P=P*correlatorOfSOrderTwoInTauCoord({n,d,I-J+unitVector({n+1,i-1})});
          S=S+P*binomOfLists({I,J});
        S2=0;
          for a from 0 to n do 
          for b from 0 to n do (
            P=1;
            P=P*correlatorOfSOrderOneInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
            P=P*inversePairingInTauCoord({n,d,{a,b}});
            P=P*correlatorOfSOrderOneInTauCoord({n,d,I-J+unitVector({n+1,b})});
            S2=S2+P;
            );
          S=S-S2*binomOfLists({I,J});
          );
        correl=S; 
        );  
      );
      );
    correl
)
)
--correlatorOfSOrderTwoInTauCoord=memoize correlatorOfSOrderTwoInTauCoord


ringOfUnknownConstTerms=method(TypicalValue => List)
ringOfUnknownConstTerms ZZ:=n->(
  R:=QQ;
  if n>=2 then R=QQ[z_2..z_n];
  R
)


correlatorInTauCoord =memoize(L->( 
    n:=L#0;
    d:=L#1;
    l:=L#2;    --the s-order, >=1
    I0:=L#3;
    R:=QQ[z_2..z_l];
    M:=gens R;

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    S3:=0;
    S4:=0;
    T3:=0;
    i:=0;
    if  Neg==0 then (
        if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
        if l>=2 then (
           if  A==0 then (
            if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
            else correl=M#(l-2);
            )
           else if A>0 then (
            if I0#0>0 then correl=0
            else if I0#1 >0 then (
              I=I0- unitVector({n+1,1});
              S=0;
              for j from 0 to n do
              for k from 0 to n do (
                Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorInTauCoord({n,d,l,Ijk});
                );
              S=S+(n*l-n+3-2*l)*correlatorInTauCoord({n,d,l,I});
              correl=S/f; 
              )
            else if I0#1==0 then (
              S=0;
              P=1;
              i=(minPositiveIndex({I0,1}))#0;
              I=I0- unitVector({n+1,i});
              low=lowerLists(I);
              for j from 0 to #low-1 do (
                  J=low#j;
                  if (not J==zeroVector(n+1)) then (
                      S1=0;
                      for a from 0 to n do
                      for b from 0 to n do (
                        P=1;
                        P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*(correlatorInTauCoord {n,d,l,I-J+unitVector({n+1,b})});
                        S1=S1+P;
                        );
                  S=S-S1*binomOfLists({I,J}); 
                  );
                  
                  
                  S2=0;
                  for k from 1 to l do (
                    P=1;
                      P=P*correlatorInTauCoord({n,d,k,J+unitVector({n+1,1})});
                      P=P*correlatorInTauCoord({n,d,l-k+1,I-J+unitVector({n+1,i-1})});
                    S2=S2+P*binomial(l-1,k-1); 
                  );
                  S=S+S2*binomOfLists({I,J});
                  
                  S3=0;
                  for k from 1 to l-1 do (
                    T3=0;
                    for a from 0 to n do 
                    for b from 0 to n do (
                        P=1;
                        P=P*correlatorInTauCoord({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*correlatorInTauCoord({n,d,l-k,I-J+unitVector({n+1,b})});
                        T3=T3+P;
                        );
                    S3=S3+T3*binomial(l-1,k); 
                    );
                  S=S-S3*binomOfLists({I,J});

                S4=0;
                for k from 1 to l-1 do (
                  P=1;
                  P=P*correlatorInTauCoord({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})});
                  P=P*correlatorInTauCoord({n,d,l-k+1,I-J});
                  S4=S4+P*binomial(l-2,k-1);
                  );
                S=S-S4*2*(l-1)*binomOfLists({I,J});
                  );
                correl=S; 
                );  
            );
          );
   
      );
      correl
)
)



correlatorInTauCoord1 =memoize(L->(                                       --function correlatorInTauCoord used in equationOfConstTerm, not using the constant term of F^(2)(0)
    n:=L#0;
    d:=L#1;
    l:=L#2;
    I0:=L#3;
    M:=L#4;

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    S3:=0;
    S4:=0;
    T3:=0;
    i:=0;
    if  Neg==0 then (
        if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
        if l>=2 then (
           if  A==0 then (
            if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
            else correl=M#(l-2);
            )
           else if A>0 then (
            if I0#0>0 then correl=0
            else if I0#1 >0 then (
              I=I0- unitVector({n+1,1});
              S=0;
              for j from 0 to n do
              for k from 0 to n do (
                Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorInTauCoord1({n,d,l,Ijk,M});
                );
              S=S+(n*l-n+3-2*l)*correlatorInTauCoord1({n,d,l,I,M});
              correl=S/f; 
              )
            else if I0#1==0 then (
              S=0;
              P=1;
              i=(minPositiveIndex({I0,1}))#0;
              I=I0- unitVector({n+1,i});
              low=lowerLists(I);
              for j from 0 to #low-1 do (
                  J=low#j;
                  if (not J==zeroVector(n+1)) then (
                      S1=0;
                      for a from 0 to n do
                      for b from 0 to n do (
                        P=1;
                        P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*(correlatorInTauCoord1 {n,d,l,I-J+unitVector({n+1,b}),M});
                        S1=S1+P;
                        );
                  S=S-S1*binomOfLists({I,J}); 
                  );
                  
                  
                  S2=0;
                  for k from 1 to l do (
                    P=1;
                      P=P*correlatorInTauCoord1({n,d,k,J+unitVector({n+1,1}),M});
                      P=P*correlatorInTauCoord1({n,d,l-k+1,I-J+unitVector({n+1,i-1}),M});
                    S2=S2+P*binomial(l-1,k-1); 
                  );
                  S=S+S2*binomOfLists({I,J});
                  
                  S3=0;
                  for k from 1 to l-1 do (
                    T3=0;
                    for a from 0 to n do 
                    for b from 0 to n do (
                        P=1;
                        P=P*correlatorInTauCoord1({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a}),M});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*correlatorInTauCoord1({n,d,l-k,I-J+unitVector({n+1,b}),M});
                        T3=T3+P;
                        );
                    S3=S3+T3*binomial(l-1,k); 
                    );
                  S=S-S3*binomOfLists({I,J});

                S4=0;
                for k from 1 to l-1 do (
                  P=1;
                  P=P*correlatorInTauCoord1({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1}),M});
                  P=P*correlatorInTauCoord1({n,d,l-k+1,I-J,M});
                  S4=S4+P*binomial(l-2,k-1);
                  );
                S=S-S4*2*(l-1)*binomOfLists({I,J});
                  );
                correl=S; 
                );  
            );
          );
   
      );
    correl
)
)




correlatorInTauCoord2 =memoize(L->(                                            --function correlatorInTauCoord used in equationOfConstTerm2, using the constant term of F^(2)(0)
    n:=L#0;
    d:=L#1;
    l:=L#2; --order of s
    I0:=L#3;  --number of insertions of each ambient class
    M:=L#4; --indeterminants associated to the constant term of each s-order

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    S3:=0;
    S4:=0;
    T3:=0;
    i:=0;
    if  Neg==0 then (
        if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
        if l==2 then correl=correlatorOfSOrderTwoInTauCoord {n,d,I0};
        if l>=3 then (
           if  A==0 then (
            if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
            else correl=M#(l-2);
            )
           else if A>0 then (
            if I0#0>0 then correl=0
            else if I0#1 >0 then (
              I=I0- unitVector({n+1,1});
              S=0;
              for j from 0 to n do
              for k from 0 to n do (
                Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorInTauCoord2({n,d,l,Ijk,M});
                );
              S=S+(n*l-n+3-2*l)*correlatorInTauCoord2({n,d,l,I,M});
              correl=S/f; 
              )
            else if I0#1==0 then (
              S=0;
              P=1;
              i=(minPositiveIndex({I0,1}))#0;
              I=I0- unitVector({n+1,i});
              low=lowerLists(I);
              for j from 0 to #low-1 do (
                  J=low#j;
                  if (not J==zeroVector(n+1)) then (
                      S1=0;
                      for a from 0 to n do
                      for b from 0 to n do (
                        P=1;
                        P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*(correlatorInTauCoord2 {n,d,l,I-J+unitVector({n+1,b}),M});
                        S1=S1+P;
                        );
                  S=S-S1*binomOfLists({I,J}); 
                  );
                  
                  
                  S2=0;
                  for k from 1 to l do (
                    P=1;
                      P=P*correlatorInTauCoord2({n,d,k,J+unitVector({n+1,1}),M});
                      P=P*correlatorInTauCoord2({n,d,l-k+1,I-J+unitVector({n+1,i-1}),M});
                    S2=S2+P*binomial(l-1,k-1); 
                  );
                  S=S+S2*binomOfLists({I,J});
                  
                  S3=0;
                  for k from 1 to l-1 do (
                    T3=0;
                    for a from 0 to n do 
                    for b from 0 to n do (
                        P=1;
                        P=P*correlatorInTauCoord2({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a}),M});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*correlatorInTauCoord2({n,d,l-k,I-J+unitVector({n+1,b}),M});
                        T3=T3+P;
                        );
                    S3=S3+T3*binomial(l-1,k); 
                    );
                  S=S-S3*binomOfLists({I,J});

                S4=0;
                for k from 1 to l-1 do (
                  P=1;
                  P=P*correlatorInTauCoord2({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1}),M});
                  P=P*correlatorInTauCoord2({n,d,l-k+1,I-J,M});
                  S4=S4+P*binomial(l-2,k-1);
                  );
                S=S-S4*2*(l-1)*binomOfLists({I,J});
                  );
                correl=S; 
                );  
            );
          );
   
      );
    correl
)
)



correlatorInTauCoord3 =memoize(L->(                                       --function correlatorInTauCoord used in equationOfConstTerm, not using the constant term of F^(2)(0), using the odd dimension vanishing due to graded symmetric
    n:=L#0;
    d:=L#1;
    l:=L#2;
    I0:=L#3;
    M:=L#4;
    m:=dimPrimCoh {n,d};
    m1:=lift(m/2,ZZ);

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    S3:=0;
    S4:=0;
    T3:=0;
    i:=0;
    if  Neg==0 then (
        if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
        if l>m1 then correl=0;
        if l>=2 and l<=m1 then (
           if  A==0 then (
            if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
            else correl=M#(l-2);
            )
           else if A>0 then (
            if I0#0>0 then correl=0
            else if I0#1 >0 then (
              I=I0- unitVector({n+1,1});
              S=0;
              for j from 0 to n do
              for k from 0 to n do (
                Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorInTauCoord3({n,d,l,Ijk,M});
                );
              S=S+(n*l-n+3-2*l)*correlatorInTauCoord3({n,d,l,I,M});
              correl=S/f; 
              )
            else if I0#1==0 then (
              S=0;
              P=1;
              i=(minPositiveIndex({I0,1}))#0;
              I=I0- unitVector({n+1,i});
              low=lowerLists(I);
              for j from 0 to #low-1 do (
                  J=low#j;
                  if (not J==zeroVector(n+1)) then (
                      S1=0;
                      for a from 0 to n do
                      for b from 0 to n do (
                        P=1;
                        P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*(correlatorInTauCoord3 {n,d,l,I-J+unitVector({n+1,b}),M});
                        S1=S1+P;
                        );
                  S=S-S1*binomOfLists({I,J}); 
                  );
                  
                  
                  S2=0;
                  for k from 1 to l do (
                    P=1;
                      P=P*correlatorInTauCoord3({n,d,k,J+unitVector({n+1,1}),M});
                      P=P*correlatorInTauCoord3({n,d,l-k+1,I-J+unitVector({n+1,i-1}),M});
                    S2=S2+P*binomial(l-1,k-1); 
                  );
                  S=S+S2*binomOfLists({I,J});
                  
                  S3=0;
                  for k from 1 to l-1 do (
                    T3=0;
                    for a from 0 to n do 
                    for b from 0 to n do (
                        P=1;
                        P=P*correlatorInTauCoord3({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a}),M});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*correlatorInTauCoord3({n,d,l-k,I-J+unitVector({n+1,b}),M});
                        T3=T3+P;
                        );
                    S3=S3+T3*binomial(l-1,k); 
                    );
                  S=S-S3*binomOfLists({I,J});

                S4=0;
                for k from 1 to l-1 do (
                  P=1;
                  P=P*correlatorInTauCoord3({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1}),M});
                  P=P*correlatorInTauCoord3({n,d,l-k+1,I-J,M});
                  S4=S4+P*binomial(l-2,k-1);
                  );
                S=S-S4*2*(l-1)*binomOfLists({I,J});
                  );
                correl=S; 
                );  
            );
          );
   
      );
    correl
)
)



dimPrimCoh=method()
dimPrimCoh List:=L->(
  n:=L#0;
  d:=L#1;
  r:=#d;
  I:=indexSet1 {r+1,n};
  S:=0;
  P:=1;
  for i from 0 to #I-1 do (
    P=binomial(n+r+1,I#i#0);
    for k from 1 to r do
      P=P*((-d#(k-1))^(I#i#k));
    S=S+P;
    );
  for i from 0 to r-1 do 
    S=S*(d#i);
  S=S-n-1;
  if  odd n then S=-S;
  S   
)





equationOfConstTerm =memoize(L->(
  n:=L#0;
  d:=L#1;
  l:=L#2; 
  R:=ringOfUnknownConstTerms l;
  M:=gens R;
  I:=L#3;
  low:=lowerLists I;
  P:=1;
  S:=0;
  S1:=0;
  S2:=0;
  J:={};
  T1:=0;
  for j from 0 to #low -1 do (
    J=low#j;

    S1=0;
        for k from 1 to l do (
          T1=0;
          for a from 0 to n do 
          for b from 0 to n do (
              P=1;
              P=P*(correlatorInTauCoord1 {n,d,k,J+unitVector({n+1,a}),M});
              P=P*inversePairingInTauCoord({n,d,{a,b}});
              P=P*(correlatorInTauCoord1 {n,d,l+1-k,I-J+unitVector({n+1,b}),M});
              T1=T1+P;
              );
          S1=S1+T1*binomial(l-1,k-1); 
          );
        S=S+S1*binomOfLists({I,J});

      S2=0;
      for k from 2 to l do (
        P=correlatorInTauCoord1 {n,d,k,J,M};
        P=P*(correlatorInTauCoord1 {n,d,l+2-k,I-J,M});
        S2=S2+P*binomial(l-2,k-2);
        );
      S=S+S2*2*(l-1)*binomOfLists({I,J}); 
    );
  S
)
)




equationOfConstTerm2 =memoize(L->(
  n:=L#0;
  d:=L#1;
  l:=L#2; 
  R:=ringOfUnknownConstTerms l;
  M:=gens R;
  I:=L#3;
  low:=lowerLists I;
  P:=1;
  S:=0;
  S1:=0;
  S2:=0;
  J:={};
  T1:=0;
  for j from 0 to #low -1 do (
    J=low#j;

    S1=0;
        for k from 1 to l do (
          T1=0;
          for a from 0 to n do 
          for b from 0 to n do (
              P=1;
              P=P*(correlatorInTauCoord2 {n,d,k,J+unitVector({n+1,a}),M});
              P=P*inversePairingInTauCoord({n,d,{a,b}});
              P=P*(correlatorInTauCoord2 {n,d,l+1-k,I-J+unitVector({n+1,b}),M});
              T1=T1+P;
              );
          S1=S1+T1*binomial(l-1,k-1); 
          );
        S=S+S1*binomOfLists({I,J});

      S2=0;
      for k from 2 to l do (
        P=correlatorInTauCoord2 {n,d,k,J,M};
        P=P*(correlatorInTauCoord2 {n,d,l+2-k,I-J,M});
        S2=S2+P*binomial(l-2,k-2);
        );
      S=S+S2*2*(l-1)*binomOfLists({I,J}); 
    );
  S 
)
)



sqrtRecursion =memoize(L->(     --compute z_k=F^(k)(0)
  n:=L#0;  --dimension
  d:=L#1;  --multidegree
  k:=L#2;  -- k is an integer >=2
  S:={};
  T:={};
  PSR:=0;
  f:=fanoIndex({n,d});
  if f<=0 then print "The Fano index is <=0"
    else (
        for i from 2 to k-1 do (
          if not #(sqrtRecursion {n,d,i})==2 then break PSR=i           --check the square root recursion for 2<=i<k
          );
        if PSR>0 then  print  ("the square root recursion fails at order "|(toString PSR))
          else (
            beta:=((n-2)*k-n+3)/f;
            if (not beta==floor(beta)) then S={0,0}    --dimension constraint
            else (
              Eq:=equationOfConstTerm {n,d,2*k-2,zeroVector (n+1)};
              R:=ring Eq;
              for i from 2 to k-1 do
                Eq=sub(Eq,{z_i_R=>(sqrtRecursion {n,d,i})#1});
              for i from k+1 to 2*k-2 do
                T=append(T,diff(z_i_R,Eq));
              Fac:=factor Eq;
              if T==zeroVector(k-2) and Fac#0#1==2 then (     --check Eq is a complete square quadratic polynomial of z_k
                linearFac:=Fac#0#0;
                a:=diff(z_k_R,linearFac);
                sol:=-(linearFac-a*z_k_R)/a;
                sol=lift(sol,QQ);
                S={Eq,sol}
                )
              else print ("the square root recursion fails at order "|(toString k)); 
            );      
          );        
    );
  S
)
)



correlAfterSqrtRecursionInTauCoord =memoize(L->(           -- non-quasi-exceptional complete intersections
    n:=L#0;
    d:=L#1;
    l:=L#2;    --the s-order, >=1
    I0:=L#3;

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    f:=fanoIndex({n,d});  
    I:={};  
    Ijk:={};  
    S:=0;
    low:={};
    J:={};
    P:=1;
    S1:=0;
    S2:=0;
    S3:=0;
    S4:=0;
    T3:=0;
    i:=0;
    if  Neg==0 then (
        if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
        if l>=2 then (
           if  A==0 then (
            if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
            else correl=(sqrtRecursion {n,d,l})#1;
            )
           else if A>0 then (
            if I0#0>0 then correl=0
            else if I0#1 >0 then (
              I=I0- unitVector({n+1,1});
              S=0;
              for j from 0 to n do
              for k from 0 to n do (
                Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlAfterSqrtRecursionInTauCoord({n,d,l,Ijk});
                );
              S=S+(n*l-n+3-2*l)*correlAfterSqrtRecursionInTauCoord({n,d,l,I});
              correl=S/f; 
              )
            else if I0#1==0 then (
              S=0;
              P=1;
              i=(minPositiveIndex({I0,1}))#0;
              I=I0- unitVector({n+1,i});
              low=lowerLists(I);
              for j from 0 to #low-1 do (
                  J=low#j;
                  if (not J==zeroVector(n+1)) then (
                      S1=0;
                      for a from 0 to n do
                      for b from 0 to n do (
                        P=1;
                        P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*(correlAfterSqrtRecursionInTauCoord {n,d,l,I-J+unitVector({n+1,b})});
                        S1=S1+P;
                        );
                  S=S-S1*binomOfLists({I,J}); 
                  );
                  
                  
                  S2=0;
                  for k from 1 to l do (
                    P=1;
                      P=P*correlAfterSqrtRecursionInTauCoord({n,d,k,J+unitVector({n+1,1})});
                      P=P*correlAfterSqrtRecursionInTauCoord({n,d,l-k+1,I-J+unitVector({n+1,i-1})});
                    S2=S2+P*binomial(l-1,k-1); 
                  );
                  S=S+S2*binomOfLists({I,J});
                  
                  S3=0;
                  for k from 1 to l-1 do (
                    T3=0;
                    for a from 0 to n do 
                    for b from 0 to n do (
                        P=1;
                        P=P*correlAfterSqrtRecursionInTauCoord({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                        P=P*inversePairingInTauCoord({n,d,{a,b}});
                        P=P*correlAfterSqrtRecursionInTauCoord({n,d,l-k,I-J+unitVector({n+1,b})});
                        T3=T3+P;
                        );
                    S3=S3+T3*binomial(l-1,k); 
                    );
                  S=S-S3*binomOfLists({I,J});

                S4=0;
                for k from 1 to l-1 do (
                  P=1;
                  P=P*correlAfterSqrtRecursionInTauCoord({n,d,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})});
                  P=P*correlAfterSqrtRecursionInTauCoord({n,d,l-k+1,I-J});
                  S4=S4+P*binomial(l-2,k-1);
                  );
                S=S-S4*2*(l-1)*binomOfLists({I,J});
                  );
                correl=S; 
                );  
            );
          );
   
      );
      correl
)
)





generatingFuncOfGivenSOrderInTauCoordUpToDegreeBNotCubic=method()
generatingFuncOfGivenSOrderInTauCoordUpToDegreeBNotCubic List:=L->(     --for non-exceptional, non-quasi-exceptional complete intersections, generating function of s-order l>=1 in tau-coordinates up to given degree B
  n:=L#0;
  d:=L#1;
  l:=L#2;     ------order of s, >=1
  B:=L#3;     --given bound of degree of monomials in tau-coordinates
  R:=ringOfTauCoord n;
  S:=0; 
  M:={};
  P:=0;
  for i from 0 to B do (
    M=indexSet1({n+1,i});
    for j from 0 to #M-1 do (
      P=1;
      for k from 0 to n do 
        P=P*(tau_k_R)^(M#j#k);
      P=P/ellD(M#j);
      P=P*correlAfterSqrtRecursionInTauCoord({n,d,l,M#j});
      S=S+P;
    );
  );
  S 
)



generatingFuncOfGivenSOrderInTCoordUpToDegreeBNotCubic=method()
generatingFuncOfGivenSOrderInTCoordUpToDegreeBNotCubic List:=L->(     --for non-exceptional, non-quasi-exceptional complete intersections, generating function of s-order l>=1 in t-coordinates up to given degree B
  n:=L#0;
  d:=L#1;
  l:=L#2;         ------order of s, >=1
  B:=L#3;         --given bound of degree of monomials in t-coordinates
  R:=ringOfTCoord n;
  f:={};
  
  S:=generatingFuncOfGivenSOrderInTauCoordUpToDegreeBNotCubic L;
  R0:=ring S;
    SUB:={};
    subk:=0;
    for k from 0 to n do (
      subk=0;
      for j from 0 to n do
        subk=subk+matrixCoeffM({n,d,{j,k}})*t_j_R;
      SUB=append(SUB,subk);
      ); 
    f=map(R,R0,SUB);
    S=f(S);   
  S 
)




generatingFuncOfDegreeUpToBNotCubic=method()
generatingFuncOfDegreeUpToBNotCubic List:=L->(                 --for non-exceptional, non-quasi-exceptional complete intersections, generating function up to given degree B, in t-coordinates
  n:=L#0;
  d:=L#1;
  B:=L#2;  ----given bound of degree of monomials in t-coordinates
  R:=ringOfTCoordAndS n;

  B1:=floor (B/2);
  if odd n then (
    m:=dimPrimCoh {n,d};
    l:=lift(m/2,ZZ);
    B1=min {l,B1};     --in odd dimension, the natural bound given by skew symmetry of middle dim classes
    );

  S0:={1};
  for i from 1 to B1 do
    S0=append(S0,s_R^i/i!);
  M0:=transpose matrix {S0};

  S:={ambientGeneratingFuncOfDegreeUpToB L};
  for i from 1 to B1 do
    S=append(S,generatingFuncOfGivenSOrderInTCoordUpToDegreeBNotCubic({n,d,i,B-2*i}));
  M1:=matrix {S};
  R1:=ring M1;

  gensR1:=drop(gens R,-1);   -- the list of generators {t_0,...,t_n} of R1
  f:=map(R,R1,gensR1);
  M1=f(M1);

  F:=flatten entries (M1*M0);
  F=F#0;

  if (odd n) and (B1>m/4+1) then 
       print ("the terms with s-degree >="|(toString ceiling (m/4+1))|" is hypothetical");
  F
)



generatingFuncOfDegreeUpToB=method()
generatingFuncOfDegreeUpToB List:=L->(                 --for a Fano complete intersection, of dim n and multidegree d, in projective space, generating function up to given degree B, in t-coordinates
  n:=L#0;
  d:=L#1;
  B:=L#2;  ----given bound of degree of monomials in t-coordinates
  R:=ringOfTCoordAndS n;
  F:=0;

  if d=={3} then 
    F=generatingFuncOfDegreeUpToBofCubicHypersurface {n,B};
  if not (d=={3}) then 
    F=generatingFuncOfDegreeUpToBNotCubic L;

  F
)





--The following are functions for quasi-exceptional complete intersections


correlatorCubicHypersurfaceInTauCoord0 =memoize(L->( 
    n:=L#0;
    d:={3};
    l:=L#1; --order of s, >=1
    I0:=L#2;  --number of insertions of each ambient class

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    if  Neg==0 then (
        f:=n-1;  --Fano index
      I:={};  
      Ijk:={};  
      S:=0;
      low:={};
      J:={};
      P:=1;
      S0:=0;
      S1:=0;
      S2:=0;
      S3:=0;
      S4:=0;
      T3:=0;
      i:=0;
          if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
          if l==2 then correl=correlatorOfSOrderTwoInTauCoord {n,d,I0};
          if l>=3 then (
             if  A==0 then (
              if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
              else (
                S0=0;
                for j from 2 to l-1 do (
                  P=binomial(l-1,j-1);
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,j,unitVector {n+1,1}});
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,l-j+1,unitVector {n+1,n-1}});
                  S0=S0+P;
                );
                for j from 1 to l-1 do 
                for a from 0 to n do
                for b from 0 to n do (
                  P=binomial(l-1,j);
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,j,unitVector({n+1,1})+unitVector({n+1,n-1})+unitVector({n+1,a})});
                  P=P*inversePairingInTauCoord({n,d,{a,b}});
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,l-j,unitVector({n+1,b})});
                  S0=S0-P;
                  );
                for j from 2 to l-1 do (
                  P=2*(l-1)*binomial(l-2,j-1);
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,j,unitVector({n+1,1})+unitVector({n+1,n-1})});
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,l-j+1,zeroVector(n+1)});
                  S0=S0-P;
                );
                S0=-S0/3;
                for j from 2 to l-1 do 
                for a from 0 to n do
                for b from 0 to n do (
                  P=1/2*binomial(l-1,j-1);
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,j,unitVector {n+1,a}});
                  P=P*inversePairingInTauCoord({n,d,{a,b}});
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,l+1-j,unitVector {n+1,b}});
                  S0=S0-P;
                  );
                for j from 3 to l-1 do (
                  P=(l-1)*binomial(l-2,j-2);
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,j,zeroVector(n+1)});
                  P=P*correlatorCubicHypersurfaceInTauCoord0({n,l+2-j,zeroVector(n+1)});
                  S0=S0-P;
                );
                correl=S0*(n-1)/(-3*l*n+12*l+3*n-21); 
                );
              )
             else if A>0 then (
              if I0#0>0 then correl=0
              else if I0#1 >0 then (
                I=I0- unitVector({n+1,1});
                S=0;
                for j from 0 to n do
                for k from 0 to n do (
                  Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                  S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorCubicHypersurfaceInTauCoord0({n,l,Ijk});
                  );
                S=S+(n*l-n+3-2*l)*correlatorCubicHypersurfaceInTauCoord0({n,l,I});
                correl=S/f; 
                )
              else if I0#1==0 then (
                S=0;
                P=1;
                i=(minPositiveIndex({I0,1}))#0;
                I=I0- unitVector({n+1,i});
                low=lowerLists(I);
                for j from 0 to #low-1 do (
                    J=low#j;
                    if (not J==zeroVector(n+1)) then (
                        S1=0;
                        for a from 0 to n do
                        for b from 0 to n do (
                          P=1;
                          P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                          P=P*inversePairingInTauCoord({n,d,{a,b}});
                          P=P*correlatorCubicHypersurfaceInTauCoord0({n,l,I-J+unitVector({n+1,b})});
                          S1=S1+P;
                          );
                    S=S-S1*binomOfLists({I,J}); 
                    );
                    
                    
                    S2=0;
                    for k from 1 to l do (
                      P=1;
                        P=P*correlatorCubicHypersurfaceInTauCoord0({n,k,J+unitVector({n+1,1})});
                        P=P*correlatorCubicHypersurfaceInTauCoord0({n,l-k+1,I-J+unitVector({n+1,i-1})});
                      S2=S2+P*binomial(l-1,k-1); 
                    );
                    S=S+S2*binomOfLists({I,J});
                    
                    S3=0;
                    for k from 1 to l-1 do (
                      T3=0;
                      for a from 0 to n do 
                      for b from 0 to n do (
                          P=1;
                          P=P*correlatorCubicHypersurfaceInTauCoord0({n,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                          P=P*inversePairingInTauCoord({n,d,{a,b}});
                          P=P*correlatorCubicHypersurfaceInTauCoord0({n,l-k,I-J+unitVector({n+1,b})});
                          T3=T3+P;
                          );
                      S3=S3+T3*binomial(l-1,k); 
                      );
                    S=S-S3*binomOfLists({I,J});

                  S4=0;
                  for k from 1 to l-1 do (
                    P=1;
                    P=P*correlatorCubicHypersurfaceInTauCoord0({n,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})});
                    P=P*correlatorCubicHypersurfaceInTauCoord0({n,l-k+1,I-J});
                    S4=S4+P*binomial(l-2,k-1);
                    );
                  S=S-S4*2*(l-1)*binomOfLists({I,J});
                    );
                  correl=S; 
                  );  
              );
            );
   
      );
    correl
)
)



correlatorCubicHypersurfaceInTauCoord =memoize(L->(             --use that when n=3, F^(4)(0)=0
    n:=L#0;
    d:={3};
    l:=L#1; --order of s, >=1
    I0:=L#2;  --number of insertions of each ambient class

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    if  Neg==0 then (
        f:=n-1;  --Fano index
      I:={};  
      Ijk:={};  
      S:=0;
      low:={};
      J:={};
      P:=1;
      S0:=0;
      S1:=0;
      S2:=0;
      S3:=0;
      S4:=0;
      T3:=0;
      i:=0;
          if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
          if l==2 then correl=correlatorOfSOrderTwoInTauCoord {n,d,I0};
          if l==4 and n==3 then correl=0;
          if l>=3 and not {n,l}=={3,4} then (
             if  A==0 then (
              if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
              else (
                S0=0;
                for j from 2 to l-1 do (
                  P=binomial(l-1,j-1);
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,j,unitVector {n+1,1}});
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,l-j+1,unitVector {n+1,n-1}});
                  S0=S0+P;
                );
                for j from 1 to l-1 do 
                for a from 0 to n do
                for b from 0 to n do (
                  P=binomial(l-1,j);
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,j,unitVector({n+1,1})+unitVector({n+1,n-1})+unitVector({n+1,a})});
                  P=P*inversePairingInTauCoord({n,d,{a,b}});
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,l-j,unitVector({n+1,b})});
                  S0=S0-P;
                  );
                for j from 2 to l-1 do (
                  P=2*(l-1)*binomial(l-2,j-1);
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,j,unitVector({n+1,1})+unitVector({n+1,n-1})});
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,l-j+1,zeroVector(n+1)});
                  S0=S0-P;
                );
                S0=-S0/3;
                for j from 2 to l-1 do 
                for a from 0 to n do
                for b from 0 to n do (
                  P=1/2*binomial(l-1,j-1);
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,j,unitVector {n+1,a}});
                  P=P*inversePairingInTauCoord({n,d,{a,b}});
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,l+1-j,unitVector {n+1,b}});
                  S0=S0-P;
                  );
                for j from 3 to l-1 do (
                  P=(l-1)*binomial(l-2,j-2);
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,j,zeroVector(n+1)});
                  P=P*correlatorCubicHypersurfaceInTauCoord({n,l+2-j,zeroVector(n+1)});
                  S0=S0-P;
                );
                correl=S0*(n-1)/(-3*l*n+12*l+3*n-21); 
                );
              )
             else if A>0 then (
              if I0#0>0 then correl=0
              else if I0#1 >0 then (
                I=I0- unitVector({n+1,1});
                S=0;
                for j from 0 to n do
                for k from 0 to n do (
                  Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                  S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorCubicHypersurfaceInTauCoord({n,l,Ijk});
                  );
                S=S+(n*l-n+3-2*l)*correlatorCubicHypersurfaceInTauCoord({n,l,I});
                correl=S/f; 
                )
              else if I0#1==0 then (
                S=0;
                P=1;
                i=(minPositiveIndex({I0,1}))#0;
                I=I0- unitVector({n+1,i});
                low=lowerLists(I);
                for j from 0 to #low-1 do (
                    J=low#j;
                    if (not J==zeroVector(n+1)) then (
                        S1=0;
                        for a from 0 to n do
                        for b from 0 to n do (
                          P=1;
                          P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                          P=P*inversePairingInTauCoord({n,d,{a,b}});
                          P=P*correlatorCubicHypersurfaceInTauCoord({n,l,I-J+unitVector({n+1,b})});
                          S1=S1+P;
                          );
                    S=S-S1*binomOfLists({I,J}); 
                    );
                    
                    
                    S2=0;
                    for k from 1 to l do (
                      P=1;
                        P=P*correlatorCubicHypersurfaceInTauCoord({n,k,J+unitVector({n+1,1})});
                        P=P*correlatorCubicHypersurfaceInTauCoord({n,l-k+1,I-J+unitVector({n+1,i-1})});
                      S2=S2+P*binomial(l-1,k-1); 
                    );
                    S=S+S2*binomOfLists({I,J});
                    
                    S3=0;
                    for k from 1 to l-1 do (
                      T3=0;
                      for a from 0 to n do 
                      for b from 0 to n do (
                          P=1;
                          P=P*correlatorCubicHypersurfaceInTauCoord({n,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                          P=P*inversePairingInTauCoord({n,d,{a,b}});
                          P=P*correlatorCubicHypersurfaceInTauCoord({n,l-k,I-J+unitVector({n+1,b})});
                          T3=T3+P;
                          );
                      S3=S3+T3*binomial(l-1,k); 
                      );
                    S=S-S3*binomOfLists({I,J});

                  S4=0;
                  for k from 1 to l-1 do (
                    P=1;
                    P=P*correlatorCubicHypersurfaceInTauCoord({n,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})});
                    P=P*correlatorCubicHypersurfaceInTauCoord({n,l-k+1,I-J});
                    S4=S4+P*binomial(l-2,k-1);
                    );
                  S=S-S4*2*(l-1)*binomOfLists({I,J});
                    );
                  correl=S; 
                  );  
              );
            );
   
      );
    correl
)
)



generatingFuncOfGivenSOrderInTauCoordUpToDegreeBofCubicHypersurface=method()
generatingFuncOfGivenSOrderInTauCoordUpToDegreeBofCubicHypersurface List:=L->(     --for cubic hypersurface of dim n, generating function of s-order l>=1 in tau-coordinates up to given degree B
  n:=L#0;
  --d:={3};
  l:=L#1;       ----order of s, >=1
  B:=L#2;       --given bound of degree of monomials
  R:=ringOfTauCoord n;
  S:=0; 
  M:={};
  P:=0;
  for i from 0 to B do (
    M=indexSet1({n+1,i});
    for j from 0 to #M-1 do (
      P=1;
      for k from 0 to n do 
        P=P*(tau_k_R)^(M#j#k);
      P=P/ellD(M#j);
      P=P*correlatorCubicHypersurfaceInTauCoord({n,l,M#j});
      S=S+P;
    );
  );
  S 
)



generatingFuncOfGivenSOrderInTCoordUpToDegreeBofCubicHypersurface=method()
generatingFuncOfGivenSOrderInTCoordUpToDegreeBofCubicHypersurface List:=L->(     --for cubic hypersurface of dim n, generating function of s-order l>=1 in t-coordinates up to given degree B
  n:=L#0;
  --d:={3};
  l:=L#1;                 ------order of s, >=1
  B:=L#2;                 --given bound of degree of monomials
  R:=ringOfTCoord n;
  f:={};
  
  S:=generatingFuncOfGivenSOrderInTauCoordUpToDegreeBofCubicHypersurface L;
  R0:=ring S;
    SUB:={};
    subk:=0;
    for k from 0 to n do (
      subk=0;
      for j from 0 to n do
        subk=subk+matrixCoeffM({n,{3},{j,k}})*t_j_R;
      SUB=append(SUB,subk);
      ); 
    f=map(R,R0,SUB);
    S=f(S);   
  S 
)




generatingFuncOfDegreeUpToBofCubicHypersurface=method()
generatingFuncOfDegreeUpToBofCubicHypersurface List:=L->(                 --for cubic hypersurface of dim n, generating function up to given degree B, in t-coordinates
  n:=L#0;
  --d:=L#1;
  B:=L#1;  
  R:=ringOfTCoordAndS n;

  B1:=floor (B/2);
  if odd n then (
    m:=dimPrimCoh {n,{3}};
    l:=lift(m/2,ZZ);
    B1=min {l,B1};     --in odd dimension, the natural bound given by skew symmetry of middle dim classes
    );

  S0:={1};
  for i from 1 to B1 do
    S0=append(S0,s_R^i/i!);
  M0:=transpose matrix {S0};

  S:={ambientGeneratingFuncOfDegreeUpToB {n,{3},B}};
  for i from 1 to B1 do
    S=append(S,generatingFuncOfGivenSOrderInTCoordUpToDegreeBofCubicHypersurface({n,i,B-2*i}));
  M1:=matrix {S};
  R1:=ring M1;

  gensR1:=drop(gens R,-1);   -- the list of generators {t_0,...,t_n} of R1
  f:=map(R,R1,gensR1);
  M1=f(M1);

  F:=flatten entries (M1*M0);
  F#0
)







correlatorOddDimIntTwoQuadricsInTauCoord =memoize(L->(              --correlators of odd dim (2,2) complete intersections, in tau coordinates
    n:=L#0;
    d:={2,2};
    l:=L#1; --order of s, >=1
    I0:=L#2;  --number of insertions of each ambient class

    correl:=0;
    A:=sum(I0);
    Neg:=0;
    for i from 0 to n do 
        if I0#i<0 then break (correl=0;
            Neg=1;
            );
    if  Neg==0 then (
        f:=n-1;  --Fano index
      I:={};  
      Ijk:={};  
      S:=0;
      low:={};
      J:={};
      P:=1;
      S0:=0;
      S1:=0;
      S2:=0;
      S3:=0;
      S4:=0;
      T3:=0;
      i:=0;
          if l==1 then correl=correlatorOfSOrderOneInTauCoord {n,d,I0};
          if l==2 then correl=correlatorOfSOrderTwoInTauCoord {n,d,I0};
          if l>=3 then (
             if  A==0 then (
              if (not (n*l-n+3-2*l)/f==floor((n*l-n+3-2*l)/f)) then correl=0
              else (
                S0=0;
                for j from 2 to l-1 do (
                  P=binomial(l-1,j-1);
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,j,unitVector {n+1,1}});
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l-j+1,unitVector {n+1,n-1}});
                  S0=S0+P;
                );
                for j from 1 to l-1 do 
                for a from 0 to n do
                for b from 0 to n do (
                  P=binomial(l-1,j);
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,j,unitVector({n+1,1})+unitVector({n+1,n-1})+unitVector({n+1,a})});
                  P=P*inversePairingInTauCoord({n,d,{a,b}});
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l-j,unitVector({n+1,b})});
                  S0=S0-P;
                  );
                for j from 2 to l-1 do (
                  P=2*(l-1)*binomial(l-2,j-1);
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,j,unitVector({n+1,1})+unitVector({n+1,n-1})});
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l-j+1,zeroVector(n+1)});
                  S0=S0-P;
                );
                S0=-S0/4;
                for j from 2 to l-1 do 
                for a from 0 to n do
                for b from 0 to n do (
                  P=1/2*binomial(l-1,j-1);
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,j,unitVector {n+1,a}});
                  P=P*inversePairingInTauCoord({n,d,{a,b}});
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l+1-j,unitVector {n+1,b}});
                  S0=S0-P;
                  );
                for j from 3 to l-1 do (
                  P=(l-1)*binomial(l-2,j-2);
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,j,zeroVector(n+1)});
                  P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l+2-j,zeroVector(n+1)});
                  S0=S0-P;
                );
                correl=S0*(n-1)/(4*l-8);  
                );
              )
             else if A>0 then (
              if I0#0>0 then correl=0
              else if I0#1 >0 then (
                I=I0- unitVector({n+1,1});
                S=0;
                for j from 0 to n do
                for k from 0 to n do (
                  Ijk=I+ unitVector({n+1,k})-unitVector({n+1,j});
                  S=S- EulerVectorFieldCoeff({n,d,j,k})*(I#j)*correlatorOddDimIntTwoQuadricsInTauCoord({n,l,Ijk});
                  );
                S=S+(n*l-n+3-2*l)*correlatorOddDimIntTwoQuadricsInTauCoord({n,l,I});
                correl=S/f; 
                )
              else if I0#1==0 then (
                S=0;
                P=1;
                i=(minPositiveIndex({I0,1}))#0;
                I=I0- unitVector({n+1,i});
                low=lowerLists(I);
                for j from 0 to #low-1 do (
                    J=low#j;
                    if (not J==zeroVector(n+1)) then (
                        S1=0;
                        for a from 0 to n do
                        for b from 0 to n do (
                          P=1;
                          P=P*ambientCorrelatorInTauCoord({n,d,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                          P=P*inversePairingInTauCoord({n,d,{a,b}});
                          P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l,I-J+unitVector({n+1,b})});
                          S1=S1+P;
                          );
                    S=S-S1*binomOfLists({I,J}); 
                    );
                    
                    
                    S2=0;
                    for k from 1 to l do (
                      P=1;
                        P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,k,J+unitVector({n+1,1})});
                        P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l-k+1,I-J+unitVector({n+1,i-1})});
                      S2=S2+P*binomial(l-1,k-1); 
                    );
                    S=S+S2*binomOfLists({I,J});
                    
                    S3=0;
                    for k from 1 to l-1 do (
                      T3=0;
                      for a from 0 to n do 
                      for b from 0 to n do (
                          P=1;
                          P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})+unitVector({n+1,a})});
                          P=P*inversePairingInTauCoord({n,d,{a,b}});
                          P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l-k,I-J+unitVector({n+1,b})});
                          T3=T3+P;
                          );
                      S3=S3+T3*binomial(l-1,k); 
                      );
                    S=S-S3*binomOfLists({I,J});

                  S4=0;
                  for k from 1 to l-1 do (
                    P=1;
                    P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,k,J+unitVector({n+1,1})+unitVector({n+1,i-1})});
                    P=P*correlatorOddDimIntTwoQuadricsInTauCoord({n,l-k+1,I-J});
                    S4=S4+P*binomial(l-2,k-1);
                    );
                  S=S-S4*2*(l-1)*binomOfLists({I,J});
                    );
                  correl=S; 
                  );  
              );
            );
   
      );
    correl
)
)









--The following are functions to compute quantum cohomology of even dimensional complete intersections of two quadrics

--allOneVector=method()
allOneVector =memoize(n->(           --produce a vector of length n with all components equal to 1
  V:={};
  for i from 0 to n-1 do
    V=append(V,1);
  V
)
)
--allOneVector=memoize allOneVector



--minNonZeroIndex=method()
minNonZeroIndex =memoize(L->(        --produce the smallest k nonzero indices, with multiplicity
  M:=L#0;
  n:=#M;
  S:={};
  k:=L#1;
  for j from 1 to k do (
  for i from 0 to n-1 do  
    if (not (M#i)==0) then break
      (S=append(S,i);
      M=M-unitVector({n,i});
      );
  );
  S
)
)
--minNonZeroIndex=memoize minNonZeroIndex


--indexTriple=method()
indexTriple =memoize(L->(            --produce the triple {a,b,c} in the the recursion equation abcc in  correlatorEvenIntersecTwoQuadricsRecursionInTauCoord
  l:=#L;
  n:=l-3;
  a:=-1;
  b:=-1;
  c:=-1;
  ab:={};
  M:={};
  sL:=sum L;
  if n>=3 and sL>4 and (not L==allOneVector(l)) and (not isVectorPureInOneDirection(L)) then (
    for i from 0 to l-1 do if (L#i)==0 then break c=i;
    if c>=0 then (
      a=(minPositiveIndex {L,1})#0;
      L=drop(L,{a,a});
      b=(minPositiveIndex {L,1})#0;
      if b>=a then
        b=b+1;
      )
    else (
      M=L- allOneVector(l)/((n-1)/(sL-4));
      c=(minNonZeroIndex {M,1})#0;
      if c==0 then (
        a=1;
        b=2
        )
      else if c==1 then (
        a=0;
        b=2;
        )
      else (
        a=1;
        b=2
      );  
    );  
  );
  {a,b,c} 
)
)
--indexTriple=memoize indexTriple




isVectorPureInOneDirection=method()
isVectorPureInOneDirection List:=L->(   --check whether a list of nonnegative integers, all components but one vanish
  l:=sum L;
  v:=false;
  for i from 0 to #L-1 do if L#i==l then break v=true;
  v
)



nonZeroComponents=method()
nonZeroComponents List:=L->(
  S:={};
  for i from 0 to #L-1 do 
    if (not L#i==0) then 
      S=append(S,L#i);
  S 
)


--ringOfVariablesEvenIntersecTwoQuadrics=method()
ringOfVariablesEvenIntersecTwoQuadrics =memoize(n->(
    R:=QQ[x,y_0..y_(2*n+3)];
    R
)
)
--ringOfVariablesEvenIntersecTwoQuadrics=memoize ringOfVariablesEvenIntersecTwoQuadrics






--correlatorEvenIntersecTwoQuadricsRecursionInTauCoord=method()                  
correlatorEvenIntersecTwoQuadricsRecursionInTauCoord =memoize(L->(             --correlators of length >=3, of even dim (2,2) complete intersections, in tau coordinates, using sort
  n:=L#0;
  I0:=L#1;
  R:=ringOfVariablesEvenIntersecTwoQuadrics n;
  lI0:=sum I0;
  I0amb:=I0_{0..n};
  J0:=I0_{(n+1)..(2*n+3)};
  lJ0:=sum J0;
  T1:=0;
  ab:={};
  a:=-1;
  b:=-1;
  c:=-1;
  ic:=0;
  SUB:={};
  I:={};
  J:={};
  lJ:=0;
  S:=0;
  S1:=0;
  S2:=0;
  S3:=0;
  S4:=0;
  S5:=0;
  S6:=0;
  S7:=0;
  S8:=0;
  S9:=0;
  S10:=0;
  S11:=0;
  S12:=0;
  P:=1;
  i:=0;
  correl:=0;
  beta:=0;
  I1:={};
  J1:={};
  for i from 0 to n do
    beta=beta+i*(I0#i);
  beta=beta+n/2*lJ0;
  beta=(beta-(n-3+lI0))/(n-1);
  if (not beta==floor(beta)) then correl=0
  else if  lJ0==0 then 
    correl=ambientCorrelatorInTauCoord {n,{2,2},I0amb}
  else if lJ0==1 then 
    correl=0
  else if lJ0==2 then (
    if isVectorPureInOneDirection(J0) then
      correl=correlatorOfSOrderOneInTauCoord {n,{2,2},I0amb}
    else correl=0;
    ) 
  else if lJ0==3 then 
    correl=0
  else if lI0==4 and lJ0==4 then (
    if nonZeroComponents(J0)=={4} or nonZeroComponents(J0)=={2,2}  then 
      correl=1
    else correl=0;
    )
  else  (
    if (I0#0)>=1 then 
      correl=0
    else if (I0#1)>=1 then (
      J1=sort J0;
      if (not J0==J1) then (
        I1=I0amb|J1;
        correl=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord {n,I1};
        )
      else (
        T1=0;
        for j from 0 to n do
          T1=T1+(j-1)*(I0#j);
        T1=T1+(n/2-1)*sum(J0)+3-n;
        correl=T1/(n-1)*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I0-unitVector({2*n+4,1})});
        if (I0#n)>0 then
          correl=correl-12*(I0#n)*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I0-unitVector({2*n+4,n})});
      );
      )
    else if lI0>lJ0 then (
      J1=sort J0;
      if (not J0==J1) then (
        I1=I0amb|J1;
        correl=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord {n,I1};
        )
      else (
        i=(minPositiveIndex {I0amb,1})#0;
        ab=minPositiveIndex {J0,2};
        a=n+1+ab#0;
        b=n+1+ab#1;
        I=I0-unitVector({2*n+4,i})-unitVector({2*n+4,a})-unitVector({2*n+4,b});
        S=0;
        if a==b then
          S=S+4*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I+unitVector({2*n+4,1})+unitVector({2*n+4,1})+unitVector({2*n+4,i-1})});
        SUB=lowerLists(I);
        for j from 0 to #SUB-1 do (
          J=SUB#j;
          lJ=sum J;
          S1=0;
          S2=0;
          S3=0;
          S4=0;
          if lJ>=1 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,i-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,a})+unitVector({2*n+4,b})});
              S1=S1+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,i-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,a})+unitVector({2*n+4,b})});
              S2=S2+P;
              );  
          );
          if lJ>=1 and lJ<=lI0-4 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,i-1})+unitVector({2*n+4,b})});
              S3=S3+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,i-1})+unitVector({2*n+4,b})});
              S4=S4+P;
              );  
          );
          S=S-(S1/4+S2)*binomOfLists({I,J})+(S3/4+S4)*binomOfLists({I,J});
        );
        correl=S;   
      );
    )   
    else if isVectorPureInOneDirection(J0) then (
      J1=sort J0;
      if (not J0==J1) then (
        I1=I0amb|J1;
        correl=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord {n,I1};
        )
      else (
        a=2*n+3;
        b=n+1;
        I=I0- unitVector({2*n+4,a})-unitVector({2*n+4,a});
        S=-((2*lJ0-8)/(n-1)-2*(lJ0-2))*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I+unitVector({2*n+4,b})+unitVector({2*n+4,b})});
        S=S-2*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I+unitVector({2*n+4,1})+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})});
        SUB=lowerLists(I);
        for j from 0 to #SUB-1 do (
          J=SUB#j;
          lJ=sum J;
          S1=0;
          S2=0;
          S3=0;
          S4=0;
          S5=0;
          S6=0;
          S7=0;
          S8=0;
          S9=0;
          S10=0;
          S11=0;
          S12=0;
          if lJ>=2 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,a})+unitVector({2*n+4,a})});
              S1=S1+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,a})+unitVector({2*n+4,a})});
              S2=S2+P;
              );  
          );
          if lJ>=1 and lJ<=lJ0-3 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,n-1})+unitVector({2*n+4,a})});
              S3=S3+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,n-1})+unitVector({2*n+4,a})});
              S4=S4+P;
              );  
          );
          if lJ>=2 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,b})+unitVector({2*n+4,b})});
              S5=S5+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,b})+unitVector({2*n+4,b})});
              S6=S6+P;
              );  
          );
          if lJ>=1 and lJ<=lJ0-3 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,b})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,n-1})+unitVector({2*n+4,b})});
              S7=S7+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,b})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,n-1})+unitVector({2*n+4,b})});
              S8=S8+P;
              );  
          );  
          if lJ>=2 and lJ<=lJ0-4 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,b})+unitVector({2*n+4,b})});
              S9=S9+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,b})+unitVector({2*n+4,b})});
              S10=S10+P;
              );  
          );  
          if lJ>=2 and lJ<=lJ0-4 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,b})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,a})+unitVector({2*n+4,b})});
              S11=S11+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,b})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,a})+unitVector({2*n+4,b})});
              S12=S12+P;
              );  
          );
          S=S+(S1/16+S2/4-S3/16-S4/4+S5/16+S6/4-S7/16-S8/4-S9/4-S10+S11/4+S12)*binomOfLists({I,J});
        );
        correl=S*(n-1)/(2*lJ0-8);
      );  
    )
    else if (not J0==allOneVector(n+3)) then (
      J1=sort J0;
      if (not J0==J1) then (
        I1=I0amb|J1;
        correl=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord {n,I1};
        )
      else (
        a=n+1+(indexTriple J0)#0;
        b=n+1+(indexTriple J0)#1;
        c=n+1+(indexTriple J0)#2;
        ic=I0#c;
        I=I0- unitVector({2*n+4,a})- unitVector({2*n+4,b});
        S=0;
        SUB=lowerLists(I);
        for j from 0 to #SUB-1 do (
          J=SUB#j;
          lJ=sum J;
          S1=0;
          S2=0;
          S3=0;
          S4=0;
          S5=0;
          S6=0;
          S7=0;
          S8=0;
          if lJ>=2 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,a})+unitVector({2*n+4,b})});
              S1=S1+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,n-1})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,a})+unitVector({2*n+4,b})});
              S2=S2+P;
              );  
          );
          if lJ>=1 and lJ<=lJ0-3 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,n-1})+unitVector({2*n+4,b})});
              S3=S3+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,1})+unitVector({2*n+4,a})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,n-1})+unitVector({2*n+4,b})});
              S4=S4+P;
              );  
          );
          if lJ>=2 and lJ<=lJ0-4 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,b})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,c})+unitVector({2*n+4,c})});
              S5=S5+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,b})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,c})+unitVector({2*n+4,c})});
              S6=S6+P;
              );  
          );  
          if lJ>=2 and lJ<=lJ0-4 then (
            for e from 0 to n do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,c})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,n-e})+unitVector({2*n+4,b})+unitVector({2*n+4,c})});
              S7=S7+P;
              );
            for e from n+1 to 2*n+3 do (
              P=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,J+unitVector({2*n+4,a})+unitVector({2*n+4,c})+unitVector({2*n+4,e})});
              P=P*correlatorEvenIntersecTwoQuadricsRecursionInTauCoord({n,I-J+unitVector({2*n+4,e})+unitVector({2*n+4,b})+unitVector({2*n+4,c})});
              S8=S8+P;
              );  
          );
          S=S+(S1/16+S2/4-S3/16-S4/4-S5/4-S6+S7/4+S8)*binomOfLists({I,J});
        );
        correl=S*(n-1)/(2*lJ0-8-2*ic*(n-1));
      );  
    )
    else if J0==allOneVector(n+3) then
      correl=x_R
  );
  correl
)
)
--correlatorEvenIntersecTwoQuadricsRecursionInTauCoord=memoize correlatorEvenIntersecTwoQuadricsRecursionInTauCoord




unknownInvInTermsOfSis=method()
unknownInvInTermsOfSis ZZ:=n->(         --with signs of invariants corrected
  S:=0;
  L:={};
  L1:={};
  T:={};
  Inv:=0;
  Mon:=1;
  P:=1;
  S1:=0;
  S2:=0;
  S3:=0;
  C:=0;
  M:={};
  lM:=0;
  N:={};
  M1:={};
  m:=lift (n/2,ZZ); 

  
  R:=QQ[z_(n+1)..z_(2*n+3)];
  for i from n+1 to 2*n+3 do 
      S1=S1+z_i_R;
  
  for i from n+1 to 3*m+4 do (
    S2=0;
    S3=0;
    for j from 0 to m-1 do (
      S2=S2+z_(i+j)_R;
      );
    S3=(-1)^m*(S1/2-S2);
    P=P*(1+S3);
  );
  for i from 3*m+5 to 4*m+3 do (
    S2=0;
    S3=0;
    for j from 0 to 4*m+3-i do 
      S2=S2+z_(i+j)_R;
    for j from 1 to i-3*m-4 do
      S2=S2+z_(n+j)_R;
    S3=(-1)^m*(S1/2-S2);
    P=P*(1+S3);
  );


  for i from 0 to m+1 do (
    l=2*i+1;
    L={};
    for j from 0 to m-1 do 
      L=append(L,0);
    L=append(L,l);
    for j from 0 to m-1 do 
      L=append(L,0);
    T=partitions (m+1-i);
    for k from 0 to #T-1 do (
      M=toList T#k;
      lM=#M;
      for j from 0 to n+3-lM-1 do
        M=append(M,0);
      L1=L;
      for j from n+1 to 2*n+3 do 
        L1=append(L1,2*(M#(j-n-1)));
      Inv=correlatorEvenIntersecTwoQuadricsRecursionInTauCoord {n,L1};
      M1:={};
      for i from 0 to #M-1 do 
        M1=append(M1,2*(M#i));
      C=extractCoeffOfSameType({P,M1})/(4^l);
      S=S+C*Inv*(-1)^(m*(m+1-i));     
    );
  );
  S
)



coefficientProductOfSisClass=method()
coefficientProductOfSisClass ZZ:=n->(
  Mon:=1;
  P:=1;
  S1:=0;
  S2:=0;
  S3:=0;
  
  m:=lift (n/2,ZZ); 

  
  R:=QQ[z_(n+1)..z_(2*n+3)];
  for i from n+1 to 2*n+3 do 
      S1=S1+z_i_R;
  
  for i from n+1 to 3*m+4 do (
    S2=0;
    S3=0;
    for j from 0 to m-1 do (
      S2=S2+z_(i+j)_R;
      );
    S3=(-1)^m*(S1/2-S2);
    P=P*S3;
  );
  for i from 3*m+5 to 4*m+3 do (
    S2=0;
    S3=0;
    for j from 0 to 4*m+3-i do 
      S2=S2+z_(i+j)_R;
    for j from 1 to i-3*m-4 do
      S2=S2+z_(n+j)_R;
    S3=(-1)^m*(S1/2-S2);
    P=P*S3;
  );

  for i from n+1 to 2*n+3 do 
    Mon=Mon*(z_i)_R;
  coefficient(Mon,P)
)




extractCoeffOfSameType=method()
extractCoeffOfSameType List:=L->(
  P:=L#0;
  M:=L#1;
  R:=ring P;
  G:=gens R;
  n:=#G;
  d:=sum M;
  I:=indexSet1 {n,d};
  S:=0;
  A:={};
  Mon:=1;

  for i from 0 to #I-1 do (
    A=sort I#i;
    if A==sort M then (
      Mon=1;
      for j from 0 to n-1 do
        Mon=Mon*((G#j)^(I#i#j));
      S=S+coefficient(Mon,P);
      );
    );
  S 
)




beginDocumentation()
multidoc ///
 Node
  Key
   QuantumCohomologyFanoCompleteIntersection
  Headline
     an example Macaulay2 package
  Description
   Text
    {\em QuantumCohomologyFanoCompleteIntersection} is a basic package to be used as an example.
  Caveat
    Still trying to figure this out.
 Node
  Key
   (fanoIndex,List)
   fanoIndex
   (zeroVector,ZZ)
   zeroVector
  Headline
   quantum cohomology
  Usage
   fanoIndex n
  Inputs
   n:
  Outputs
   :
    a silly string, depending on the value of {\tt n}
  Description
   Text
    Here we show an example.
   Example
    fanoIndex {5,{5}}
///

TEST ///
    assert ( fanoIndex {5,{5}} == "2" )
///

end--


