-- -*- coding: utf-8 -*-
newPackage(
  "ConicsOn4DimIntersectionOfTwoQuadrics",
      Version => "1.0", 
      Date => "Auguest 20, 2021",
      Authors => {{Name => "Xiaowen Hu", 
      Email => "huxw06@gmail.com", 
      HomePage => ""}},
      Headline => "find conics on 4 dimensional smooth complete intersections of two quadrics in P6",
      DebuggingMode => false
      )

export {"linearEqPluckerCoord","twoDimPlanes","syslinearEqsPluckerCoord","solveSyslinearEqsPluckerCoord","simpleEliminationExpressionOfAllVariables","noConicOnSIntersectingSelectedPlanes","planeOtherThanSMeetingSevenPlanes"}


needsPackage "PrimaryDecomposition"

ringOfPluckerCoord=method()
ringOfPluckerCoord  List:=L->(
    J:=Grassmannian (L#0,L#1);
    S:=(ring J_0)/J;
    S=S**QQ;
    I:=ideal S;
    R:=ring I;
    {R,I}
  )



R=getSymbol "R";
I=getSymbol "I";
p=getSymbol "p";

RI:=ringOfPluckerCoord {2,6};
R:=RI#0;
I:=RI#1;





linearEqPluckerCoord=method()
linearEqPluckerCoord List:=L->(
  S:=subsets (7,3);
  --P:={};
  --for i from 0 to #S-1 do 
  --  P=append(P,p_(S#i#0,S#i#1,S#i#2));
  --R:=QQ P;
  --R:=(ring (Grassmannian(2,6))_0)**QQ;
  --R:=(ringOfPluckerCoord {2,6})_0;
  --I:=(ringOfPluckerCoord {2,6})_1;


  Eqs:={};
  A:=0;
  M:={};
  M1:={};
  j0:=0;
  j1:=0;
  j2:=0;
  D:=0;



  for k from 0 to #L-1 do (
    A=0;
    M=matrix (L#k);
    for i from 0 to #S-1 do (
      M1=M^{1,2,3};
      M1=M1_(S#i);
      D=det M1;
      j0=S#i#0;
      j1=S#i#1;
      j2=S#i#2;
      A=A+(-1)^(j0+j1+j2)*D*p_(j0,j1,j2)_R;
      );
    Eqs=append(Eqs,A);
    
    A=0;
    for i from 0 to #S-1 do (
      M1=M^{0,2,3};
      M1=M1_(S#i);
      D=det M1;
      j0=S#i#0;
      j1=S#i#1;
      j2=S#i#2;
      A=A+(-1)^(j0+j1+j2)*D*p_(j0,j1,j2)_R;
      );
    Eqs=append(Eqs,A);  

    A=0;
    for i from 0 to #S-1 do (
      M1=M^{0,1,3};
      M1=M1_(S#i);
      D=det M1;
      j0=S#i#0;
      j1=S#i#1;
      j2=S#i#2;
      A=A+(-1)^(j0+j1+j2)*D*p_(j0,j1,j2)_R;
      );
    Eqs=append(Eqs,A);

    A=0;
    for i from 0 to #S-1 do (
      M1=M^{0,1,2};
      M1=M1_(S#i);
      D=det M1;
      j0=S#i#0;
      j1=S#i#1;
      j2=S#i#2;
      A=A+(-1)^(j0+j1+j2)*D*p_(j0,j1,j2)_R;
      );
    Eqs=append(Eqs,A);
  );

  Eqs
)


twoDimPlanes=method()
twoDimPlanes List:=L->(
  M:={};
  S:={};
  Mi:={};

  for i from 0 to 5 do (
    Mi={};
    for k from 0 to 3 do (
      S={};
      for j from 0 to i-1 do (
        S=append(S,(L#j)^k);
        );
      S=append(S,-(L#i)^k);
      S=append(S,-(L#(i+1))^k);


      for j from i+2 to 6 do (
        S=append(S,(L#j)^k);
        );
      Mi=append(Mi,S);  
    );
    M=append(M,Mi);
  );

  Mi={};
  for k from 0 to 3 do (
    S={-(L#0)^k};
    for j from 1 to 5 do (
      S=append(S,(L#j)^k);
      );
    S=append(S,-(L#6)^k);
    Mi=append(Mi,S);  
  );
  M=append(M,Mi);
  
  M
)


syslinearEqsPluckerCoord=method()
syslinearEqsPluckerCoord List:=L->(
  M:=twoDimPlanes L;
  Eqs:=linearEqPluckerCoord M;
  Eqs
)


simpleEliminationExpressionOfAllVariables=method()
simpleEliminationExpressionOfAllVariables List:=L->(
  I0:=ideal(L#1);
  l:=#(L#0);
  A:=L#0;
  C:=L#0;
  MC:=transpose matrix vector C;
  J:={};
  for i from 0 to l-1 do
    for j from 0 to #(I0_*)-1 do
      if diff(L#0#(l-1-i),(I0_*)#j)!=0 
    and isConstant diff(L#0#(l-1-i),(I0_*)#j)
         then (
          MC=sub(MC,{L#0#(l-1-i)=>L#0#(l-1-i)-(I0_*)#j/coefficient(L#0#(l-1-i),(I0_*)#j)});
          I0=sub(I0,{L#0#(l-1-i)=>L#0#(l-1-i)-(I0_*)#j/coefficient(L#0#(l-1-i),(I0_*)#j)});
          A=drop(A,{(l-1-i),(l-1-i)});
          J=append(J,l-1-i);
        );
  C=flatten entries MC;
  D:={};
  for i from 0 to #J-1 do
    D=append(D,L#0#(J#(#J-1-i))=>C#(J#(#J-1-i)));   
  {A,I0,D}     
)


solveSyslinearEqsPluckerCoord=method()
solveSyslinearEqsPluckerCoord List:=L->(
    sys:=syslinearEqsPluckerCoord L;
    PlC:=gens ring sys_0;
    simpleEliminationExpressionOfAllVariables {PlC,sys}
)


defEqsOfS=method()
defEqsOfS List:=L->(
    M:={};
    M=M|{{1,1,1,1,1,1,1}};
    M=M|{{L_0,L_1,L_2,L_3,L_4,L_5,L_6}};
    M=M|{{(L_0)^2,(L_1)^2,(L_2)^2,(L_3)^2,(L_4)^2,(L_5)^2,(L_6)^2}};
    M=M|{{(L_0)^3,(L_1)^3,(L_2)^3,(L_3)^3,(L_4)^3,(L_5)^3,(L_6)^3}};
    M
)



noConicOnSIntersectingSelectedPlanes=method()                                               --check if there is no conic on S that intersecting S_{i,i+1} for 0<=i<=6
noConicOnSIntersectingSelectedPlanes List:=L->(
  M:={};
  T:=0;
  M=append(M,{L_0^2*L_1^2, (-L_0 - L_1)^2, 1, L_0*(-L_0 - L_1)*L_1, L_0*L_1, -L_0 - L_1});
  M=append(M,{L_1^2*L_2^2, (-L_1 - L_2)^2, 1, L_1*(-L_1 - L_2)*L_2, L_1*L_2, -L_1 - L_2}); 
  M=append(M,{L_2^2*L_3^2, (-L_2 - L_3)^2, 1, L_2*(-L_2 - L_3)*L_3, L_2*L_3, -L_2 - L_3});
  M=append(M,{L_3^2*L_4^2, (-L_3 - L_4)^2, 1, L_3*(-L_3 - L_4)*L_4, L_3*L_4, -L_3 - L_4}); 
  M=append(M,{L_4^2*L_5^2, (-L_4 - L_5)^2, 1, L_4*(-L_4 - L_5)*L_5, L_4*L_5, -L_4 - L_5}); 
  M=append(M,{L_5^2*L_6^2, (-L_5 - L_6)^2, 1, L_5*(-L_5 - L_6)*L_6, L_5*L_6, -L_5 - L_6});
  M=append(M,{L_0^2*L_6^2, (-L_0 - L_6)^2, 1, L_0*(-L_0 - L_6)*L_6, L_0*L_6, -L_0 - L_6});
  rk:=rank matrix M;
  if rk==6 then T=true else T=false;
  T
)


planeOtherThanSMeetingSevenPlanes=method()
planeOtherThanSMeetingSevenPlanes List:=L->(
    --S:=ringOfPluckerCoord {2,6};
    --R:=S#0;
    --I:=S#1;
    --use R;
    A:={};
    if not (noConicOnSIntersectingSelectedPlanes L) then (print "there exists conics on S that intersects all S_{i,i+1}")
    else (
    M:={};

    sys:=syslinearEqsPluckerCoord L;
    sol:=solveSyslinearEqsPluckerCoord L;

    
    M0:={};
    M0=append(M0,{p_(1,2,3)_R,p_(0,2,3)_R,p_(0,1,3)_R,p_(0,1,2)_R,0,0,0});
    M0=append(M0,{-p_(1,2,4)_R,-p_(0,2,4)_R,-p_(0,1,4)_R,0,p_(0,1,2)_R,0,0});
    M0=append(M0,{p_(1,2,5)_R,p_(0,2,5)_R,p_(0,1,5)_R,0,0,p_(0,1,2)_R,0});
    M0=append(M0,{-p_(1,2,6)_R,-p_(0,2,6)_R,-p_(0,1,6)_R,0,0,0,p_(0,1,2)_R});
    M0=matrix M0;
    
    rk:=0;


    
    Isub:=sub(I,sol_2);
    Planes:=primaryDecomposition ideal flatten entries gens gb Isub;
    numOfPlanes:=#(Planes)-1;

    for i from 0 to numOfPlanes-1 do (
        solPlEq:=simpleEliminationExpressionOfAllVariables {gens R,sys|(Planes_i_*)};
        if solPlEq_0=={(gens R)_0} then (
            M= sub(sub(M0,solPlEq_2),{p_(0,1,2)_R=>1});
           rk=rank (M||(matrix defEqsOfS L));
            if rk>4 then 
               A=append(A,M);
          )
        else  (print "p_(0,1,2) vanishes");
      );
      );
   A   
)






beginDocumentation()
multidoc ///
 Node
  Key
   ConicsOn4DimIntersectionOfTwoQuadrics
  Headline
     a Macaulay2 package
  Description
   Text
    {\em ConicsOn4DimIntersectionOfTwoQuadrics} is a basic package to be used as an example.
  Caveat
    Still trying to figure this out.
 Node
  Key
   (syslinearEqsPluckerCoord,List)
   syslinearEqsPluckerCoord
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
    assert ( syslinearEqsPluckerCoord {1,2,3,4,5,6,7} == "2" )
///

end--


