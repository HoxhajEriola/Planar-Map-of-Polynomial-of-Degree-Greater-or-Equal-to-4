

--    This program is free software: you can redistribute it and/or modify
--   it under the terms of the GNU General Public License as published by
--   the Free Software Foundation, either version 3 of the License, or
--   (at your option) any later version.

--    This program is distributed in the hope that it will be useful,
--   but WITHOUT ANY WARRANTY; without even the implied warranty of
--   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--   GNU General Public License for more details.

--    You should have received a copy of the GNU General Public License
--   along with this program.  If not, see <http://www.gnu.org/licenses/>.


--"This file contains interactive macaulay2 code for computing";
--"  planar map of polynomial of degree grater then three";




-- Program package for computing a map with given discriminant

-- global settings


needsPackage "Elimination"
needsPackage "FastMinors"
needsPackage "RationalMaps"

k=ZZ/32003;
P2=k[s,t,u];  
RC=k[y,z,w];
RDC=k[s,t,u,y,z,w];

--------------------------------------------------------------------------------


AdIdeal = (B) -> (
--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--OUTPUT: the  adjoint ideal which is equal to the ideal of  the singular locus
--(jacobian ideal)



  use RC;
  J := jacobian(ideal(B)); 
  JI := B+minors(1,J);
   
  Iy := eliminate(JI,y);
  Iz := eliminate(JI,z);
  Iw := eliminate(JI,w);
  A := JI+radical(Iy)+radical(Iz)+radical(Iw);
 I:= saturate(A,ideal(y));
 I
)

--------------------------------------------------------------------------------


--time B=AdIdeal(B);  --used 200.621 seconds 


--------------------------------------------------------------------------------


LNormalize = (B) -> (

--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--First find the adjoint ideal and pick a form of degree less then deg(B)
--then compute the quotient ideal as in the Theorem in the paper.
--OUTPUT: map finding the linear normalization

  A := AdIdeal(B);  
  denom := A_0;
  l := first degree(denom);    
  Q1:=ideal(B,denom);
  Q := Q1:A ;      
  L1:={Q_0};
 
  for i from 0 to (numgens Q)-1 do (
    if first degree Q_i  == l+1 then
      L1 = append(L1,Q_i) 
  );

  L2:=drop(L1,1);
  g:={Q_0};
  L:= join (y*g,z*g,w*g,L2);
  
  QR = RC/ideal(B);
 
  Rbig = k[x_0..x_(#L-1)]; 
  psi:=map(QR,Rbig,L);
  psi
)

---------------------------------------------------------------------------------------------------------------------


--time LNormalize (B);   --used 220.6 seconds


--------------------------------------------------------------------------------------------------------------------

DegPolMp =(B) ->(

--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--Express d depending on the degree of B and see the condition that 
--it should fulfill.
--OUTPUT: d the degree of polnomials that will define the planar map


     a:= first degree(B);  
    a1:=sqrt(a/3+1/4)+1/2;         
    if a1==floor a1 then a1=floor a1 else error "it is not a branching locus";
    d:=lift(a1,ZZ);
    d
)    

--------------------------------------------------------------------------------


--time DegPolMp(B)  --used 0.0004 seconds


--------------------------------------------------------------------------------


Veronese=(B)->(

---INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--First we find the linear normalization of the curve B, B~ denoted imB
--then we take all the quadratic forms in the ideal of linear normalization.
--OUTPUT: the defining ideal of the Veronese surface having only quadratic forms.
  
    psi:= LNormalize B;
    
    h:=DegPolMp(B);

    p:=hilbertFunction(2*h,RC);

    I:=ideal basis ({2},Rbig);
    QR = RC/ideal(B);
    
    r:=first degree(B);
    J:=ideal basis (2*(r-3),QR);
     
    use QR;
    
    PsiI=substitute(psi I,QR);
   
    N:=(gens PsiI)//(gens J); 
    N1:=substitute(N,ZZ/32003);
  
    g:=getSubmatrixOfRank(p,N1, Strategy=>StrategyRandom);
    LstRnk:=for i from 0 to #g#0-1 list substitute(g#0_i,ZZ);
    M:=N1^LstRnk;

    A:=substitute(gens ker M,Rbig);
    V:=ideal((gens I)*A);
    V
)      
    
--------------------------------------------------------------------------------


--time Veronese (B)    --used 228.769 seconds


--------------------------------------------------------------------------------


PointVeronese=(B)->(

--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--First we compute the defining ideal of the Veronese surface, then we cut the
--surface with a linear space. 
--OUTPUT: the maximal ideal of one point in Veronese surface
    
    V:= Veronese(B);

    found=false;
    use Rbig;
    while not found do(
    l1:=random(1,Rbig);
    l2:=random(1,Rbig);
    ln:=ideal(l1,l2);

    J:=V+ln;
    
    e:=entries vars Rbig;
    L:=drop(e#0,2);
    
   J1:=eliminate(J,L);
   Pr:=primaryDecomposition J1;
   
   if degree(Pr_0)==1 then found=true);
   M:=Pr_0+J ;
   M
)
 
--------------------------------------------------------------------------------


--time P= PointVeronese(B)      --used 233.461 
  
  
--------------------------------------------------------------------------------   
   

OsculatingSpaces = (B) ->(

--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--We compute a Veronese surface and a point on it, 
--then we compute 2nd &3rd osculating spaces on that point. 
--OUTPUT: the definig ideal of 2nd & 3rd osculating spaces

      V:=Veronese(B);
      M:=PointVeronese(B);
      Vn:=sub(V,Rbig);
      
      E:=(entries vars Rbig)#0;
      
     Vaff:=ideal gens gb sub(Vn,{E_(#E-1)=>1});                
     Maff:=ideal gens gb sub (M,{E_(#E-1)=>1});
     
     t:=DegPolMp(B1);
     t1:=t-1;
     Osc1:=ideal gens gb (Maff^t+Vaff);    
     Osc2:=ideal gens gb (Maff^t1+Vaff);           

    Lst1:=for i from 0 to (numgens(Osc1)-1) list  Osc1_i;
    L1:=select(Lst1, a ->degree a == {1}); 
    
    Lst2:=for i from 0 to (numgens(Osc2)-1) list  Osc2_i;
    L2:=select(Lst2, b ->degree b == {1}); 
    
    V1:= ideal L1;
    V2:= ideal L2;
    
   V1,V2
    
    )
    
--------------------------------------------------------------------------------


--time OsculatingSpaces(B1)    --458.746 seconds


--------------------------------------------------------------------------------

ParametrizationVeronese=(B) -> (

--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--First we apply twice the function for finding the 2nd & 3rd osculating space
--at the Veronese surface containing the linear normalization of the curve B.
--Next we intersect the osculating spaces of different points with different
-- order. Then we collect the linear forms of these intersections. After that we
--take minimal generators of the union of these linear forms. The basis of the
--last vector space of the union  define a rational map from Veronese 
--to the plane, and then find its inverse which is exactly the parametrization.
--OUTPUT: the parametrization of the Veronese surface.

      (V3,V4):=OsculatingSpaces(B);
      (V5,V6):=OsculatingSpaces(B);
    
      v3:=sub(V3,Rbig);
      v4:=sub(V4,Rbig);
      v5:=sub(V5,Rbig);
      v6:=sub(V6,Rbig);
     
      i1:=intersect(v3,v6);
      A1:= for i from 0 to numgens(i1)-1 list i1_i;
      A:=select(A1,f-> degree f=={1});
     
      i2:=intersect(v4,v5);
      C1:= for i from 0 to numgens(i2)-1 list i2_i;
      C:=select(C1,g-> degree g=={1});
     
      I1:=ideal A;
      I2:=ideal C;
      
      I:=trim(I1+I2);
      
      L:=(entries vars Rbig)#0;
       
      J:=homogenize(I,L_(#L-1));
      V:=Veronese(B1);
      RV:=Rbig/V;
      
      j1:=sub(J_0,Rbig);
      j2:=sub(J_1,Rbig);
      j3:=sub(J_2,Rbig);
      
      q:=map(RV,P2,{j1,j2,j3});
  
      InversE:=inverseOfMap q;
      
    InversE
      )
      
--------------------------------------------------------------------------------

--time ParametrizationVeronese(B) --1198 sec

-------------------------------------------------------------------------------

PlanarMap=(B)->(

--INPUT: the definig polynomial of a planar curve B whose singularities are nodes or cusps 
-- and the degree can be factored as 3d(d-1).
--The first step is finding the parametrization of the Veronese surface
--where the linear normalization of the curve B lies.
--The next step is to compose this parametrization with a random
--projection to a plane. 

--OUTPUT: a planar map such that the curve B is ist branching curve.    
       
       Par:=ParametrizationVeronese(B);
       Parm:=matrix map Par;
       
       Entr := entries Parm;
       f1:=factor(Entr#0#0);
       f2:=factor(Entr#0#1);
       com := gcd(Entr#0#0,Entr#0#1);
       
       ParSimp := apply(Entr#0, i->(quotientRemainder(i,com))#0);
       RndLstParSimp:=random(ParSimp);
       ParProj:=take(RndLstParSimp,3);
      PlanarMap:=map(P2,RC,ParProj)
       
       )

--------------------------------------------------------------------------------


time PlanarMap(B) --1163 sec

