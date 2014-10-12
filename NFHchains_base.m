(* ::Package:: *)

(* Mathematica Package *)

(* :Author: Christian B. Mendl
	http://christian.mendl.net *)

(* :Copyright:
	Copyright (C) 2013-2014, Christian B. Mendl
	All rights reserved.
	This program is free software; you can redistribute it and/or
	modify it under the terms of the Simplified BSD License
	http://www.opensource.org/licenses/bsd-license.php
*)

(* :Summary:
	This package computes the coupling constants in Appendix A of Ref [1]
	and additionally takes the average mass into account.
*)

(* :References:
	[1] Herbert Spohn
	Nonlinear fluctuating hydrodynamics for anharmonic chains
	J. Stat. Phys. 154, 1191-1227 (2014), arXiv:1305.6412

	[2] Christian B. Mendl, Herbert Spohn
	Dynamic correlators of Fermi-Pasta-Ulam chains and nonlinear fluctuating hydrodynamics
	Phys. Rev. Lett. 111, 230601 (2013), arXiv:1305.1209

	[3] Christian B. Mendl, Herbert Spohn
	Equilibrium time-correlation functions for one-dimensional hard-point systems
	Phys. Rev. E 90, 012147 (2014), arXiv:1403.0213
*)


(* general definitions of cumulants *)

(* dynamic programming *)
CalculateAverage[f_,{V_,p_,\[Beta]_},sym_]:=CalculateAverage[f,{V,p,\[Beta]},sym]=
	If[sym,(* symbolic version *)
		 Integrate[f[x]Exp[-\[Beta](V[x]+p x)],{x,-\[Infinity],\[Infinity]}]/Integrate[Exp[-\[Beta](V[x]+p x)],{x,-\[Infinity],\[Infinity]}],
		NIntegrate[f[x]Exp[-\[Beta](V[x]+p x)],{x,-\[Infinity],\[Infinity]}]/NIntegrate[Exp[-\[Beta](V[x]+p x)],{x,-\[Infinity],\[Infinity]}]]


(* cumulants of order 2 *)
CalculateCumulant2[f1_,f2_,Vp\[Beta]_,sym_]:=CalculateAverage[f1[#]f2[#]&,Vp\[Beta],sym]-CalculateAverage[f1,Vp\[Beta],sym]CalculateAverage[f2,Vp\[Beta],sym]

(* cumulants of order 3 *)
CalculateCumulant3[f1_,f2_,f3_,Vp\[Beta]_,sym_]:=Module[{
	a123=CalculateAverage[f1[#]f2[#]f3[#]&,Vp\[Beta],sym],
	a12=CalculateAverage[f1[#]f2[#]&,Vp\[Beta],sym],
	a13=CalculateAverage[f1[#]f3[#]&,Vp\[Beta],sym],
	a23=CalculateAverage[f2[#]f3[#]&,Vp\[Beta],sym],
	a1=CalculateAverage[f1,Vp\[Beta],sym],
	a2=CalculateAverage[f2,Vp\[Beta],sym],
	a3=CalculateAverage[f3,Vp\[Beta],sym]},
		Simplify[a123-(a1 a23+a2 a13+a3 a12)+2a1 a2 a3]]


(* equilibrium covariance matrix *)

Cov[{V_,p_,\[Beta]_,m_:1},sym_:False]:={{CalculateCumulant2[#&,#&,{V,p,\[Beta]},sym],0,CalculateCumulant2[#&,V,{V,p,\[Beta]},sym]},{0,m/\[Beta],0},{CalculateCumulant2[#&,V,{V,p,\[Beta]},sym],0,1/(2\[Beta]^2)+CalculateCumulant2[V,V,{V,p,\[Beta]},sym]}}


(* mean length and derivatives with respect to pressure p and inverse temperature \[Beta] *)

ell[Vp\[Beta]_,sym_:False]:=CalculateAverage[#&,Vp\[Beta],sym]

dpell[{V_,p_,\[Beta]_},sym_:False]:=-\[Beta] CalculateCumulant2[#&,#&,{V,p,\[Beta]},sym]
d\[Beta]ell[{V_,p_,\[Beta]_},sym_:False]:=-CalculateCumulant2[#&,V[#]+p #&,{V,p,\[Beta]},sym]

d2\[Beta]ell[{V_,p_,\[Beta]_},sym_:False]:=CalculateCumulant3[#&,V[#]+p #&,V[#]+p #&,{V,p,\[Beta]},sym]

d\[Beta]dpell[{V_,p_,\[Beta]_},sym_:False]:=-CalculateCumulant2[#&,#&,{V,p,\[Beta]},sym]+\[Beta] CalculateCumulant3[#&,#&,V[#]+p #&,{V,p,\[Beta]},sym]


(* mean energy and derivatives with respect to pressure p and inverse temperature \[Beta] *)

En[{V_,p_,\[Beta]_},sym_:False]:=1/(2\[Beta])+CalculateAverage[V,{V,p,\[Beta]},sym]

dpEn[{V_,p_,\[Beta]_},sym_:False]:=-\[Beta] CalculateCumulant2[#&,V,{V,p,\[Beta]},sym]
d\[Beta]En[{V_,p_,\[Beta]_},sym_:False]:=-1/(2\[Beta]^2)-CalculateCumulant2[V[#]+p #&,V,{V,p,\[Beta]},sym]

d2\[Beta]En[{V_,p_,\[Beta]_},sym_:False]:=1/\[Beta]^3+CalculateCumulant3[V[#]+p #&,V[#]+p #&,V,{V,p,\[Beta]},sym]

d\[Beta]dpEn[{V_,p_,\[Beta]_},sym_:False]:=-CalculateCumulant2[#&,V,{V,p,\[Beta]},sym]+\[Beta] CalculateCumulant3[#&,V,V[#]+p #&,{V,p,\[Beta]},sym]


(* determinant \[CapitalGamma] and derivatives with respect to pressure p and inverse temperature \[Beta] *)

\[CapitalGamma][{V_,p_,\[Beta]_},sym_:False]:=Module[{
	c2xx=CalculateCumulant2[#&,#&,{V,p,\[Beta]},sym],
	c2VV=CalculateCumulant2[V,V,{V,p,\[Beta]},sym],
	c2xV=CalculateCumulant2[#&,V,{V,p,\[Beta]},sym]},
		Simplify[\[Beta](c2xx c2VV-c2xV^2)+1/(2\[Beta]) c2xx]]

d\[Beta]\[CapitalGamma][{V_,p_,\[Beta]_},sym_:False]:=Module[{
	c2xx=CalculateCumulant2[#&,#&,{V,p,\[Beta]},sym],
	c2VV=CalculateCumulant2[V,V,{V,p,\[Beta]},sym],
	c2xV=CalculateCumulant2[#&,V,{V,p,\[Beta]},sym],
	c3xxVpx=CalculateCumulant3[#&,#&,V[#]+p #&,{V,p,\[Beta]},sym],
	c3xVVpx=CalculateCumulant3[#&,V,V[#]+p #&,{V,p,\[Beta]},sym],
	c3VVVpx=CalculateCumulant3[V,V,V[#]+p #&,{V,p,\[Beta]},sym]},
		(c2xx c2VV-c2xV^2)-1/(2\[Beta]^2) c2xx+\[Beta](-c3xxVpx c2VV-c2xx c3VVVpx+2c2xV c3xVVpx)-1/(2\[Beta]) c3xxVpx]

dp\[CapitalGamma][{V_,p_,\[Beta]_},sym_:False]:=Module[{
	c2xx=CalculateCumulant2[#&,#&,{V,p,\[Beta]},sym],
	c2VV=CalculateCumulant2[V,V,{V,p,\[Beta]},sym],
	c2xV=CalculateCumulant2[#&,V,{V,p,\[Beta]},sym],
	c3xxx=CalculateCumulant3[#&,#&,#&,{V,p,\[Beta]},sym],
	c3VVx=CalculateCumulant3[V,V,#&,{V,p,\[Beta]},sym],
	c3xVx=CalculateCumulant3[#&,V,#&,{V,p,\[Beta]},sym]},
		\[Beta](-\[Beta] c3xxx c2VV-\[Beta] c2xx c3VVx+2\[Beta] c2xV c3xVx)-1/2 c3xxx]


(* derivatives of pressure p with respect to mean length and energy *)

dellp[Vp\[Beta]_,sym_:False]:=1/\[CapitalGamma][Vp\[Beta],sym] d\[Beta]En[Vp\[Beta],sym]

denp[Vp\[Beta]_,sym_:False]:=-1/\[CapitalGamma][Vp\[Beta],sym] d\[Beta]ell[Vp\[Beta],sym]

  d2ellp[Vp\[Beta]_,sym_:False]:=-1/\[CapitalGamma][Vp\[Beta],sym]^2 (  dpEn[Vp\[Beta],sym]d2\[Beta]En[Vp\[Beta],sym] - d\[Beta]En[Vp\[Beta],sym] d\[Beta]dpEn[Vp\[Beta],sym])+1/\[CapitalGamma][Vp\[Beta],sym]^3 (  dpEn[Vp\[Beta],sym] d\[Beta]En[Vp\[Beta],sym]d\[Beta]\[CapitalGamma][Vp\[Beta],sym]- d\[Beta]En[Vp\[Beta],sym]^2 dp\[CapitalGamma][Vp\[Beta],sym])
dendellp[Vp\[Beta]_,sym_:False]:=-1/\[CapitalGamma][Vp\[Beta],sym]^2 ( -dpEn[Vp\[Beta],sym]d2\[Beta]ell[Vp\[Beta],sym]+ d\[Beta]En[Vp\[Beta],sym]d\[Beta]dpell[Vp\[Beta],sym])+1/\[CapitalGamma][Vp\[Beta],sym]^3 ( -dpEn[Vp\[Beta],sym]d\[Beta]ell[Vp\[Beta],sym]d\[Beta]\[CapitalGamma][Vp\[Beta],sym]+ d\[Beta]En[Vp\[Beta],sym]d\[Beta]ell[Vp\[Beta],sym]dp\[CapitalGamma][Vp\[Beta],sym])
   d2enp[Vp\[Beta]_,sym_:False]:= 1/\[CapitalGamma][Vp\[Beta],sym]^2 (-dpell[Vp\[Beta],sym]d2\[Beta]ell[Vp\[Beta],sym]+d\[Beta]ell[Vp\[Beta],sym]d\[Beta]dpell[Vp\[Beta],sym])-1/\[CapitalGamma][Vp\[Beta],sym]^3 (-d\[Beta]ell[Vp\[Beta],sym]dpell[Vp\[Beta],sym]d\[Beta]\[CapitalGamma][Vp\[Beta],sym]+d\[Beta]ell[Vp\[Beta],sym]^2 dp\[CapitalGamma][Vp\[Beta],sym])


(* A matrix (linearization at u==0) *)

A[{V_,p_,\[Beta]_,m_:1},sym_:False]:={{0,-1/m,0},{dellp[{V,p,\[Beta]},sym],0,denp[{V,p,\[Beta]},sym]},{0,p/m,0}}


(* sound velocity *)

(* squared sound velocity for m==1 *)
csq1[{V_,p_,\[Beta]_},sym_:False]:=1/\[CapitalGamma][{V,p,\[Beta]},sym] (1/(2\[Beta]^2)+CalculateCumulant2[V[#]+p #&,V[#]+p #&,{V,p,\[Beta]},sym])

(* actual squared sound velocity, taking average mass 'm' into account *)
csq[{V_,p_,\[Beta]_,m_:1},sym_:False]:=csq1[{V,p,\[Beta]},sym]/m


(* rotation matrix R *)

(* Z normalization factors (turn out to be independent of mass) *)
Ztilde[0,Vp\[Beta]_,sym_:False]:=Sqrt[csq1[Vp\[Beta],sym] \[CapitalGamma][Vp\[Beta],sym]]
Ztilde[\[Sigma]_,{V_,p_,\[Beta]_},sym_:False]:=Sqrt[2/\[Beta] csq1[{V,p,\[Beta]},sym]]

Z[0,Vp\[Beta]_,sym_:False]:=Sqrt[csq1[Vp\[Beta],sym]/\[CapitalGamma][Vp\[Beta],sym]]
Z[\[Sigma]_,{V_,p_,\[Beta]_},sym_:False]:=Sqrt[2\[Beta] csq1[{V,p,\[Beta]},sym]]

R[{V_,p_,\[Beta]_,m_:1},sym_:False]:={
	1/Ztilde[-1,{V,p,\[Beta]},sym]{dellp[{V,p,\[Beta]},sym],-Sqrt[csq[{V,p,\[Beta],m},sym]],denp[{V,p,\[Beta]},sym]},
	1/Ztilde[ 0,{V,p,\[Beta]},sym]{p,                   0,                       1                 },
	1/Ztilde[ 1,{V,p,\[Beta]},sym]{dellp[{V,p,\[Beta]},sym], Sqrt[csq[{V,p,\[Beta],m},sym]],denp[{V,p,\[Beta]},sym]}}

Rinv[{V_,p_,\[Beta]_,m_:1},sym_:False]:=Transpose[{
	1/Z[-1,{V,p,\[Beta]},sym]{-1,                -Sqrt[csq[{V,p,\[Beta],m},sym]]m, p                  },
	1/Z[ 0,{V,p,\[Beta]},sym]{denp[{V,p,\[Beta]},sym], 0,                         -dellp[{V,p,\[Beta]},sym]},
	1/Z[ 1,{V,p,\[Beta]},sym]{-1,                 Sqrt[csq[{V,p,\[Beta],m},sym]]m, p                  }}]


(* H matrix elements transformed to normal modes (averages with respect to \[Psi] vectors) *)

Hell[\[Sigma]_,\[Tau]_,Vp\[Beta]_,sym_:False]:=0

(* Hu is independent of mass *)
Hu[0,0,Vp\[Beta]_,sym_:False]:=1/Z[0,Vp\[Beta],sym]^2 (d2ellp[Vp\[Beta],sym]denp[Vp\[Beta],sym]^2-2dendellp[Vp\[Beta],sym]dellp[Vp\[Beta],sym]denp[Vp\[Beta],sym]+d2enp[Vp\[Beta],sym]dellp[Vp\[Beta],sym]^2)
Hu[0,\[Sigma]_,{V_,p_,\[Beta]_},sym_:False]:=1/(Z[0,{V,p,\[Beta]},sym]Z[\[Sigma],{V,p,\[Beta]},sym]) (-d2ellp[{V,p,\[Beta]},sym]denp[{V,p,\[Beta]},sym]-p d2enp[{V,p,\[Beta]},sym]dellp[{V,p,\[Beta]},sym]+p dendellp[{V,p,\[Beta]},sym]denp[{V,p,\[Beta]},sym]+dendellp[{V,p,\[Beta]},sym]dellp[{V,p,\[Beta]},sym])
Hu[\[Sigma]_,0,Vp\[Beta]_,sym_:False]:=Hu[0,\[Sigma],Vp\[Beta],sym]
Hu[\[Sigma]_,\[Tau]_,{V_,p_,\[Beta]_},sym_:False]:=1/(Z[\[Sigma],{V,p,\[Beta]},sym]Z[\[Tau],{V,p,\[Beta]},sym]) (d2ellp[{V,p,\[Beta]},sym]-2p dendellp[{V,p,\[Beta]},sym]+p^2 d2enp[{V,p,\[Beta]},sym]-\[Sigma] \[Tau] csq1[{V,p,\[Beta]},sym]denp[{V,p,\[Beta]},sym])

(* Hen depends on mass via sound speed *)
Hen[0,0,Vp\[Beta]m_,sym_:False]:=0
Hen[0,\[Sigma]_,Vp\[Beta]m_,sym_:False]:=0
Hen[\[Sigma]_,0,Vp\[Beta]m_,sym_:False]:=0
Hen[\[Sigma]_,\[Tau]_,{V_,p_,\[Beta]_,m_:1},sym_:False]:=Sqrt[csq[{V,p,\[Beta],m},sym]]/(2\[Beta]) (\[Sigma]+\[Tau])


(* G matrices, mass enters as scaling factor 1/Sqrt[m] *)

(* G_0 equals 1/2 1/Ztilde[0,{V,p,\[Beta]},sym] Hen[i,j,{V,p,\[Beta],m},sym] *)
G[0,0,0,Vp\[Beta]m_,sym_:False]:=0
G[0,0,\[Sigma]_,Vp\[Beta]m_,sym_:False]:=0
G[0,\[Sigma]_,0,Vp\[Beta]m_,sym_:False]:=0
G[0,\[Sigma]_,\[Tau]_,{V_,p_,\[Beta]_,m_:1},sym_:False]:=1/2 1/(\[Beta] Sqrt[m \[CapitalGamma][{V,p,\[Beta]},sym]]) (\[Sigma]+\[Tau])/2

G[\[Sigma]_,i_,j_,{V_,p_,\[Beta]_,m_:1},sym_:False]:=1/2 \[Sigma] Sqrt[\[Beta]/(2m)]Hu[i,j,{V,p,\[Beta]},sym]+1/2 denp[{V,p,\[Beta]},sym] Sqrt[\[Beta]/(2 csq1[{V,p,\[Beta]},sym])] Hen[i,j,{V,p,\[Beta],m},sym]
