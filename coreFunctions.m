(* ::Package:: *)

(* ::Section:: *)
(*1Global Definitions (should be executed first)*)


(* ::Text:: *)
(*transition probabilities vector for game A and B (or game vector in short), L is the period of the transition probability, M is the period of the game itself. L is meaningful only when you wan to mix two games with different period*)


aMx[p_,L_]:=Table[p,{L}];
bmMx[p_,q_,M_,L_]:=Join @@ Table[ReplacePart[Table[q,{M}],1->p],{Quotient[L,M]}];


(* ::Text:: *)
(*constrcut transition matrix from game vectors*)


transition[game_,dim_]:=Table[ReplacePart[Table[0,{dim}],{Mod[i+1,dim,1]->game[[i]],Mod[i-1+dim,dim,1]->(1-game[[i]])}],{i,dim}];


(* ::Text:: *)
(*solves for the long term distribution given a game vector*)


longterm[M_]:=Module[{len=Length[M]},LinearSolve[ReplacePart[Transpose[M]-IdentityMatrix[len],len->Table[1,{len}]],ReplacePart[Table[0,{len}],len->1]]];
payoff[game_]:=2 game-1;


(* ::Text:: *)
(*Expected payoff given a game sequence*)


ParrondoExpected[game_,n_]:=Module[
{freq=ReplacePart[Table[0,{Length[game[[1]]]}],1->1],capital=0,capitalList=Table[0,{n+1}],pos=0,len=Length[game],pay=payoff/@game,trans=transition[#,Length[game[[1]]]]&/@game},
Do[pos=Mod[pos,len]+1;
capital+=freq.pay[[pos]];
capitalList[[i]]=capital;freq=freq.trans[[pos]],{i,2,n+1}];
capitalList];
AddXVals[d_] := Transpose[{Range[0,Length[d]-1], d}];


(* ::Text:: *)
(*useful and more specific simplifying function, for rational function specifically*)


(* handy in simplify rational functions *)
simp0[poly_]:=Collect[Expand[poly],C,Factor];
simp[ratio_]:=Module[{fun=Together[ratio]},simp0[Numerator[fun]]/simp0[Denominator[fun]]];
simp02[poly_]:=Module[{ls},ls=CoefficientRules[poly,{\[Gamma],C}];Plus@@(ls/.Rule[{a_,b_},c_]:>\[Gamma]^a C^b Factor[c])];
simp2[ratio_]:=Module[{fun=Together[ratio]},simp02[Numerator[fun]]/simp02[Denominator[fun]]];


(* ::Text:: *)
(*"winning" and "losing" probability*)


winProb[M1_,M2_]:=With[{period=LCM[M1,M2]},Simplify[Times @@ (C bmMx[Subscript[p, b],Subscript[p, g],M1,period]+(1-C)bmMx[Subscript[p, b],Subscript[p, g],M2,period])]];
loseProb[M1_,M2_]:=With[{period=LCM[M1,M2]},Simplify[Times @@ (1-(C bmMx[Subscript[p, b],Subscript[p, g],M1,period]+(1-C)bmMx[Subscript[p, b],Subscript[p, g],M2,period]))]];
winProbA[M1_,M2_,\[Gamma]_]:=
With[{period=LCM[M1,M2]},Simplify[Times @@ (\[Gamma] Subscript[p, A]+(1-\[Gamma])(C bmMx[Subscript[p, b],Subscript[p, g],M1,period]+(1-C)bmMx[Subscript[p, b],Subscript[p, g],M2,period]))]];
loseProbA[M1_,M2_,\[Gamma]_]:=With[{period=LCM[M1,M2]},Simplify[Times @@ (1-(\[Gamma] Subscript[p, A]+(1-\[Gamma])(C bmMx[Subscript[p, b],Subscript[p, g],M1,period]+(1-C)bmMx[Subscript[p, b],Subscript[p, g],M2,period])))]];


(* ::Text:: *)
(*plot a smooth fair game boundary by turnning the condition into a differential equation and then numerically integrate it*)


dBoundary[M1_,M2_,Cx_]:=
Module[{deri,sol},
deri=Solve[D[winProb[M1,M2]-loseProb[M1,M2],Subscript[p, g],NonConstants->{Subscript[p, b]}]==0, D[Subscript[p, b],Subscript[p, g],NonConstants->{Subscript[p, b]}]][[1,1,2]];
NDSolve[{Subscript[p, b]'[Subscript[p, g]]==(deri/.{C->Cx,Subscript[p, b]->Subscript[p, b][Subscript[p, g]]}),Subscript[p, b][0.5]==0.5},Subscript[p, b],{Subscript[p, g],0.5,1}]
];
dBoundaryA[M1_,M2_,Cx_,\[Gamma]x_]:=
Module[{deri,sol},
deri=Solve[D[winProbA[M1,M2,\[Gamma]]-loseProbA[M1,M2,\[Gamma]],Subscript[p, g],NonConstants->{Subscript[p, b]}]==0, D[Subscript[p, b],Subscript[p, g],NonConstants->{Subscript[p, b]}]][[1,1,2]];
NDSolve[{Subscript[p, b]'[Subscript[p, g]]==(deri/.{C->Cx,\[Gamma]->\[Gamma]x,Subscript[p, b]->Subscript[p, b][Subscript[p, g]]}),Subscript[p, b][0.5]==0.5},Subscript[p, b],{Subscript[p, g],0.5,1}]
];


constructEqn[L_]:=
Module[{m},
m=ConstantArray[0,{L,L}];
Do[m[[i,i]]=Subscript[F, i]+1;m[[i,i+1]]=Subscript[F, i+1]-1,{i,1,L-1}];
m[[L,1]]=Subscript[F, 1]-1;m[[L,L]]=Subscript[F, L]+1;
m
];
V[i_]:=-1/2 Sum[Log[(1+Subscript[F, k-1])/(1-Subscript[F, k])],{k,1,i}];
V2[i_]:=-1/2 Sum[Log[Subscript[q, k-1]/(1-Subscript[q, k])],{k,1,i}];
V2[i_,game_]:=
Module[{L=Length[game]},Simplify[(-1/2 Sum[Log[Subscript[q, k-1]/(1-Subscript[q, k])],{k,1,i}]/.{Subscript[q, L]->Subscript[q, 0]})/.{Subscript[q,x_]:>game[[Mod[x+1,L,1]]]}]];
current[L_]:=Simplify[statP0[L] (1-Exp[2V[L]])/(2Sum[Exp[2V[j]]/(1-Subscript[F, j]),{j,1,L}])/.{Subscript[F, L]->Subscript[F, 0]}];
current[L_,p0_]:=Simplify[p0 (1-Exp[2V[L]])/(2Sum[Exp[2V[j]]/(1-Subscript[F, j]),{j,1,L}])/.{Subscript[F, L]->Subscript[F, 0]}];
current2[L_,game_]:=Simplify[(statP02[L] (1-Exp[2V2[L]])/(2Sum[Exp[2V2[j]]/(2-2Subscript[q, j]),{j,1,L}])/.{Subscript[q, L]->Subscript[q, 0]})/.{Subscript[q,x_]:>game[[x+1]]}];
current2[L_]:=Simplify[statP02[L] (1-Exp[2V2[L]])/(2Sum[Exp[2V2[j]]/(2-2Subscript[q, j]),{j,1,L}])/.{Subscript[q, L]->Subscript[q, 0]}];
statP[i_,L_]:=
 Exp[-2V[i]](statP0[L]-2current[L]Sum[Exp[2V[j]]/(1-Subscript[F, j]),{j,1,i}]);
statP[i_,L_,p0_]:=
 Exp[-2V[i]](p0-2current[L,p0]Sum[Exp[2V[j]]/(1-Subscript[F, j]),{j,1,i}]);
statP2[i_,L_,game_]:=
 Exp[-2V2[i]](statP02[L,game]-2current2[L,game]Sum[Exp[2V2[j,game]]/(2-2Subscript[q, j]),{j,1,i}])/.{Subscript[q,x_]:>game[[x+1]]};
statP0[L_]:=1/Simplify@(Sum[Exp[-2V[i]],{i,0,L-1}]-Sum[(Exp[-2V[i]](1-Exp[2V[L]]))/Sum[Exp[2V[j]]/(1-Subscript[F, j]),{j,1,L}] Sum[Exp[2V[j]]/(1-Subscript[F, j]),{j,1,i}],{i,0,L-1}]);
statP02[L_]:=1/(Sum[Exp[-2V2[i]],{i,0,L-1}]-Sum[(Exp[-2V2[i]](1-Exp[2V2[L]]))/Sum[Exp[2V2[j]]/(2-2Subscript[q, j]),{j,1,L}] Sum[Exp[2V2[j]]/(2-2Subscript[q, j]),{j,1,i}],{i,0,L-1}]/.{Subscript[q, L]->Subscript[q, 0]});
statP02[L_,game_]:=1/(Sum[Exp[-2V2[i]],{i,0,L-1}]-Sum[(Exp[-2V2[i]](1-Exp[2V2[L]]))/Sum[Exp[2V2[j]]/(2-2Subscript[q, j]),{j,1,L}] Sum[Exp[2V2[j]]/(2-2Subscript[q, j]),{j,1,i}],{i,0,L-1}]/.{Subscript[q, L]->Subscript[q, 0]}/.{Subscript[q,x_]:>game[[Mod[x+1,L,1]]]});
time[ix_,Lx_,game_]:=With[{expr=1/Subscript[p, i]+Sum[Product[Subscript[q, k]/Subscript[p, k],{k,j,i+L}]/Subscript[p, j-1],{j,i+1,i+L}]/(1-Product[Subscript[q, k],{k,1,L}]/Product[Subscript[p, k],{k,1,L}])},
Together[((Simplify[(expr/.{L->Lx,i->ix})]/.{Subscript[x_,i_]:>Subscript[x,Mod[i,Lx]]})/.{Subscript[q,i_]:>1-Subscript[p, i]})/.{Subscript[p,x_]:>game[[x+1]]}
]
];
gain[game_]:=
Module[{L=Length[game]},
Simplify[L/Sum[time[i,L,game],{i,0,L-1}]]
];
Options[burnTooltips]={ImageSize->360,"LabelFunction"->(Framed[#,FrameStyle->None,RoundingRadius->8,Background->RGBColor[1,.8,.4]]&)};

burnTooltips[plot_,opt:OptionsPattern[]]:=DynamicModule[{ins={},wrapper=OptionValue["LabelFunction"],toolRule=Function[{arg},Tooltip[t__]:>Button[Tooltip[t],AppendTo[arg,Inset[wrapper[Last[{t}]],MousePosition["Graphics"]]]],HoldAll]},EventHandler[Dynamic@Show[plot/.toolRule[ins],Graphics@ins,ImageSize->OptionValue[ImageSize]],{"MouseUp",2}:>(toolRule={}&)]]


Clear[longtermX];
longtermX[M_?MatrixQ]:=Module[{len=Length[M],tmp},tmp=Transpose[M]-IdentityMatrix[len];
tmp[[len,All]]=ConstantArray[1,len];
tmp];


(* ::Text:: *)
(*directly compute the long-term average gain, due to Derrida 1983*)


A[L_,game_]:=L/Sum[(1/game[[Mod[n,L,1]]])(1+Sum[Product[(1-game[[Mod[n+j,L,1]]])/game[[Mod[n+j,L,1]]],{j,1,i}],{i,1,L-1}]),{n,1,L}](1-Product[(1-game[[n]])/game[[n]],{n,1,L}])
