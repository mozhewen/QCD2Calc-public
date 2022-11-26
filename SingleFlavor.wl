(* ::Package:: *)

(* ::Section:: *)
(*Usage*)


a::usage = 
"a[i, k], a[\[Dagger], i, k] Scalar quark annihilation / creation operator with color index i and momentum k. ";
c::usage = 
"c[i, k], c[\[Dagger], i, k] Scalar anti-quark annihilation / creation operator with color index i and momentum k. ";


b::usage = 
"b[i, k], b[\[Dagger], i, k] Quark annihilation / creation operator with color index i and momentum k. ";
d::usage = 
"d[i, k], d[\[Dagger], i, k] Anti-quark annihilation / creation operator with color index i and momentum k. ";


(* ::Section:: *)
(*Rules*)


(* NOTE: The order of the following rules matters *)
\[Delta] /: \[Delta][i_, j_] (h:a|b)[\[Dagger], i_, k___] := h[\[Dagger], j, k]
\[Delta] /: \[Delta][i_, j_] (h:a|b)[j_, k___] := h[i, k]
\[Delta] /: \[Delta][i_, j_] (h:c|d)[\[Dagger], j_, k___] := h[\[Dagger], i, k]
\[Delta] /: \[Delta][i_, j_] (h:c|d)[i_, k___] := h[j, k]

\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:a|b)[\[Dagger], i_, k___], y___] := Dot[x, h[\[Dagger], j, k], y]
\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:a|b)[j_, k___], y___] := Dot[x, h[i, k], y]
\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:c|d)[\[Dagger], j_, k___], y___] := Dot[x, h[\[Dagger], i, k], y]
\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:c|d)[i_, k___], y___] := Dot[x, h[j, k], y]


(* NOTE: \[Delta][i,j] stands for Subsuperscript[\[Delta], i, j] *)
CC[a[i_, k_], a[\[Dagger], j_, l_]] := \[Delta][i, j] (2\[Pi]) \[Delta][k-l]
CC[a[\[Dagger], j_, l_], a[i_, k_]] := - \[Delta][i, j] (2\[Pi]) \[Delta][k-l]
CC[c[i_, k_], c[\[Dagger], j_, l_]] := \[Delta][j, i] (2\[Pi]) \[Delta][k-l]
CC[c[\[Dagger], j_, l_], c[i_, k_]] := - \[Delta][j, i] (2\[Pi]) \[Delta][k-l]
(* Otherwise *)
CC[(a|c)[__], (a|c)[__]] := 0
(* Derivatives of a, c *)
CC[\[GothicCapitalD][lh:a|c, k_][la__], (rh:a|c)[ra__]] := Module[{k1}, \[DoubleStruckCapitalD][CC[lh[la]/.k->k1, rh[ra]], k1]/.k1->k]
CC[(lh:a|c)[la__], \[GothicCapitalD][rh:a|c, k_][ra__]] := Module[{k1}, \[DoubleStruckCapitalD][CC[lh[la], rh[ra]/.k->k1], k1]/.k1->k]


(* NOTE: \[Delta][i,j] stands for Subsuperscript[\[Delta], i, j] *)
AC[b[i_, k_], b[\[Dagger], j_, l_]] := \[Delta][i, j] (2\[Pi]) \[Delta][k-l]
AC[b[\[Dagger], j_, l_], b[i_, k_]] := \[Delta][i, j] (2\[Pi]) \[Delta][k-l]
AC[d[i_, k_], d[\[Dagger], j_, l_]] := \[Delta][j, i] (2\[Pi]) \[Delta][k-l]
AC[d[\[Dagger], j_, l_], d[i_, k_]] := \[Delta][j, i] (2\[Pi]) \[Delta][k-l]
(* Otherwise *)
AC[(b|d)[__], (b|d)[__]] := 0
(* Derivatives of b, d *)
AC[\[GothicCapitalD][lh:b|d, k_][la__], (rh:b|d)[ra__]] := Module[{k1}, \[DoubleStruckCapitalD][AC[lh[la]/.k->k1, rh[ra]], k1]/.k1->k]
AC[(lh:b|d)[la__], \[GothicCapitalD][rh:b|d, k_][ra__]] := Module[{k1}, \[DoubleStruckCapitalD][AC[lh[la], rh[ra]/.k->k1], k1]/.k1->k]


CC[(a|c)[__], (b|d)[__]] := 0
CC[(b|d)[__], (a|c)[__]] := 0


rulesForNormalOrdering = {
	(o1:((a|c)[_, _])) . (o2:((a|c)[\[Dagger], _, _])) :> CC[o1, o2] + o2 . o1,
	(o1:(a[_, _])) . (o2:(c[_, _])) :> o2 . o1,
	(o1:(c[\[Dagger], _, _])) . (o2:(a[\[Dagger], _, _])) :> o2 . o1,

	(o1:((b|d)[_, _])) . (o2:((b|d)[\[Dagger], _, _])) :> AC[o1, o2] - o2 . o1,
	(o1:(b[_, _])) . (o2:(d[_, _])) :> - o2 . o1,
	(o1:(d[\[Dagger], _, _])) . (o2:(b[\[Dagger], _, _])) :> - o2 . o1,

	(o1:(a[_, _])) . (o2:(d[_, _])) :> o2 . o1,
	(o1:(b[_, _])) . (o2:(c[_, _])) :> o2 . o1,
	(o1:(d[\[Dagger], _, _])) . (o2:(a[\[Dagger], _, _])) :> o2 . o1,
	(o1:(c[\[Dagger], _, _])) . (o2:(b[\[Dagger], _, _])) :> o2 . o1,
	(o1:((a|c)[_, _])) . (o2:((b|d)[\[Dagger], _, _])) :> o2 . o1,
	(o1:((b|d)[_, _])) . (o2:((a|c)[\[Dagger], _, _])) :> o2 . o1
};


rules4VacExp = {
	(* NOTE: This is much alike the rulesForNormalOrdering.  *)
	{o1:((a|c)[_, _]), seqA__:1, o2:((a|c)[\[Dagger], _, _]), seqB___} :> {CC[o1, o2], {seqA, seqB}},
	{o1:((b|d)[_, _]), seqA__:1, o2:((b|d)[\[Dagger], _, _]), seqB___} :> {If[ACOpQ[Dot[seqA]], -1, 1] AC[o1, o2], {seqA, seqB}}
};


rulesForBosonOrdering  = {
	(* Sort by color index *)
	(g:a|c)[HoldPattern[gdg_:Sequence[]], i_, k_] . (h:a|b|c|d)[HoldPattern[hdg_:Sequence[]], j_, l_]/;Order[i, j]==-1 :>\
		CC[g[gdg, i, k], h[hdg, j, l]] + h[hdg, j, l] . g[gdg, i, k],
	(g:a|b|c|d)[HoldPattern[gdg_:Sequence[]], i_, k_] . (h:a|c)[HoldPattern[hdg_:Sequence[]], j_, l_]/;Order[i, j]==-1 :>\
		CC[g[gdg, i, k], h[hdg, j, l]] + h[hdg, j, l] . g[gdg, i, k],
	(g:b|d)[HoldPattern[gdg_:Sequence[]], i_, k_] . (h:b|d)[HoldPattern[hdg_:Sequence[]], j_, l_]/;Order[i, j]==-1 :>\
		AC[g[gdg, i, k], h[hdg, j, l]] - h[hdg, j, l] . g[gdg, i, k],

	(* Rearrange a, c to match N, A, C *)
	c[\[Dagger], i_, k_] . a[\[Dagger], i_, l_] :> a[\[Dagger], i, l] . c[\[Dagger], i, k],
	a[i_, k_] . c[i_, l_] :> c[i, l] . a[i, k],
	a[i_, k_] . a[\[Dagger], i_, l_] :> CC[a[i, k], a[\[Dagger], i, l]] + a[\[Dagger], i, l] . a[i, k],
	c[i_, k_] . c[\[Dagger], i_, l_] :> CC[c[i, k], c[\[Dagger], i, l]] + c[\[Dagger], i, l] . c[i, k],

	(* Rearrange b, d to match M, B, D *)
	d[\[Dagger], i_, k_] . b[\[Dagger], i_, l_] :> -b[\[Dagger], i, l] . d[\[Dagger], i, k],
	b[i_, k_] . d[i_, l_] :> -d[i, l] . b[i, k],
	b[i_, k_] . b[\[Dagger], i_, l_] :> AC[b[i, k], b[\[Dagger], i, l]] - b[\[Dagger], i, l] . b[i, k],
	d[i_, k_] . d[\[Dagger], i_, l_] :> AC[d[i, k], d[\[Dagger], i, l]] - d[\[Dagger], i, l] . d[i, k],

	(* Rearrange a, d or b, c to match K, L *)
	a[i_, k_] . d[i_, l_] :> d[i, l] . a[i, k],
	b[i_, k_] . c[i_, l_] :> c[i, l] . b[i, k],
	d[\[Dagger], i_, k_] . a[\[Dagger], i_, l_] :> a[\[Dagger], i, l] . d[\[Dagger], i, k],
	c[\[Dagger], i_, k_] . b[\[Dagger], i_, l_] :> b[\[Dagger], i, l] . c[\[Dagger], i, k]
};


(* ::Section:: *)
(*Output Typesetting*)


(* a[c, k] to Subscript[a, c](k) *)
a /: MakeBoxes[a[c_, k_], tf:TraditionalForm] := 
	RowBox[{SubscriptBox["a", MakeBoxes[c, tf]], "(", MakeBoxes[k, tf], ")"}]
(* a[\[Dagger], c, k] to a^\[Dagger]c(k) *)
a /: MakeBoxes[a[\[Dagger], c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["a", RowBox[{"\[Dagger]", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* c[c, k] to c^c(k) *)
c /: MakeBoxes[c[c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["c", MakeBoxes[c, tf]], "(", MakeBoxes[k, tf], ")"}]
(* c[\[Dagger], c, k] to Subsuperscript[c, c, \[Dagger]](k) *)
c /: MakeBoxes[c[\[Dagger], c_, k_], tf:TraditionalForm] := 
	RowBox[{SubsuperscriptBox["c", MakeBoxes[c, tf], "\[Dagger]"], "(", MakeBoxes[k, tf], ")"}]


(* b[c, k] to Subscript[b, c](k) *)
b /: MakeBoxes[b[c_, k_], tf:TraditionalForm] := 
	RowBox[{SubscriptBox["b", MakeBoxes[c, tf]], "(", MakeBoxes[k, tf], ")"}]
(* b[\[Dagger], c, k] to b^\[Dagger]c(k) *)
b /: MakeBoxes[b[\[Dagger], c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["b", RowBox[{"\[Dagger]", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* d[c, k] to d^c(k) *)
d /: MakeBoxes[d[c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["d", MakeBoxes[c, tf]], "(", MakeBoxes[k, tf], ")"}]
(* d[\[Dagger], c, k] to Subsuperscript[d, c, \[Dagger]](k) *)
d /: MakeBoxes[d[\[Dagger], c_, k_], tf:TraditionalForm] := 
	RowBox[{SubsuperscriptBox["d", MakeBoxes[c, tf], "\[Dagger]"], "(", MakeBoxes[k, tf], ")"}]
