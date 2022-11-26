(* ::Package:: *)

(* ::Section:: *)
(*Usage*)


a::usage = 
"a[f, i, k], a[\[Dagger], f, i, k] Multiple flavor version of a[]. Note that paired flavor indices are not contracted. \
If intergers or strings are used as flavor indices, they are seen as specific flavors. Otherwise they are seen \
as unspecified and using Sum\[Delta]f[] will sum over all these unspecified flavor indices. ";
c::usage = 
"c[f, i, k], c[\[Dagger], f, i, k] Multiple flavor version of c[]. Note that paired flavor indices are not contracted. \
If intergers or strings are used as flavor indices, they are seen as specific flavors. Otherwise they are seen \
as unspecified and using Sum\[Delta]f[] will sum over all these unspecified flavor indices. ";


b::usage = 
"b[f, i, k], b[\[Dagger], f, i, k] Multiple flavor version of b[]. Note that paired flavor indices are not contracted. \
If intergers or strings are used as flavor indices, they are seen as specific flavors. Otherwise they are seen \
as unspecified and using Sum\[Delta]f[] will sum over all these unspecified flavor indices. ";
d::usage = 
"d[f, i, k], d[\[Dagger], f, i, k] Multiple flavor version of d[]. Note that paired flavor indices are not contracted. \
If intergers or strings are used as flavor indices, they are seen as specific flavors. Otherwise they are seen \
as unspecified and using Sum\[Delta]f[] will sum over all these unspecified flavor indices. ";


(* ::Section:: *)
(*Rules*)


(* NOTE: The order of the following rules matters *)
\[Delta] /: \[Delta][i_, j_] (h:a|b)[\[Dagger], f_, i_, k___] := h[\[Dagger], f, j, k]
\[Delta] /: \[Delta][i_, j_] (h:a|b)[f_, j_, k___] := h[f, i, k]
\[Delta] /: \[Delta][i_, j_] (h:c|d)[\[Dagger], f_, j_, k___] := h[\[Dagger], f, i, k]
\[Delta] /: \[Delta][i_, j_] (h:c|d)[f_, i_, k___] := h[f, j, k]

\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:a|b)[\[Dagger], f_, i_, k___], y___] := Dot[x, h[\[Dagger], f, j, k], y]
\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:a|b)[f_, j_, k___], y___] := Dot[x, h[f, i, k], y]
\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:c|d)[\[Dagger], f_, j_, k___], y___] := Dot[x, h[\[Dagger], f, i, k], y]
\[Delta] /: \[Delta][i_, j_] Dot[x___, (h:c|d)[f_, i_, k___], y___] := Dot[x, h[f, j, k], y]


(* NOTE: \[Delta][i,j] stands for Subsuperscript[\[Delta], i, j] *)
CC[a[f1_, i_, k_], a[\[Dagger], f2_, j_, l_]] := \[Delta]f[f1, f2] \[Delta][i, j] (2\[Pi]) \[Delta][k-l]
CC[a[\[Dagger], f2_, j_, l_], a[f1_, i_, k_]] := - \[Delta]f[f1, f2] \[Delta][i, j] (2\[Pi]) \[Delta][k-l]
CC[c[f1_, i_, k_], c[\[Dagger], f2_, j_, l_]] := \[Delta]f[f2, f1] \[Delta][j, i] (2\[Pi]) \[Delta][k-l]
CC[c[\[Dagger], f2_, j_, l_], c[f1_, i_, k_]] := - \[Delta]f[f2, f1] \[Delta][j, i] (2\[Pi]) \[Delta][k-l]
(* Otherwise *)
CC[(a|c)[__], (a|c)[__]] := 0
(* Derivatives of bb, dd *)
CC[\[GothicCapitalD][lh:a|c, k_][la__], (rh:a|c)[ra__]] := Module[{k1}, \[DoubleStruckCapitalD][CC[lh[la]/.k->k1, rh[ra]], k1]/.k1->k]
CC[(lh:a|c)[la__], \[GothicCapitalD][rh:a|c, k_][ra__]] := Module[{k1}, \[DoubleStruckCapitalD][CC[lh[la], rh[ra]/.k->k1], k1]/.k1->k]


(* NOTE: \[Delta][i,j] stands for Subsuperscript[\[Delta], i, j] *)
AC[b[f1_, i_, k_], b[\[Dagger], f2_, j_, l_]] := \[Delta]f[f1, f2]\[Delta][i, j] (2\[Pi]) \[Delta][k-l]
AC[b[\[Dagger], f2_, j_, l_], b[f1_, i_, k_]] := \[Delta]f[f1, f2]\[Delta][i, j] (2\[Pi]) \[Delta][k-l]
AC[d[f1_, i_, k_], d[\[Dagger], f2_, j_, l_]] := \[Delta]f[f2, f1]\[Delta][j, i] (2\[Pi]) \[Delta][k-l]
AC[d[\[Dagger], f2_, j_, l_], d[f1_, i_, k_]] := \[Delta]f[f2, f1]\[Delta][j, i] (2\[Pi]) \[Delta][k-l]
(* Otherwise *)
AC[(b|d)[__], (b|d)[__]] := 0
(* Derivatives of bb, dd *)
AC[\[GothicCapitalD][lh:b|d, k_][la__], (rh:b|d)[ra__]] := Module[{k1}, \[DoubleStruckCapitalD][AC[lh[la]/.k->k1, rh[ra]], k1]/.k1->k]
AC[(lh:b|d)[la__], \[GothicCapitalD][rh:b|d, k_][ra__]] := Module[{k1}, \[DoubleStruckCapitalD][AC[lh[la], rh[ra]/.k->k1], k1]/.k1->k]


CC[(a|c)[__], (b|d)[__]] := 0
CC[(b|d)[__], (a|c)[__]] := 0


rulesForNormalOrdering = {
	(o1:((a|c)[_, _, _])) . (o2:((a|c)[\[Dagger], _, _, _])) :> CC[o1, o2] + o2 . o1,
	(o1:(a[_, _, _])) . (o2:(c[_, _, _])) :> o2 . o1,
	(o1:(c[\[Dagger], _, _, _])) . (o2:(a[\[Dagger], _, _, _])) :> o2 . o1,

	(o1:((b|d)[_, _, _])) . (o2:((b|d)[\[Dagger], _, _, _])) :> AC[o1, o2] - o2 . o1,
	(o1:(b[_, _, _])) . (o2:(d[_, _, _])) :> - o2 . o1,
	(o1:(d[\[Dagger], _, _, _])) . (o2:(b[\[Dagger], _, _, _])) :> - o2 . o1,

	(o1:(a[_, _, _])) . (o2:(d[_, _, _])) :> o2 . o1,
	(o1:(b[_, _, _])) . (o2:(c[_, _, _])) :> o2 . o1,
	(o1:(d[\[Dagger], _, _, _])) . (o2:(a[\[Dagger], _, _, _])) :> o2 . o1,
	(o1:(c[\[Dagger], _, _, _])) . (o2:(b[\[Dagger], _, _, _])) :> o2 . o1,
	(o1:((a|c)[_, _, _])) . (o2:((b|d)[\[Dagger], _, _, _])) :> o2 . o1,
	(o1:((b|d)[_, _, _])) . (o2:((a|c)[\[Dagger], _, _, _])) :> o2 . o1
};


rules4VacExp = {
	(* NOTE: This is much alike the rulesForNormalOrdering.  *)
	{o1:((a|c)[_, _, _]), seqA__:1, o2:((a|c)[\[Dagger], _, _, _]), seqB___} :> {CC[o1, o2], {seqA, seqB}},
	{o1:((b|d)[_, _, _]), seqA__:1, o2:((b|d)[\[Dagger], _, _, _]), seqB___} :> {If[ACOpQ[Dot[seqA]], -1, 1] AC[o1, o2], {seqA, seqB}}
};


rulesForBosonOrdering  = {
	(* Sort by color index *)
	(g:a|c)[HoldPattern[gdg_:Sequence[]], f1_, i_, k_] . (h:a|b|c|d)[HoldPattern[hdg_:Sequence[]], f2_, j_, l_]/;Order[i, j]==-1 :>\
		CC[g[gdg, f1, i, k], h[hdg, f2, j, l]] + h[hdg, f2, j, l] . g[gdg, f1, i, k],
	(g:a|b|c|d)[HoldPattern[gdg_:Sequence[]], f1_, i_, k_] . (h:a|c)[HoldPattern[hdg_:Sequence[]], f2_, j_, l_]/;Order[i, j]==-1 :>\
		CC[g[gdg, f1, i, k], h[hdg, f2, j, l]] + h[hdg, f2, j, l] . g[gdg, f1, i, k],
	(g:b|d)[HoldPattern[gdg_:Sequence[]], f1_, i_, k_] . (h:b|d)[HoldPattern[hdg_:Sequence[]], f2_, j_, l_]/;Order[i, j]==-1 :>\
		AC[g[gdg, f1, i, k], h[hdg, f2, j, l]] - h[hdg, f2, j, l] . g[gdg, f1, i, k],

	(* Rearrange a, c to match N, A, C *)
	c[\[Dagger], f1_, i_, k_] . a[\[Dagger], f2_, i_, l_] :> a[\[Dagger], f2, i, l] . c[\[Dagger], f1, i, k],
	a[f1_, i_, k_] . c[f2_, i_, l_] :> c[f2, i, l] . a[f1, i, k],
	a[f1_, i_, k_] . a[\[Dagger], f2_, i_, l_] :> CC[a[f1, i, k], a[\[Dagger], f2, i, l]] + a[\[Dagger], f2, i, l] . a[f1, i, k],
	c[f1_, i_, k_] . c[\[Dagger], f2_, i_, l_] :> CC[c[f1, i, k], c[\[Dagger], f2, i, l]] + c[\[Dagger], f2, i, l] . c[f1, i, k],

	(* Rearrange b, d to match M, B, D *)
	d[\[Dagger], f1_, i_, k_] . b[\[Dagger], f2_, i_, l_] :> -b[\[Dagger], f2, i, l] . d[\[Dagger], f1, i, k],
	b[f1_, i_, k_] . d[f2_, i_, l_] :> -d[f2, i, l] . b[f1, i, k],
	b[f1_, i_, k_] . b[\[Dagger], f2_, i_, l_] :> AC[b[f1, i, k], b[\[Dagger], f2, i, l]] - b[\[Dagger], f2, i, l] . b[f1, i, k],
	d[f1_, i_, k_] . d[\[Dagger], f2_, i_, l_] :> AC[d[f1, i, k], d[\[Dagger], f2, i, l]] - d[\[Dagger], f2, i, l] . d[f1, i, k],

	(* Rearrange a, d or b, c to match K, L *)
	a[f1_, i_, k_] . d[f2_, i_, l_] :> d[f2, i, l] . a[f1, i, k],
	b[f1_, i_, k_] . c[f2_, i_, l_] :> c[f2, i, l] . b[f1, i, k],
	d[\[Dagger], f1_, i_, k_] . a[\[Dagger], f2_, i_, l_] :> a[\[Dagger], f2, i, l] . d[\[Dagger], f1, i, k],
	c[\[Dagger], f1_, i_, k_] . b[\[Dagger], f2_, i_, l_] :> b[\[Dagger], f2, i, l] . c[\[Dagger], f1, i, k]
};


(* ::Section:: *)
(*Output Typesetting*)


(* a[f, c, k] to Subscript[a, f,c](k) *)
a /: MakeBoxes[a[f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SubscriptBox["a", RowBox[{MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* a[\[Dagger], f, c, k] to a^(\[Dagger]f,c)(k) *)
a /: MakeBoxes[a[\[Dagger], f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["a", RowBox[{"\[Dagger]", MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* c[f, c, k] to c^(f,c)(k) *)
c /: MakeBoxes[c[f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["c", RowBox[{MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* c[\[Dagger], f, c, k] to Subsuperscript[c, f,c, \[Dagger]](k) *)
c /: MakeBoxes[c[\[Dagger], f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SubsuperscriptBox["c", RowBox[{MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}], "\[Dagger]"], "(", MakeBoxes[k, tf], ")"}]


(* b[f, c, k] to Subscript[b, f,c](k) *)
b /: MakeBoxes[b[f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SubscriptBox["b", RowBox[{MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* b[\[Dagger], f, c, k] to b^(\[Dagger]f,c)(k) *)
b /: MakeBoxes[b[\[Dagger], f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["b", RowBox[{"\[Dagger]", MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* d[f, c, k] to d^(f,c)(k) *)
d /: MakeBoxes[d[f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SuperscriptBox["d", RowBox[{MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}]], "(", MakeBoxes[k, tf], ")"}]
(* d[\[Dagger], f, c, k] to Subsuperscript[d, f,c, \[Dagger]](k) *)
d /: MakeBoxes[d[\[Dagger], f_, c_, k_], tf:TraditionalForm] := 
	RowBox[{SubsuperscriptBox["d", RowBox[{MakeBoxes[f, tf], ",", MakeBoxes[c, tf]}], "\[Dagger]"], "(", MakeBoxes[k, tf], ")"}]
