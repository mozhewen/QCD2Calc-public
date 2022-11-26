(* ::Package:: *)

(* ::Text:: *)
(*Description: *)
(*	1+1D QCD Hamiltonian approach automatic calculation package. *)
(*	Note that this package is designed for conciseness and readability instead of efficiency. *)
(*	Due to the conventions of \[Theta][0] and the strict inequality of integral bounds, this package cannot deal with zero modes in the light-cone quantization. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*TODO: *)
(*	1. More general condition statements for VacExp[]'s rules to ensure correct results. *)
(*	2. The rules for the derivatives of a, b, c, d are not complete. *)
(**)
(*Mathematica version: 13.0*)
(**)
(*Last update: 2022.9.14*)


(* ::Section:: *)
(*Begin*)


If[!ValueQ[$MultipleFlavors],
	$MultipleFlavors = False;
]


BeginPackage["QCD2Calc`"]


$QCD2CalcDebug = False;


(* NOTE: Unlike what the name suggests, these are actually the declarations of b, d and so on (as null variables).  *)
ClearAll[AddToList, RemoveFromList]
ClearAll[realValued, acOperators, cNumbers, noDagger, positiveAssumptions]

ClearAll[RealValQ, ACOpQ, CNumberQ, NoDaggerQ, SpecificQ]

ClearAll[a, b, c, d]
ClearAll[\[Dagger]]

ClearAll[Nf, Nc, gs, \[Lambda]]
ClearAll[\[Delta]f, \[Gamma], \[Delta], T, \[Theta], \[Delta]1, Expi]

ClearAll[HC, \[DoubleStruckCapitalD], \[GothicCapitalD], Int]
ClearAll[ReduceIntRegion, AdvancedReduceIntRegion, ComputeInt, ChangeIntVar, PermuteIntOrder, SimplifyInt]

ClearAll[Sum\[Delta]f]
ClearAll[CC, AC]
ClearAll[NormalOrdering, VacExp, BosonOrdering]

ClearAll[MyExponent, Fac, WrapIntegrandFactors, RenumberIndex, CollectLikeTerms]


Nf::usage = "Number of flavors. ";
Nc::usage = "Number of colors. ";
gs::usage = "Strong coupling constant. ";
\[Lambda]::usage = "Redefined coupling constant: \[Lambda] \[Congruent] \!\(\*FractionBox[\(\*SuperscriptBox[\(gs\), \(2\)] Nc\), \(4  \[Pi]\)]\). ";

\[Delta]f::usage = "\[Delta]f[f1, f2] represents the Kronecker delta \!\(\*SubsuperscriptBox[\(\[Delta]\), \(f1\), \(f2\)]\) of flavor indices. ";
\[Gamma]::usage = "\[Gamma][i, s1, s2] represents the Dirac gamma matrix (\!\(\*SuperscriptBox[\(\[Gamma]\), \(i\)]\)\!\(\*SubsuperscriptBox[\()\), \(s1\), \(s2\)]\). ";
\[Delta]::usage = "\[Delta][i, j] represents the Kronecker delta \!\(\*SubsuperscriptBox[\(\[Delta]\), \(i\), \(j\)]\) of color indices in the \
fundamental representation. 
\[Delta][k] represents the Dirac delta function. ";
T::usage = "T[a, i, j] represents the SU(Nc) fundamental representation generators \
(\!\(\*SuperscriptBox[\(T\), \(a\)]\)\!\(\*SubsuperscriptBox[\()\), \(i\), \(j\)]\). ";
\[Theta]::usage = "\[Theta][x] represents the Heaviside theta function. ";
\[Delta]1::usage = "\[Delta]1[k] represents the first derivative of the Dirac delta function. ";
Expi::usage = "Expi[x] = Exp[\[ImaginaryI] x]. ";

Int::usage = "Int[expr, {x1, x1lb, x1ub}, ...] represents a definite integral of x1, ... with interval [x1lb, x1ub], ..., \
a integral that should not be evaluated by the built-in Integrate[] function of Mathematica. Trivial integrals are evaluated \
automatically, whereas further reductions should be done by ComputeInt[] and SimplifyInt[]. 
NOTE: There are several restrictions to make this simple function work: 
1. xilb (i = 1, 2,...) must be less than xiub and must not contain any integration variables. 
2. Do not use, for example, x and its subscripted form \!\(\*SubscriptBox[\(x\), \(i\)]\) as integration variables at the \
same time. Use different symbols such as y and \!\(\*SubscriptBox[\(x\), \(i\)]\). 
3. As for the integrand, \[Theta][], \[Delta][], \[Delta]1[] and Expi[] must appear as factors. The expressions inside these functions must be \
linear functions of the integration variables and must not contain any operators. ";


Begin["`Private`"]
ClearAll["`*"]


ECHOLABEL[label_] := If[$QCD2CalcDebug === True, EchoLabel[label], Identity]


(* ::Section:: *)
(*Query Functions*)


(* ::Text:: *)
(*NOTE: The symbols not registered in cNumbers are by default regarded as operators which are suitable for commutator naturally. To define an operator suitable for anti-commutator, add it to acOperators. *)


AddToList::usage = 
"AddToList[list, {item1, item2, ...}] adds items into list, automatically maintains distinct elements. ";
SetAttributes[AddToList, HoldFirst]
AddToList[list_, items_List] := (Unevaluated[list] = Union[list, items];)


RemoveFromList::usage = 
"RemoveFromList[list, {item1, item2, ...}] removes items from list. ";
SetAttributes[RemoveFromList, HoldFirst]
RemoveFromList[list_, items_List] := (Unevaluated[list] = Complement[list, items];)


realValued::usage = 
"Symbols or heads of expresions which match a member of this list will be regarded as real-valued. ";
realValued = {Nf, Nc, gs, \[Lambda], \[Delta]f, \[Delta], \[Theta], \[Delta]1};


acOperators::usage = 
"Primitive operators which are suitable for anti-commutator (e.g. b, d) should be registered in this list. ";
acOperators = {b, d};


cNumbers::usage = 
"Symbols or heads of expresions which match a member of this list will be regarded as c-numbers. ";
cNumbers = {Nf, Nc, gs, \[Lambda], \[Delta]f, \[Gamma], \[Delta], T, \[Theta], \[Delta]1, Expi, Fac};


noDagger::usage = 
"Expressions with head in this list will not be calculated by HC[] by adding a \[Dagger]. ";
noDagger = {Expi, Int, CC, AC};


positiveAssumptions::usage = "Expressions in this list will be assumed positive. "
positiveAssumptions = {};


(* The actual head of expression \[GothicCapitalD][x, k][balabala...] is defined as x, not \[GothicCapitalD][x, k] *)
SetAttributes[ActualHead, HoldAll]
ActualHead[head_] := Switch[Head@Head[Unevaluated[head]],
	\[GothicCapitalD],
		First[Head[Unevaluated[head]]]
	, _,
		Head[Unevaluated[head]]
]


(* Prevent matching patterns, which would cause evaluation in the lhs. of Set(Delayed)((:)=) statement and other places where patterns appear.  *)
SetAttributes[NonPatternQ, HoldAll]
NonPatternQ[expr_] := FreeQ[Unevaluated@expr, Pattern|Blank|BlankSequence|BlankNullSequence|Optional|Alternatives|Repeated|Except]


(* Used in the definition of HC[]. *)
(* NOTE: Only vaild for symbols in "realValued". You can't use this function to recognize other real-valued expressions.  *)
SetAttributes[RealValQ, HoldAll]
RealValQ[expr_?NonPatternQ] := AnyTrue[realValued, MatchQ[Unevaluated@expr, #] || MatchQ[ActualHead@Unevaluated@expr, #]&]


SetAttributes[ACOpQ, HoldAll]
ACOpQ[expr_?NonPatternQ] := 
	If[Head@Unevaluated@expr === Dot,
		Xor@@(ACOpQ/@Unevaluated[expr])
	,(*Else*)
		AnyTrue[acOperators, MatchQ[Unevaluated@expr, #] || MatchQ[ActualHead@Unevaluated@expr, #]&]
	]


(* NOTE: If the head of a subexpression is registered in "cNumbers", 
the whole subexpression will be regarded as a c-number even if it has some contents that are not c-numbers.  *)
SetAttributes[CNumberQ, HoldAll]
CNumberQ[expr_?NonPatternQ] :=
	If[AnyTrue[cNumbers, MatchQ[Unevaluated@expr, #] || MatchQ[ActualHead@Unevaluated@expr, #]&],
		True
	,(*Else*)
		If[MemberQ[Attributes@Evaluate@ActualHead@Unevaluated@expr, NumericFunction],
			AllTrue[Unevaluated@expr, CNumberQ]
		,(*Else*)
			If[AtomQ[Unevaluated[expr]] && NumericQ[expr],
				True
			,(*Else*)
				False
			]
		]
	]


SetAttributes[NoDaggerQ, HoldAll]
NoDaggerQ[expr_?NonPatternQ] := MemberQ[noDagger, ActualHead@Unevaluated@expr]


SetAttributes[SpecificQ, HoldAll]
SpecificQ[f_] := MatchQ[Unevaluated@f, _Integer | _String]


(* ::Section::Closed:: *)
(*Rules for Dot[]*)


Unprotect[Dot];
Clear[Dot]
a_ . (b_ + c_) := a . b + a . c
(b_ + c_) . a_ := b . a + c . a
a_ . (c_?CNumberQ * b_) := Expand[c * (a . b)]
(c_?CNumberQ * b_) . a_ := Expand[c * (b . a)]
a_ . (c_?CNumberQ) := Expand[c * a]
(c_?CNumberQ) . a_ := Expand[c * a]
Protect[Dot];


(* ::Section::Closed:: *)
(*Rules for \[Delta][]*)


(* \[Delta][i, j] stands for Subsuperscript[\[Delta], i, j] *)
\[Delta] /: \[Delta][i_, j_] \[Delta][j_, k_] := \[Delta][i, k]
\[Delta] /: \[Delta][i_, i_] := Nc


(* ::Code::Initialization::Italic:: *)
\[Delta][expr_] := Module[{exprSimp = Simplify[expr]}, \[Delta][exprSimp]/; exprSimp=!=expr]
\[Delta]1[expr_] := Module[{exprSimp = Simplify[expr]}, \[Delta]1[exprSimp]/; exprSimp=!=expr]


(* ::Section::Closed:: *)
(*Rules for SU(N) Fundamental Representation Generators*)


T /: T[a_, i_, j_] T[a_, k_, l_] := 1/2 (\[Delta][i, l] \[Delta][k, j] - 1/Nc \[Delta][i, j] \[Delta][k, l])
T /: T[a_, i_, j_] \[Delta][j_, k_] := T[a, i, k]
T /: \[Delta][k_, i_]T[a_, i_, j_] := T[a, k, j]


(* ::Section::Closed:: *)
(*Definition of \[Theta][]*)


(* ::Text:: *)
(*NOTE: \[Theta][0] will be set to 0 by the convention of Piecewise[]. In fact, the convention of this package rules out all zero modes (k=0) of integrals, which in light-cone do have physical effects such as vacuum condensate. *)


\[Theta][x_?NumericQ] := \!\(\*
TagBox[GridBox[{
{"\[Piecewise]", GridBox[{
{"1", 
RowBox[{"x", ">", "0"}]},
{"0", 
RowBox[{"x", "<", "0"}]}
},
AllowedDimensions->{2, Automatic},
Editable->True,
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.84]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}},
Selectable->True]}
},
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.35]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}}],
"Piecewise",
DeleteWithContents->True,
Editable->False,
SelectWithContents->True,
Selectable->False,
StripWrapperBoxes->True]\)
\[Theta] /: \[Theta][x_]^p_Integer := \[Theta][x] /; p>1


\[Theta][expr_] := Module[{exprSimp = Simplify[expr]}, \[Theta][exprSimp]/; exprSimp=!=expr]


(* ::Section::Closed:: *)
(*Definition of Expi[]*)


Expi /: Expi[a_] Expi[b_] := Expi[a + b]
Expi /: Expi[a_] ^ b_ := Expi[a b]
Expi[0] := 1
Expi /: HC@Expi[x_] := Expi[-x]  (* NOTE: This must be prior to the other rules for HC[].  *)


(* ::Section::Closed:: *)
(*Definition of HC[]*)


HC::usage = 
"HC[expr] represents the Hermitian conjugate of expr. 
NOTE: It can not deal with functions with attribute NumericFunction which have complex values at the real axis. \
e.g. Log[x] at x<0. ";


HC[expr_?NumericQ] := Conjugate[expr]
HC[x_?RealValQ] := x
HC[expr_?(NonPatternQ[#]&&MatrixQ[#]&)] := Transpose[Map[HC, expr, {2}]]  (* Deal with matrices *)
HC[expr_Dot?NonPatternQ] := Reverse[HC/@expr]
HC[expr_?NonPatternQ]/;MemberQ[Attributes@Evaluate@ActualHead@expr, NumericFunction] := HC/@expr  (* NOTE: This is not always correct.  *)
HC[HC[expr_]] := expr
(* Otherwise *)
HC[expr_?(!AtomQ[#]&&!NoDaggerQ[#]&)] := If[First[expr]===\[Dagger], Rest[expr], Prepend[expr, \[Dagger]]]


(* ::Section::Closed:: *)
(*Definition of \[DoubleStruckCapitalD][]*)


\[DoubleStruckCapitalD]::usage = 
"\[DoubleStruckCapitalD][expr, x] represents a derivative that should not be evaluated by the built-in D[] function of Mathematica. ";


(* Linearity *)
\[DoubleStruckCapitalD][a_ + b_, x_] := \[DoubleStruckCapitalD][a, x] + \[DoubleStruckCapitalD][b, x]
\[DoubleStruckCapitalD][a_ b_, x_] := \[DoubleStruckCapitalD][a, x] b + a \[DoubleStruckCapitalD][b, x]
\[DoubleStruckCapitalD][a_ . b_, x_] := \[DoubleStruckCapitalD][a, x] . b + a . \[DoubleStruckCapitalD][b, x]
\[DoubleStruckCapitalD][a_, x_]/;FreeQ[a, x] := 0
(* Special functions *)
\[DoubleStruckCapitalD][\[Theta][krlt_], k_] := \[DoubleStruckCapitalD][krlt, k] \[Delta][krlt]
\[DoubleStruckCapitalD][\[Delta][krlt_], k_] := \[DoubleStruckCapitalD][krlt, k] \[Delta]1[krlt]
\[DoubleStruckCapitalD][Expi[a_], x_] := I \[DoubleStruckCapitalD][a, x] Expi[a]
\[DoubleStruckCapitalD][Int[expr_, kList__], x_]/;FreeQ[{kList}, x] := Int[\[DoubleStruckCapitalD][expr, x], kList]
\[DoubleStruckCapitalD][a_?(Not@*AtomQ), x_]/;!CNumberQ[a] := ReplacePart[a, 0 -> \[GothicCapitalD][Head[a], x]]  (* \[GothicCapitalD] is a new symbol *)
(* Otherwise *)
\[DoubleStruckCapitalD][a_, x_] := D[a, x]


(* ::Section:: *)
(*Definition of Int[]*)


(* Trivial integral *)
Int[0, __] := 0
(* Linearity *)
Int[a_ + b_, kList__] := Int[a, kList] + Int[b, kList]
Int /: (Longest[a_] Int[b_, kList__])/;AllTrue[{kList}[[All,1]], FreeQ[Unevaluated[a], #]&] := Int[a b, kList]
Int /: (Longest[a_] . Int[b_, kList__])/;AllTrue[{kList}[[All,1]], FreeQ[Unevaluated[a], #]&] := Int[a . b, kList]
Int /: (Int[b_, kList__] . Longest[a_])/;AllTrue[{kList}[[All,1]], FreeQ[Unevaluated[a], #]&] := Int[b . a, kList]
(* Auto-expand inside the integral *)
Int[a_?NonPatternQ, kList__] := 
	Module[{a1 = Expand[a]},
		Int[a1, kList] /; a1=!=a
	]
(* Combine iterated integrals *)
Int[Int[a_, kList2__], kList1__] := Int[a, kList2, kList1]
(* Commute with HC *)
Int /: HC@Int[expr_, kList__] := Int[HC@expr, kList]


(* Integral with Expi[] is done automatically *)
(* NOTE: The FreeQ[] below cannot distinguish two variables such as x and Subscript[x, 1], i.e. Subscript[x, 1] is regarded not free of x. *)
Int[Expi[kx_] subexpr_., OrderlessPatternSequence[{x_, -\[Infinity], \[Infinity]} , xResList___]]/;FreeQ[Unevaluated[subexpr], x] := 
	If[Length[{xResList}] == 0,
		(2\[Pi]) \[Delta][Coefficient[kx, x]] Expi[Coefficient[kx, x, 0]] subexpr
	,(*Else*)
		Int[(2\[Pi]) \[Delta][Coefficient[kx, x]] Expi[Coefficient[kx, x, 0]] subexpr, xResList]
	]

Int[x_ Expi[kx_] subexpr_., OrderlessPatternSequence[{x_, -\[Infinity], \[Infinity]} , xResList___]]/;FreeQ[Unevaluated[subexpr], x] := 
	If[Length[{xResList}] == 0,
		(2\[Pi])/I \[Delta]1[Coefficient[kx, x]] Expi[Coefficient[kx, x, 0]] subexpr
	,(*Else*)
		Int[(2\[Pi])/I \[Delta]1[Coefficient[kx, x]] Expi[Coefficient[kx, x, 0]] subexpr, xResList]
	]


(* ::Text:: *)
(*NOTE: Due to the bug of Mathematica (up to 12.1), underline (_) followed by Greek letters sometimes breaks automatically. So I directly write down the full form of the patterns. *)


ReduceIntRegion::usage = 
"ReduceIntRegion[expr] tries to reduce integration regions in expr which is restricted by \[Theta][], \[Delta][] and \[Delta]1[] functions. ";
ReduceIntRegion[expr_] := expr /. {
	(* Integral with \[Theta][] *)
	Int[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"thetas", ",", " ", 
RowBox[{"BlankSequence", "[", "\\[Theta]", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\) subexpr___, kList__]/;FreeQ[{subexpr}, \!\(\*
TagBox[
StyleBox[
RowBox[{"Blank", "[", "\\[Theta]", "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)] :>
	Module[{region, vars, thetaProd, flag},
		Int[thetaProd Times[subexpr], kList]/;(
		region = AllTrue[{kList}, #[[2]] < #[[1]] < #[[3]]&] && AllTrue[positiveAssumptions, # > 0&];  (* Initial region is generated by the range of integration *)
		vars = Union[{kList}[[All,1]], Variables[positiveAssumptions], Variables[First/@{thetas}]];
		thetaProd = 1;
		flag = False;  (* Whether a reduction of integral is possible *)
		Do[
			If[Resolve[ForAll[Evaluate@vars, region \[Implies] First[t] > 0]] === True,  (* If \[Theta][] = 1 can be deduced from the current region *)
			(*True*)
				flag = True;
			,(*False*)
				If[SubsetQ[vars, Variables@First[t]], (* Restrict the power of \[Theta][] reduction *)
					region = Reduce[region && First@t > 0, vars]  (* Modify the region to include the restriction imposed by the \[Theta][] *)
				];
				If[region === False,   (* If the region has been reduced to empty set *)
					thetaProd = 0; flag = True; Break[]; 
				,(*Else*)
					thetaProd *= t;
				];
			],
			{t, {thetas}}
		];
		flag
		)
	],

	(* Trivial integral with \[Delta][], \[Delta]1[] *)
	Int[(((\[Delta]|\[Delta]1)[krlt_]^(i_Integer:1)/;i>0)
	|((\[Delta]|\[Delta]1)[krlt_]^(i_Integer:1)/;i>0) \!\(\*
TagBox[
RowBox[{
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"thetas", ",", " ", 
RowBox[{"BlankNullSequence", "[", "\\[Theta]", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True], 
StyleBox["\n",
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True], "\t"}],
FullForm]\)) subexpr_., kList__]/;FreeQ[subexpr, Blank[\[Theta]]] :>
	Module[{region, kVars},
		0 /;(
		(* If the support set of integrand does not contain singularities of \[Delta][] *)
		region = AllTrue[{kList}, #[[2]] < #[[1]] < #[[3]]&] && AllTrue[{thetas}, First@#>0&];
		kVars = {kList}[[All,1]];
		Resolve[ForAll[Evaluate@kVars, region \[Implies] krlt > 0 || krlt < 0]]
		)
	]
}


ParseIneq[ineq_, x_] := Replace[ineq, {
	x < u_ :> {x, -\[Infinity], u},
	x > l_ :> {x, l, \[Infinity]},
	Inequality[l_, Less, x, Less, u_] :> {x, l, u},
	iiee_ :> All
}]

AdvancedReduceIntRegion::usage = 
"AdvancedReduceIntRegion[expr] tries to reduce integration regions restricted by \[Theta][] into upper & lower limit. ";
AdvancedReduceIntRegion[expr_] := expr /. {
	(* Integral with \[Theta][] *)
	Int[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"thetas", ",", " ", 
RowBox[{"BlankSequence", "[", "\\[Theta]", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\) subexpr___:1, kList__]/;FreeQ[{subexpr}, \!\(\*
TagBox[
StyleBox[
RowBox[{"Blank", "[", "\\[Theta]", "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)] :>
	Module[{region = AllTrue[positiveAssumptions, # > 0&] \
				&& AllTrue[{kList}, #[[2]] < #[[1]] < #[[3]]&] \
				&& (And@@({thetas} /. \[Theta][ex_] :> ex > 0)),
			exVars = ECHOLABEL["exVars"]@Complement[Join[positiveAssumptions, Variables[First/@{thetas}]], {kList}[[All,1]]],
			inVars = ECHOLABEL["inVars"]@DeleteDuplicates[{kList}[[All,1]]],
			decomp, temp, kListNew},
			
		Int[Times[subexpr], Sequence@@kListNew] /; Catch[
			decomp = Check[ECHOLABEL["CyDec"]@CylindricalDecomposition[region, exVars ~Join~ inVars], Throw[False]];
			If[Not@FreeQ[decomp, Or], Throw[False]];
			decomp = ECHOLABEL["decomp"]@Replace[decomp, {
				HoldPattern@And[range__] :> {range},
				range_ :> {range}
			}];
			Do[If[ParseIneq[First@decomp, var] =!= All, decomp = Rest[decomp]], {var, exVars}];
			kListNew = Table[
				temp = ECHOLABEL["Parse"]@ParseIneq[First@ECHOLABEL["decomp"]@decomp, ECHOLABEL["var"]@var];
				If[temp =!= All, decomp = Rest[decomp]; temp, {var, -\[Infinity], \[Infinity]}],
				{var, inVars}
			];
			True
		]
	]
}


ComputeInt::usage = 
"ComputeInt[expr, {k1, k2, ...}] computes the integrals with nontrivial \[Delta][] and \[Delta]1[] on k1, k2, ..., \
successively";
rulesForComputeInt[p_] := {
	(* Eliminate \[Delta][] associated with specific p *)
	(* NOTE: It can only handle linear expressions inside \[Delta][]. *)
	HoldPattern@Int[(\[Delta][krlt_]^(i_Integer:1)/;i>0) subexpr_., kList__] :> 
		Module[{ik = FirstPosition[{kList}[[All,1]], p, Missing["NotFound"], {1}, Heads->False],
				k, klb, kub,
				k0},
			(
			ik = First[ik];
			k = {kList}[[ik,1]]; klb = {kList}[[ik,2]]; kub = {kList}[[ik,3]];
			k0 = (-Coefficient[krlt, k, 0]/Coefficient[krlt, k]);
			If[Length[{kList}] == 1,
				(\[Delta][krlt]^(i-1) subexpr/.k->k0) (If[klb===-\[Infinity], 1, \[Theta][k0-klb]] If[kub===+\[Infinity], 1, \[Theta][kub-k0]])/Abs@Coefficient[krlt, k],
			(*Else*)
				Int[
					(\[Delta][krlt]^(i-1) subexpr/.k->k0) (If[klb===-\[Infinity], 1, \[Theta][k0-klb]] If[kub===+\[Infinity], 1, \[Theta][kub-k0]])/Abs@Coefficient[krlt, k],
					Sequence@@Delete[{kList}, ik]
				]
			]
			)/;!MissingQ[ik] && MemberQ[krlt, p, {0, \[Infinity]}]
		],
	(* Eliminate \[Delta]1[] associated with specific p *)
	(* NOTE: It can only handle linear expressions inside \[Delta]1[]. *)
	HoldPattern@Int[\[Delta]1[krlt_] subexpr_., kList__] :> 
		Module[{ik = FirstPosition[{kList}[[All,1]], p, Missing["NotFound"], {1}, Heads->False],
				k, klb, kub,
				k0},
			(
			ik = First[ik];
			k = {kList}[[ik,1]]; klb = {kList}[[ik,2]]; kub = {kList}[[ik,3]];
			k0 = (-Coefficient[krlt, k, 0]/Coefficient[krlt, k]);
			If[Length[{kList}] == 1,
				(-\[DoubleStruckCapitalD][subexpr, k]/.k->k0) (If[klb===-\[Infinity], 1, \[Theta][k0-klb]] If[kub===+\[Infinity], 1, \[Theta][kub-k0]])/Abs@Coefficient[krlt, k],
			(*Else*)
				Int[
					(-\[DoubleStruckCapitalD][subexpr, k]/.k->k0) (If[klb===-\[Infinity], 1, \[Theta][k0-klb]] If[kub===+\[Infinity], 1, \[Theta][kub-k0]])/Abs@Coefficient[krlt, k],
					Sequence@@Delete[{kList}, ik]
				]
			]
			)
			/;!MissingQ[ik] && MemberQ[krlt, p, {0, \[Infinity]}]
		]
}
ComputeInt[expr_, pList_List] := 
	If[Length[pList] == 1,
		expr /. rulesForComputeInt[First@pList]
	,(*Else*)
		ComputeInt[
			expr /. rulesForComputeInt[First@pList],
			Rest[pList]
		]
	]

ComputeInt[pList_List] := ComputeInt[#, pList]&


ChangeIntVar::usage = 
"ChangeIntVar[expr, k, p, kExpressedByp] change the integration variable k to p with relation pExpressedByk";
ChangeIntVar::not1to1 = "`` solution(s) found. ";
ChangeIntVar[expr_, k_, p_, pExpressedByk_] := expr /. {
	Int[subexpr_, kList__] :> 
		Module[{ik = FirstPosition[{kList}[[All,1]], k, Missing["NotFound"], {1}, Heads->False],
				klb, kub, kEx, 
				jac = 1, plb, pub
				},
			ik = First[ik]; klb = {kList}[[ik,2]]; kub = {kList}[[ik,3]];
			kEx = Solve[p == pExpressedByk, k];
			If[Length[kEx]=!=1, Message[ChangeIntVar::not1to1, Length[kEx]]; Abort[]];
			plb = Simplify[pExpressedByk/.k->klb]; pub = Simplify[pExpressedByk/.k->kub];
			If[pub < plb || pub == -\[Infinity] || plb == \[Infinity], jac=-1; {plb, pub} = {pub, plb}];
			jac = Simplify[jac D[k/.First[kEx], p]];
			Int[jac subexpr/.First[kEx], Sequence@@MapAt[{p, plb, pub}&, {kList}, ik]] /; !MissingQ[ik]
		]
}

ChangeIntVar[k_, p_, pExpressedByk_] := ChangeIntVar[#, k, p, pExpressedByk]&


PermuteIntOrder::usage =
"PermuteIntOrder[expr, perm] permutes the integration variables by perm. Used for the correction of the integration order \
after ChangeIntVar[]. ";
PermuteIntOrder[expr_, perm_] := expr /. {
	Int[ex_, kList__] :> Int[ex, Sequence@@Permute[{kList}, perm]]
}

PermuteIntOrder[perm_] := PermuteIntOrder[#, perm]&


SimplifyInt::usage = 
"SimplifyInt[expr]
SimplifyInt[expr, SimpFunc] simplifies integrands using the function given by SimpFunc. SimpFunc = Simplify by default. ";
rulesForSimplifyInt[SimpFunc_] := {
	Plus[Longest[IntList__Int], rest___] :>
		Module[{case},
			case = Cases[{IntList}, Int[expr_, kList__] :> <|{kList}->expr|>];
			case = Merge[case, SimpFunc@Total[#]&];
			Total[KeyValueMap[Int[#2, Sequence@@#1]&, case]] + Plus[rest]
		]
}

SimplifyInt[expr_, SimpFunc_:Simplify] := Expand[expr]/.rulesForSimplifyInt[SimpFunc]


(* ::Section::Closed:: *)
(*Flavor indices*)


(* \[Delta]f[f1, f2] stands for Subsuperscript[\[Delta], f1, f2] *)
\[Delta]f[f1_?SpecificQ, f2_?SpecificQ] := If[f1 === f2, 1, 0];


Sum\[Delta]f::usage = 
"Sum\[Delta]f[expr] sums up all the unspecific flavor indices. expr[...f1...] stands for summation of f1. \
If a term in expr has no f1, f1 is not summed. ";
Sum\[Delta]f[expr_] := expr//.{
    (* Sum out f2(f1) and at the same time retain f1(f2).  *)
	\[Delta]f[f1_, f2_?(Not@*SpecificQ)]^(_Integer:1) Longest[rest_.]/; !FreeQ[Unevaluated[rest], f2] :> (Unevaluated[rest]/.f2 -> f1),
	\[Delta]f[f1_?(Not@*SpecificQ), f2_]^(_Integer:1) Longest[rest_.]/; !FreeQ[Unevaluated[rest], f1] :> (Unevaluated[rest]/.f1 -> f2),
	(* Sum out f1(f2) which only appear in the \[Delta]f[]. *)
	\[Delta]f[f1_?(Not@*SpecificQ), f2_?(Not@*SpecificQ)]^(_Integer:1) Longest[rest_.] /; FreeQ[Unevaluated[rest], f1]&&FreeQ[Unevaluated[rest], f2] :> Nf rest,
	\[Delta]f[f1_?(Not@*SpecificQ), f2_?SpecificQ]^(_Integer:1) Longest[rest_.] /; FreeQ[Unevaluated[rest], f1] :> rest,
	\[Delta]f[f1_?SpecificQ, f2_?(Not@*SpecificQ)]^(_Integer:1) Longest[rest_.] /; FreeQ[Unevaluated[rest], f2] :> rest
}


(* ::Section::Closed:: *)
(*(Anti-)Commutation Relations*)


CC::usage = "CC[a, b] is the commutator [a, b]. ";
AC::usage = "AC[a, b] is the anti-commutator {a, b}. ";


(* General *)
(* 1. Factor out c-numbers *)
CC[c_?CNumberQ * a_, b_] := Expand[c * CC[a, b]]
CC[a_, c_?CNumberQ * b_] := Expand[c * CC[a, b]]
CC[a_, b_]/;(CNumberQ[a]||CNumberQ[b]) := 0
AC[c_?CNumberQ * a_, b_] := Expand[c * AC[a, b]]
AC[a_, c_?CNumberQ * b_] := Expand[c * AC[a, b]]
AC[a_, b_]/;(CNumberQ[a]||CNumberQ[b]) := 2 a b
(* 2. Distributive law *)
CC[a_, b_ + c_] := CC[a, b] + CC[a, c]
CC[b_ + c_, a_] := CC[b, a] + CC[c, a]
AC[a_, b_ + c_] := AC[a, b] + AC[a, c]
AC[b_ + c_, a_] := AC[b, a] + AC[c, a]
CC[a_, Int[b_, kList__]]/;AllTrue[{kList}[[All,1]], FreeQ[a, #]&] := Int[CC[a, b], kList]
CC[Int[b_, kList__], a_]/;AllTrue[{kList}[[All,1]], FreeQ[a, #]&] := Int[CC[b, a], kList]
AC[a_, Int[b_, kList__]]/;AllTrue[{kList}[[All,1]], FreeQ[a, #]&] := Int[AC[a, b], kList]
AC[Int[b_, kList__], a_]/;AllTrue[{kList}[[All,1]], FreeQ[a, #]&] := Int[AC[b, a], kList]
(* 3. Commute, or anti-commute *)
CC[a_, b_Dot]/;Head[a]=!=Dot := -CC[b, a]
AC[a_, b_Dot]/;Head[a]=!=Dot := AC[b, a]
(* 4. Decomposition of product *)
(* NOTE: It's assumed that the operators inside CC[] and AC[] are appropriate.
i.e. CC[ccOp, ccOp], CC[ccOp, acOp], CC[acOp, ccOp] or AC[acOp, acOp].  *)
CC[Shortest[a_]?ACOpQ . b_?ACOpQ, c_?ACOpQ] := a . AC[b, c] - AC[a, c] . b
(* Otherwise *)
CC[Shortest[a_] . b_, c_] := a . CC[b, c] + CC[a, c] . b
(*  *)
AC[Shortest[a_]?ACOpQ . b_?(Not@*ACOpQ), c_?ACOpQ] := a . CC[b, c] + AC[a, c] . b
AC[Shortest[a_]?(Not@*ACOpQ) . b_?ACOpQ, c_?ACOpQ] := a . AC[b, c] - CC[a, c] . b
(* 5. Relation with HC[] *)
CC /: HC@CC[a_, b_] := CC[HC[b], HC[a]]
AC /: HC@AC[a_, b_] := AC[HC[b], HC[a]]


(* ::Section::Closed:: *)
(*Operator Ordering*)


NormalOrdering::usage = 
"NormalOrdering[expr] calculates the normal ordered version of the expression expr. ";
rulesForNormalOrdering = {
	(* To be determinted in SingleFlavor.wl & MultipleFlavors.wl *)
};
NormalOrdering[expr_] := (Expand[expr]//.rulesForNormalOrdering)//Expand


VacExp::usage = 
"VacExp[expr] calculates the vacuum expectation value of the operator expr. ";
rules4VacExp = {
	(* To be determinted in SingleFlavor.wl & MultipleFlavors.wl *)
};
VacExpSub[prod_List, rules_] := (
	If[prod === {}, Return[1]];
	If[First[First[prod], Null] === \[Dagger],
		0
	,(*Else*)
		Module[{repList},
			repList = ReplaceList[prod, rules];
			If[repList === {},
				0,
				Total@Apply[#1 VacExpSub[#2, rules]&, repList, 1]
			]
		]
	]
)
Options[VacExp] = {
	"Rules" -> rules4VacExp
};
VacExp[expr_, OptionsPattern[]] := 
	Module[{exExpr = Expand[expr]},
		exExpr = If[Head[exExpr] === Plus, List@@exExpr, List@exExpr];
		Replace[#, {
			Int[(Longest[c_.] o_)/;CNumberQ[c]&&!CNumberQ[o], kList__] :> 
				Int[(c If[Head[o] === Dot, VacExpSub[List@@o, OptionValue["Rules"]], VacExpSub[List@o, OptionValue["Rules"]]]), kList],
			Except[_Int, (Longest[c_.] o_)/;CNumberQ[c]&&!CNumberQ[o]] :> 
				(c If[Head[o] === Dot, VacExpSub[List@@o, OptionValue["Rules"]], VacExpSub[List@o, OptionValue["Rules"]]])
		}]&/@exExpr//Total
	]


BosonOrdering::usage = 
"BosonOrdering[expr] rearranges the expresion expr to match the bosonized operators. ";
rulesForBosonOrdering  = {
	(* To be determinted in SingleFlavor.wl & MultipleFlavors.wl *)
};
BosonOrdering[expr_] := (Expand[expr]//.rulesForBosonOrdering)//Expand


(* ::Section:: *)
(*Import Rules for a, b, c, d Operators*)


If[Global`$MultipleFlavors === True,
	Get[FileNameJoin[{DirectoryName[$InputFileName], "MultipleFlavors.wl"}]],
	Get[FileNameJoin[{DirectoryName[$InputFileName], "SingleFlavor.wl"}]]
]


(* ::Section:: *)
(*Utility Functions*)


MyExponent[expr_, var_] := Module[{exprEx = Expand[expr]}, MyExponent[exprEx, var] /; exprEx=!=expr]
MyExponent[HoldPattern@Plus[expr__], var_] := Max[MyExponent[#, var]& /@ {expr}]
MyExponent[Int[expr_, __], var_] := MyExponent[expr, var]
MyExponent[expr_, var_] := Exponent[expr, var]


Fac::usage = 
"Fac[fac] prevents factors in fac being calculated automatically by Int[] and ComputeInt[]. It is normally \
generated by WrapIntegrandFactors[] and CollectLikeTerms[]. To remove Fac[], simply apply the rule Fac -> Identity. "
Fac /: Fac[a_]Fac[b_] := Fac[a b]
Fac[a_?(!FreeQ[#,Fac]&)] := Fac[a/.Fac->Identity]
(* Commute with HC *)
Fac /: HC@Fac[expr_] := Fac[HC@expr]


WrapIntegrandFactors::usage = 
"WrapIntegrandFactors[expr] recognizes complicated factors in Int[] that are irrelevant to the calculation and \
wrap them with Fac[]. This speeds up the the calculation. Fac[] can be removed afterwards simply by applying \
the rule Fac -> Identity. ";
WrapIntegrandFactors[expr_] := Expand[expr]/.{
	Int[(fac_?CNumberQ) Shortest[subexpr_], kList__]/;
		AllTrue[{Expi, \[Delta]f, T, \[Delta], \[Delta]1, \[Theta]}, FreeQ[fac, #]&] && AllTrue[{kList}[[;;,1]], Exponent[fac, #] <= 0&]
		:> Int[Fac[fac] subexpr, kList]
}


RenumberIndex::usage = 
"RenumberIndex[expr, {c, ic}, {k, ik}, ...] renumbers subscripted indices of c, k, ... starting from ic, ik, ... \
respectively. ";

(* Index management *)
knownIndices = {<||>, 0};

RenumberIndexMono[mono_, var_] := mono /. Subscript[var, j_] :> (
	If[!KeyExistsQ[knownIndices[[1]], j], 
		AppendTo[knownIndices[[1]], j -> knownIndices[[2]]++]
	];
	Subscript[var, knownIndices[[1]][j]]
)
RenumberIndexSub[expr_, varList__] := 
	Module[{
		var = First[{varList}][[1]], i = First[{varList}][[2]],
		rs
	},
		knownIndices = {<||>, i};
		rs = If[Head[expr] === Plus,  (* Polynomial *)
			RenumberIndexMono[#, var]&/@expr
		,(*Else*)  (* Monomial *)
			RenumberIndexMono[expr, var]
		];
		If[Length[{varList}] == 1,
			rs
		,(*Else*)
			RenumberIndexSub[rs, Sequence@@Rest[{varList}]]
		]
	]
RenumberIndex[expr_, varList__] := RenumberIndexSub[Expand[expr], varList]


CollectLikeTerms::usage = 
"CollectLikeTerms[expr]
CollectLikeTerms[expr, {dummy1, dummy2, ...}] collects like integral terms with respect to the operator product. \
Dummy indices should be designated explicitly. ";

NewVariable[name_String] := Unique[name, {Temporary}]

(* TODO: ... *)
CollectLikeTerms[expr_, dummyList_List] := 
	Module[
	{
		exExpr = Expand[expr],
		A, B,
		coefA, opA, kListA,
		coefB, opB, kListB, kListBInf, opB2,
		opPatt, kListPatt,
		dummyRules = (NewVariable["dummy"] -> #)&/@dummyList,
		allRules, allRulesInv,
		B2ARules,
		ptr, match,
		result = 0
	},
	If[Head[exExpr] === Plus,  (* If polynomial *)
		exExpr = List@@exExpr;  (* Change sum into list *)
		While[exExpr =!= {},
			A = First[exExpr]; exExpr = Rest[exExpr];  (* Pop *)
			(* If not the form of interest *)
			If[!MatchQ[A, Int[Longest[c_.] o_/;CNumberQ[c]&&!CNumberQ[o], kList__]], result += A; Continue[]];
			allRules = dummyRules;
			{coefA, opA, kListA} = Replace[A, 
				Int[Longest[c_.] o_/;CNumberQ[c]&&!CNumberQ[o], kList__] :> (
					allRules = allRules ~Join~ (
						(NewVariable["intVar"] -> #)& /@ Cases[{kList}, {k_, _, _} :> k]
					);
					{c, o, {kList}}
				)
			];
			(* Generate operator pattern for  *)
			allRulesInv = (allRules/.{(x_ -> y_) :> (y -> Pattern[Evaluate[x], Blank[]])});
			opPatt = opA /. allRulesInv;
			kListPatt = OrderlessPatternSequence@@(kListA/.allRulesInv);

			ptr = 1;
			While[ptr <= Length[exExpr],
				B = exExpr[[ptr]];
				(* If not the form of interest *)
				If[!MatchQ[B, Int[Longest[c_.] o_/;CNumberQ[c]&&!CNumberQ[o], kList__]], ptr++; Continue[]];
				{coefB, opB, kListB} = Replace[B, 
					Int[Longest[c_.] o_/;CNumberQ[c]&&!CNumberQ[o], kList__] :> {c, o, {kList}}
				];
				(* If kList of B is not the same with A *)
				If[!MatchQ[kListB, {kListPatt}], ptr++; Continue[]];
				kListBInf = Cases[kListB, {k_, -\[Infinity], \[Infinity]} :> k];
				Do[
					opB2 = opB/.Thread[kListBInf -> MapThread[Times, {sgn, kListBInf}]];
					If[MatchQ[{opB2, kListB}, {opPatt, {kListPatt}}],
						B2ARules = Replace[{opB2, kListB},
							{opPatt, {kListPatt}} :> Evaluate[allRules]
						];
						coefA += coefB/.B2ARules;
						exExpr = Delete[exExpr, ptr]; ptr--;
						Break[];
					],
					{sgn, Tuples[{1, -1}, Length[kListBInf]]}
				];
				ptr++;
			];
			result += Int[Fac[coefA] opA, Sequence@@kListA];
		];
		result
	,(*Else*)
		exExpr
	]
]
CollectLikeTerms[expr_] := CollectLikeTerms[expr, {}]


(* ::Section::Closed:: *)
(*Output Typesetting*)


\[Delta] /: MakeBoxes[\[Delta][i_, j_], tf:TraditionalForm] := SubsuperscriptBox["\[Delta]", MakeBoxes[i, tf], MakeBoxes[j, tf]]
\[Delta]f /: MakeBoxes[\[Delta]f[f1_, f2_], tf:TraditionalForm] := SubsuperscriptBox["\[Delta]f", MakeBoxes[f1, tf], MakeBoxes[f2, tf]]
\[Gamma] /: MakeBoxes[\[Gamma][i_, s1_, s2_], tf:TraditionalForm] := 
	SubsuperscriptBox[
		RowBox[{"(", SuperscriptBox["\[Gamma]", MakeBoxes[i, tf]], ")"}], 
		MakeBoxes[s1, tf], MakeBoxes[s2, tf]
	]

(* Parameters *)
gs /: MakeBoxes[gs, TraditionalForm] := SubscriptBox["g", "s"]
Nc /: MakeBoxes[Nc, TraditionalForm] := SubscriptBox["N", "c"]
T /: MakeBoxes[T[a_, i_, j_], tf:TraditionalForm] := 
	SubsuperscriptBox[
		RowBox[{"(", SuperscriptBox["T", MakeBoxes[a, tf]], ")"}], 
		MakeBoxes[i, tf], MakeBoxes[j, tf]
	]

(* For Expi[] *)
Expi /: MakeBoxes[Expi[expr_], tf:TraditionalForm] := SuperscriptBox["\[ExponentialE]", ToBoxes[I expr, tf]]

(* For Int[] *)
Int /: MakeBoxes[Int[expr_, {k_,klb_,kub_}, kListRest___], tf:TraditionalForm] :=
	RowBox[{
		If[klb===-\[Infinity] && kub===+\[Infinity],
			"\[Integral]",
		(*Else*)
			SubsuperscriptBox["\[Integral]", MakeBoxes[klb, tf], MakeBoxes[kub, tf]]
		],
		"\[DifferentialD]", MakeBoxes[k, tf],
		If[Length[{kListRest}] == 0,
			MakeBoxes[expr, tf],
		(*Else*)
			MakeBoxes[Int[expr, kListRest], tf]
		]
	}]
	
(* For Fac[] *)
Fac /: MakeBoxes[Fac[expr_], tf:TraditionalForm] := 
	StyleBox[RowBox[{"(", MakeBoxes[expr, tf], ")"}], FontColor -> Blue]


(* ::Section::Closed:: *)
(*End*)


End[];


EndPackage[];
