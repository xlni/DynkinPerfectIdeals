newPackage(
    "DynkinPerfectIdeals",
    Version => "1.0",
    Date => "January 24, 2022",
    Authors => {
	{Name => "Xianglong Ni",
	    Email => "xlni@berkeley.edu",
	    HomePage => "https://math.berkeley.edu/~xlni/"
	    }
	},
    Headline => "(conjecturally) generic examples of perfect resolutions",
    AuxiliaryFiles => true,
    DebuggingMode => false
    )

export {
    "LieAlgebraCache",
    "fillBracket",
    "Jacobi",
    "name",
    "newRep",
    "Ltog",
    "L0tog",
    "LieAlgebraRep",
    "newLieAlgebra",
    "LieAlgebra",
    "lieAlgebra",
    "action",
    "actionHT",
    "checkRep",
    "generate",
    "subRep",
    "quotientRep",
    "alg",
    "gl",
    "igl",
    "tr",
    "wedgeDiag",
    "isl",
    "sl",
    "psl",
    "completeIrrepAction",
    "extendMap",
    "trivialRep",
    "invariants",
    "equivariantMaps",
    "glLie",
    "soLie",
    "slLie",
    "glStandard",
    "schurRep",
    "adjointRep",
    "tensorRep",
    "dualRep",
    "bracket",
    "repFromGradedAction",
    "completeGradedAction",
    "parametricAction",
    "adj",
    "extremalRep",
    "genericBigrade",
    "genericMultigrade",
    "topComplex",
    "genericGorIndexing",
    "lengthThreeVars",
    "subAlgebra",
    "safeInc",
    "algebra",
    "Sign",
    "defectLieAlgebraDual",
    "formatLookup",
    "mapInfo"
    }

needsPackage "SchurFunctors"

------------------------------------------------
-- Cache for storing Lie algebra computations --
------------------------------------------------

LieAlgebraCache = new MutableHashTable;

---------------------
-- Auxiliary files --
---------------------

--wedgeDiag, working with reps, etc.
load "./DynkinPerfectIdeals/BasicMethods.m2"

--initializing Lie algebra data
load "./DynkinPerfectIdeals/LieAlgebras.m2"

--actually constructing the resolutions
load "./DynkinPerfectIdeals/GenericResolutions.m2"

end
uninstallPackage "DynkinPerfectIdeals"
restart
installPackage "DynkinPerfectIdeals";
needsPackage "DynkinPerfectIdeals";
needsPackage "SchurFunctors"

frmt={1,7,12,7,1}
g = lieAlgebra formatLookup frmt; g' = truncate(g,0)
--start here for demonstration
ggen = genericMultigrade(g,u); S = ring ggen;
--keep only the variables with strictly positive multidegree
L = {1,2}/(i->i-1)
R = prune (S/ideal(select(gens S, i -> not all((degree i)_L,j->j>0)))) 
ggen = sub(ggen,R)
ggen' = g'_[0,-1,-2,-3]*g^[0,-1,-2,-3]*ggen;

zgen = map(module g',QQ^1,0)
F = topComplex(frmt,ggen')


debugLevel = 1

--1562 d2 d3 broken

--all length 4 stuff broken...













g = lieAlgebra("E",7)

so = soLie(QQ^6) -- so(12)

CM = fold(apply(6, i -> ((bracket g)*(g.cache#"h"**g.cache#"e"_{i}))//g.cache#"e"_{i}), (a,b)->a||b)

(bracket so)*(so.cache#"h"**so.cache#"e"_{1})
g=so


L = {7,6,5,4,2,3}/(i->i-1)

so = slLie(QQ^6)
L = {7,6,3,4,2}/(i->i-1)

debugLevel = 1
extendMap(so.cache#"e"|so.cache#"f", so, g.cache#"e"_L|g.cache#"f"_L,g);


--implement so(M+M')?
n=8;
kk = QQ; M = kk^n
MM = directSum("M"=>M, "M*" => dual M)

qform = MM_["M*"]*MM^["M"] + MM_["M"]*MM^["M*"]

g = glLie MM

--use "generate" to get so?
--Li - Lj
(i,j)=(0,1)
e = apply(
    apply(toList(1..(n-1)),i -> (i-1,i)), (i,j) -> 
    MM_["M"]*map(M,M,{(i,j)=>1})*MM^["M"] + MM_["M*"]*map(dual M, dual M,{(j,i)=>1})*MM^["M*"]
    )
elast = MM_["M"]*map(M,dual M,{(n-2,n-1)=>1})*MM^["M*"] - MM_["M"]*map(M,dual M,{(n-1,n-2)=>1})*MM^["M*"]

f = e/transpose
flast = (transpose elast)
e = MM_["M"]*map(M,dual M,{(i-1,j-1)=>1})

ee = fold(apply(e|{elast},x -> flip(dual MM, MM)*adjoint(x,kk^1,MM)), (a,b)->a|b)
ff = fold(apply(f|{flast},x -> flip(dual MM, MM)*adjoint(x,kk^1,MM)), (a,b)->a|b)

h = fold(apply(numcols ee, i -> (bracket g)*(ee_{i}**ff_{i})), (a,b)->a|b)

fold(apply(numcols h, i -> ((bracket g)*(h**ee_{i}))//ee_{i}), (a,b)->a||b)

soinc = generate(ee|ff,glLie(MM));
so = subAlgebra(soinc,glLie(MM))

so.cache#"e" = ee//soinc; so.cache#"f" = ff//soinc; so.cache#"h" = h//soinc;
CM = fold(apply(numcols h, i -> ((bracket so)*(h**ee_{i}))//ee_{i}), (a,b)->a||b)
so.cache#"alpha" = (inverse CM)*so.cache#"h"









--next task: fully weight-grade the defect algebra?

frmt={1,5,6,2}
g = lieAlgebra formatLookup frmt; g'=truncate(g,0);
x = new IndexedVariableTable

-- 2 4 5 6
--   3
--   1


-- 6 4 3 2 1
--   5

ggen = genericMultigrade(g,x); S = ring ggen;
--keep only the variables with strictly positive multidegree
R = prune (S/ideal(select(gens S, i -> not all((degree i)_{1,2},j->j>0)))) 
ggen = sub(ggen,R)
ggen' = g'_[0,-1,-2,-3]*g^[0,-1,-2,-3]*ggen;

F=topComplex(frmt,ggen')

M = (matrix degrees source F.dd_1)**QQ
--kernel
K = matrix{{-2,0,1,0,0,0}}

L=(unique permutations {3,3,3,4,6})/(i->(QQ**(dual matrix{i}))//M)


M = (matrix degrees source F.dd_2)**QQ
deg2 = {4,5,5,5,8,10}

XList = apply(unique permutations deg2, i-> (inverse M)*(transpose matrix{i}))

--start here for demonstration
ggen = genericMultigrade(g,u); S = ring ggen;
--keep only the variables with strictly positive multidegree
R = prune (S/ideal(select(gens S, i -> not all((degree i)_{1,2},j->j>0)))) 
ggen = sub(ggen,R)
ggen' = g'_[0,-1,-2,-3]*g^[0,-1,-2,-3]*ggen;

Rran = ZZ/32003[x,y,z]
testran = X -> sub(ggen',
    apply(gens R, i -> (
	    degvec := ((matrix{degree i})*(dual matrix {X}))_(0,0);
	    if liftable(degvec,ZZ) then (
		return i => random(lift(degvec,ZZ),Rran)
		) else (
		return i => 0
		)
	    )
	)
    )

gran = testran X;
F = topComplex(frmt,gran)
isHomogeneous F
prune HH F
prune HH dual F
betti F

setRandomSeed "hello"
--(2,2,5,5,5)
X = {-4,-3,4,0,0,3}

--(2,3,4,4,6)
X = {4,-4,-1,2,0,1}

--(2,3,4,5,5)
X = {4,-3,0,0,1,1}

--(3,3,3,3,7), (3,3,3,4,6) all "graded substitutions" were zero
--(3,3,3,5,5) got nonzero substitution possibilities but none yielded a resolution

--(3,4,4,4,5)
X = {4,-1,-2,1,0,1}



testgen = sub(ggen',
    apply(gens R, i -> (
	    if (degree i)_0 == 0 then return i => 1 else return i => i))
    )
F=topComplex(frmt,testgen)

I = ideal F.dd_3
1%I

prune HH F

S = QQ[a_1..a_3]
index S_0

baseName S_0


L = {a}
S = QQ L



genericMultigrade = method();
genericMultigrade (LieAlgebra,Thing) := Matrix => (g,x) -> (
    kk := ring module g;
    n := numcols g.cache#"e";
    grd := apply(n, i -> (bracket g)*(g.cache#"alpha"_{i}**id_(module g)));
    degmax := apply(n, i -> (
	    j := 0;
    	    while not zero ker (grd#i+j) do j = j+1;
    	    return j
	    )
	);
    hgrade := hashTable {{}=>module g};
    for i from 0 to n-1 do (
    	newhgrade := new MutableHashTable;
    	for k in keys hgrade do (
    	    jmin := 0; --if member(i,{2,3}) then jmin := 1 else jmin = 0;
	    for j from jmin to degmax_i do (
	    	temp := intersect (hgrade#k, ker (grd#i+j));
	    	if not zero temp then newhgrade#(k|{j}) = temp
    	    	);
	    );
    	hgrade = new HashTable from newhgrade
	);
    numvars := applyValues(hgrade, v -> numcols gens v);
    varl := transpose flatten apply(pairs hgrade,
	(k,v) -> apply(toList(1..(numcols gens v)), i -> {k,x_((toSequence (-k))|(1:i))})
	);
    R := kk[varl_1, Degrees => varl_0];
    varHT := applyPairs(hgrade,
	(k,v) -> (k,apply(toList(1..(numcols gens v)),i -> x_((toSequence (-k))|(1:i))))
	);
    sum(keys hgrade, k -> (gens hgrade#k)*(transpose matrix{toList varHT#k}))
    )





















(Lgen,L)=defectLieAlgebraDual(frmt,{b,c,d,e,f}); S = ring Lgen;
ggen = (Ltog frmt)*Lgen;
time F = topComplex(frmt,ggen);


grd = new MutableHashTable
for i from 1 to 7 do grd#i = (bracket g)*(g.cache#"alpha"_{i-1}**id_(module g));

-*
2 4 5 6 7
  3
  1
*-

rank ker (grd#3+3)

degmax = new MutableHashTable
for i from 1 to 6 do (
    j := 0;
    while not zero ker (grd#i+j) do j = j+1;
    degmax#i = j
    )


hgrade = new MutableHashTable
hgrade#{} = module g;
for i from 1 to 6 do (
    newhgrade := new MutableHashTable;
    for k in keys hgrade do (
    	if member(i,{2,3}) then jmin := 1 else jmin = 0;
	for j from jmin to degmax#i do (
	    temp := intersect (hgrade#k, ker (grd#i+j));
	    if not zero temp then newhgrade#(k|{j}) = temp
    	    );
	);
    hgrade = newhgrade
    )
keys hgrade


g = lieAlgebra("E",6)
x = symbol x
genericMultigrade(g,x)

genericMultigrade = method();
genericMultigrade (LieAlgebra,Thing) := Matrix => (g,x) -> (
    kk := ring module g;
    n := numcols g.cache#"e";
    grd := apply(n, i -> (bracket g)*(g.cache#"alpha"_{i}**id_(module g)));
    degmax := apply(n, i -> (
	    j := 0;
    	    while not zero ker (grd#i+j) do j = j+1;
    	    return j
	    )
	);
    hgrade := hashTable {{}=>module g};
    for i from 0 to n-1 do (
    	newhgrade := new MutableHashTable;
    	for k in keys hgrade do (
    	    jmin := 0; --if member(i,{2,3}) then jmin := 1 else jmin = 0;
	    for j from jmin to degmax_i do (
	    	temp := intersect (hgrade#k, ker (grd#i+j));
	    	if not zero temp then newhgrade#(k|{j}) = temp
    	    	);
	    );
    	hgrade = new HashTable from newhgrade
	);
    numvars := applyValues(hgrade, v -> numcols gens v);
    varl := transpose flatten apply(pairs hgrade,
	(k,v) -> apply(toList(1..(numcols gens v)), i -> {k,x_((toSequence (-k))|(1:i))})
	);
    R := kk[varl_1, Degrees => varl_0];
    varHT := applyPairs(hgrade,
	(k,v) -> (k,apply(toList(1..(numcols gens v)),i -> x_((toSequence (-k))|(1:i))))
	);
    return sum(keys hgrade, k -> (gens hgrade#k)*(transpose matrix{toList varHT#k}))
    )

keys hgrade
    
    bb := bracket g;
    gn := truncate(g,-1);
    projneg := sum(indices module gn, i -> gn_[i]*g^[i]);
    incneg := sum(indices module gn, i -> g_[i]*gn^[i]);
    h1 := hnew := gens trim h;
    n := 0; hn := {null};
    while not zero hnew do (
	hn = hn|{projneg*hnew}; n = n+1;
	hnew = gens trim image (bb*(hnew**h1))
	);
    biHT := hashTable apply(((indices module gn)**(toList(1..n))), L -> (
	    {L_0,-L_1} => gens trim intersect(image hn_(L_1),image gn_[L_0])
	    )
	);
    biHT = hashTable select(pairs biHT, (k,v)->not zero v);
    numvars := applyValues(biHT, v->rank v);
    x := symbol x;
    varl := transpose flatten (toList\apply(keys biHT, k -> (1..(numvars#k))/(i->{x_((toSequence k)|(1:i)),k})));
    R := kk[varl_0, Degrees => (varl_1)/(i->-i)];
    varHT := applyPairs(biHT, (k,v)->(k,(1..(rank v))/(i->x_((toSequence k)|(1:i)))));
    return sum(pairs varHT, (k,v) -> (
	    incneg*biHT#k*(transpose matrix{toList v})
	    )
	)
    );















(values hgrade)/rank



(grd#3)*(gens hgrade#{1,2})

intersect (hgrade#{1,2}, ker(grd#3+2))


i=7
wt = (bracket g)*(g.cache#"h"**g.cache#"e"_{i-1})//g.cache#"e"_{i-1}
(g.cache#"e"_{i-1}*wt == (bracket g)*(g.cache#"h"**g.cache#"e"_{i-1}))

(grd#3)*(gens hgrade#{1,2})

keys hgrade
(values hgrade)/rank

rank ker (grd#1+2)


j=0
while true do (
    temp = ker (grd#i+j);
    if not zero temp then hgrade#{j} = temp else break;
    j = j+1
    )

i=2



for j from 0 to 5 do << rank ker (grd#i+j) << endl
rank ker (grd#2+2)
rank ker (grd#1








Ltog frmt;

map(QQ^3,QQ^0,0)

fold({},(a,b)->a|b)

glLie QQ^0
slLie F3

frmt={1,4,10,7}
g = lieAlgebra formatLookup frmt; g'=truncate(g,0);
(Lgen,L)=defectLieAlgebraDual(frmt,{b,c,d,e,f}); S = ring Lgen;
ggen = (Ltog frmt)*Lgen;
time F = topComplex(frmt,ggen);
zero (F.dd_1*F.dd_2)
zero (F.dd_2*F.dd_3)


L0tog = method()
L0tog List := Matrix => frmt -> (
    kk := QQ; F3 := kk^(frmt_3); F1 := kk^(frmt_1);
    algname := formatLookup frmt; g := lieAlgebra algname; n := algname_1;
    --the two lists of remaining nodes depends on format
    if algname_0=="E" and frmt_3==2 then (
    	i := 3-1; L3 := {1}/(i->i-1); L1 := ((reverse toList(4..n))|{2})/(i->i-1)
	) else
    if algname_0=="E" then (
	i = 5-1; L3 = (toList(6..n))/(i->i-1); L1 = {1,3,4,2}/(i->i-1)
	) else
    if algname_0=="D" and frmt_3==1 then (
	i = n-1-1; L3 = {}; L1 = ({n}|(reverse toList(1..(n-2))))/(i->i-1)
	) else
    if algname_0=="D" then (
	i = n-3-1; L3 = (reverse toList(1..(n-4)))/(i->i-1); L1 = {n-1,n-2,n}/(i->i-1)
	);
    --slF3:
    slF3 := slLie(F3);
    incslF3 := extendMap(
	slF3.cache#"e"|slF3.cache#"f",slF3,
	g.cache#"e"_L3|g.cache#"f"_L3,g
	);
    --slF1:
    slF1 := slLie(F1);
    incslF1 := extendMap(
	slF1.cache#"e"|slF1.cache#"f",slF1,
	g.cache#"e"_L1|g.cache#"f"_L1,g
	);
    incC := g.cache#"alpha"_{i};
    L0 := directSum(sl(F3),sl(F1),kk^1);
    return map(module g, L0,incslF3*L0^[0]+incslF1*L0^[1]+incC*L0^[2])
    )









temp=id_(QQ^2)
temp_{}|temp_{}

g = lieAlgebra formatLookup frmt; g'=truncate(g,0);
(Lgen,L)=defectLieAlgebraDual(frmt,{b,c,d,e,f}); S = ring Lgen;
ggen = (Ltog frmt)*Lgen


--fixing the Dn reps
g = lieAlgebra("E",6)
V = extremalRep(g,2)
V' = repFromGradedAction(g,completeIrrepAction(g, actionHT V,module V),module V)

2 4 5 6
  3
  1



grd = new MutableHashTable
for i from 0 to 5 do grd#i = (bracket g)*(g.cache#"alpha"_{i}**id_(module g));

bb=(gens ker (grd#1+2))_{0}; --bottom part in F-grading

tt=(gens ker (grd#2-2)) --top part in L-grading

grd#5*tt
tt


for i from 0 to 5 do (
    temp:=((bracket g)*(g.cache#"alpha"**tt_{i}))//tt_{i};
    if tt_{i}*temp != ((bracket g)*(g.cache#"alpha"**tt_{i})) then error "eig failure";
    << i << " " << temp << endl
    )

((bracket g)*(g.cache#"alpha"**bb))//bb

zero checkRep(V',1,-1,4)



n = 4
g = lieAlgebra("D",n)
V = extremalRep(g,n-1)
kk=QQ;F=kk^n

e := new MutableHashTable; f := new MutableHashTable; h := new MutableHashTable;

CartanMatrix = fold(apply(n,i->((bracket g)*(g.cache#"h"**g.cache#"e"_{i}))//g.cache#"e"_{i}), (a,b)->a||b)

hwvec = invariants(g.cache#"e",V')    
((action V')*(g.cache#"h"**hwvec))//hwvec

test=(action V')*(g.cache#"alpha"_{6}**id_(module V'));

V = adjointRep g
((bracket g)*(g.cache#"alpha"**g_1_{0}))//g_1_{0}








frmt = {1,5,7,3}
topComplex(2,frmt);



g=lieAlgebra formatLookup frmt



g'=truncate(lieAlgebra formatLookup frmt,0)
(Lgen,L) = defectLieAlgebraDual(frmt,{b,c,d,e,f}); S = ring Lgen;
ggen = (Ltog frmt)*Lgen;
F = topComplex(frmt,ggen)

mapInfo F.dd_3

F.dd_1

g'^[0]*ggen

g = lieAlgebra formatLookup frmt
g.cache#"alpha"_{

F=topComplex(frmt,ggen)

