mapInfo = method()
mapInfo Matrix := Net => M -> (
    return (
	(net "degrees: "|netList apply((entries M),rrow->rrow/(entry->if not zero entry then return degree entry else return null)))||
	(net "# terms: "|netList apply((entries M),rrow->rrow/(entry->#terms entry)))
	)
    )


---------------------------------
-- Basic operations on modules --
---------------------------------

gl = method()
gl Module := Module => M -> (
    return (M**(dual M))
    )
--M ** M* -> R eval/trace
tr = method()
tr Module := Matrix => M -> (
    return adjoint'(id_M, dual M, (ring M)^1)
    )
--wedge coproduct/diagonal
wedgeDiag = method()
wedgeDiag (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    return dual wedgeProduct(a,b, dual M)
    )
--inclusion sl -> gl
isl = method()
isl Module := Matrix => M -> (
    return gens ker tr(M)
    )
sl = method()
sl Module := Module => M -> (
    return source isl(M)
    )
--projection gl -> sl
psl = method()
psl Module := Matrix => M -> (
    return (id_(gl(M))-1/(rank M)*(dual tr(dual M))*tr(M)) // isl(M)
    )
--identification gl -> sl+C
igl = method()
igl Module := Matrix => M -> (
    targ := directSum(0=>sl(M),1=>(ring M)^1);
    return (1/(rank M))*(targ)_[1]*tr(M) + (targ)_[0]*psl(M)
    )

--exponentiating nilpotent matrix
exp Matrix := Matrix => M -> (
    curPow := M^0;
    val := curPow; i := 1;
    while true do (
	curPow = (1/i)*M*curPow;
	if curPow == 0 then break else val = val + curPow;
	i = i+1
	);
    return val
    )

--override default behavior of inclusion and projection
--to allow for cases when components are zero / not specified
safeProj = method()
safeProj (Module,Array) := Matrix => (M,a) -> (
    if #a==0 then return map((ring M)^0,M,0);
    inds := toList a;
    compHT := hashTable apply(transpose{indices M, components M},i->i_0=>i_1);
    mats := apply(inds, i -> (
	    if member(i,indices M) then return map(compHT#i,M,M^[i]) else
	    return map((ring M)^0,M,0)
	    ));
    return map(directSum(apply(transpose({inds,mats/target}),i->i_0=>i_1)),M,fold(mats,(i,j)->i||j))
    )
safeInc = method()
safeInc (Module,Array) := Matrix => (M,a) -> (
    if #a==0 then return map(M,(ring M)^0,0);
    inds := toList a;
    compHT := hashTable apply(transpose{indices M, components M},i->i_0=>i_1);
    mats := apply(inds, i -> (
	    if member(i,indices M) then return map(M,compHT#i,M_[i]) else
	    return map(M,(ring M)^0,0)
	    ));
    return map(M,directSum(apply(transpose({inds,mats/source}),i->i_0=>i_1)),fold(mats,(i,j)->i|j))
    )

------------------
-- Lie algebras --
------------------

LieAlgebra = new Type of HashTable;
module LieAlgebra := Module => g -> g#"module";
bracket = method();
bracket LieAlgebra := Matrix => g -> g#"bracket";
name = method();
name LieAlgebra := Thing => g -> g#"name";
net LieAlgebra := Net => g -> net module g;
--some shorthand
LieAlgebra^Array := Matrix => (g,v) -> safeProj(module g,v);
LieAlgebra_Array := Matrix => (g,v) -> safeInc(module g,v);
LieAlgebra_ZZ := (g,i) -> (components source safeInc(module g,[i]))_0;
--can I make LieAlgebra_(ZZ,ZZ) work?
LieAlgebra_Sequence := Matrix => (g,pair) -> (
    return (g^[pair_0+pair_1]*(bracket g)*(g_[pair_0]**g_[pair_1]))
    );

fillBracket = method()
fillBracket (Module,HashTable) := HashTable => (g,partialbracket) -> (
    ht := hashTable apply(
	select(
	    apply(keys partialbracket, (i,j)->(j,i)),
	    k -> not member(k,keys partialbracket)
	    ),
	(j,i) -> (j,i)=>(-1)*(partialbracket#(i,j))*flip(
	    first components source g_[j],first components source g_[i]
	    )
	);
    return merge(partialbracket,ht,(i,j) -> error "conflicting keys")
    )


--creation from graded module and bracket hash table
newLieAlgebra = method(Options => {Name=>null});
newLieAlgebra (Module,HashTable) := LieAlgebra => o -> (g,bracket) -> (
    MIN := min(indices g); 
    MAX := max(indices g);
    brk := sum(toList select((MIN,MIN)..(MAX,MAX),(i,j)->i+j>=MIN and i+j<=MAX),
	(i,j) -> (
	    if bracket#?(i,j) then return g_[i+j]*(bracket#(i,j))*(g^[i]**g^[j]) else
	    if bracket#?(j,i) then return (-1)*g_[i+j]*(bracket#(j,i))*flip(target g^[i],target g^[j])*(g^[i]**g^[j]) else
	    return map(g,g**g,0)
	    )
	);
    L := {"module"=>g,"bracket"=>map(g,g**g,brk),cache=>new CacheTable};
    if (not o.Name === null) then L = L|{"name"=>o.Name};
    return new LieAlgebra from hashTable L
    );
newLieAlgebra (Module,Matrix) := LieAlgebra => o -> (g,bracket) -> (
    L := {"module"=>g,"bracket"=>map(g,g**g,bracket),cache=>new CacheTable};
    if (not o.Name === null) then L = L|{"name"=>o.Name};
    return new LieAlgebra from hashTable L
    );

Jacobi = method()
Jacobi (LieAlgebra,ZZ,ZZ,ZZ) := Matrix => (g,i,j,k) -> (
    return (
	g_(i,j+k)*(id_(g_i)**g_(j,k))
	+g_(j,k+i)*(id_(g_j)**g_(k,i))*flip(g_i,g_j**g_k)
	+g_(k,i+j)*(id_(g_k)**g_(i,j))*flip(g_i**g_j,g_k)
	)
    )

--use a map h -> g to pull back Lie alg structure
--this is intended for inclusions (i.e. subalgebras)
subAlgebra = method()
subAlgebra (Matrix,LieAlgebra) := LieAlgebra => (f,g) -> (
    h := source f;
    hbrak := map(target f,,((bracket g)*(f**f)))//f;
    if debugLevel > 0 and not zero(f*hbrak - (bracket g)*(f**f)) then << "warning: Lie algebra may not be well-defined" << endl;
    return newLieAlgebra(h,map(h,h**h,hbrak))
    )

--truncation
--the part >= m
--generally only makes sense if m>=0
truncate(ZZ,LieAlgebra) := LieAlgebra => (m,g) -> (
    MAX := max indices module g;
    return subAlgebra(g_(new Array from m..MAX),g)
    );
--the part <= m
--generally only makes sense if m<=0
truncate(LieAlgebra,ZZ) := LieAlgebra => (g,m) -> (
    MIN := min indices module g;
    return subAlgebra(g_(new Array from MIN..m),g)
    );

---------------------
-- Representations --
---------------------

LieAlgebraRep = new Type of HashTable;
action = method(); algebra = method();
action LieAlgebraRep := Matrix => V -> V#"action";
module LieAlgebraRep := Module => V -> V#"module";
algebra LieAlgebraRep := LieAlgebra => V -> V#"LieAlg";
net LieAlgebraRep := Net => V -> net V#"module";
--the rep doesn't have to be graded, but in case it is:
LieAlgebraRep^Array := Matrix => (V,a) -> safeProj(module V,a);
LieAlgebraRep_Array := Matrix => (V,a) -> safeInc(module V,a);
LieAlgebraRep_ZZ := Module => (V,i) -> (components source safeInc(module V,[i]))_0;

conjugate List := List => p -> return toList conjugate new Partition from p;

--takes (V,param) and outputs V -(param)-> g ** V -(action)-> V
parametricAction = method();
parametricAction (LieAlgebraRep,Matrix) := Matrix => (V,param) -> (
    R := ring param;
    return sub(action V,R)*(param**sub(id_(module V),R))
    );

newRep = method()
newRep (LieAlgebra,Matrix,Module) := LieAlgebraRep => (g,act,V) -> (
    return new LieAlgebraRep from hashTable{
	"action" => act,
	"LieAlg" => g,
	"module" => V
	}
    )

adjointRep = method()
adjointRep LieAlgebra := LieAlgebraRep => g -> (
    return newRep(g,bracket g,module g)
    )


--restriction and subreps
generate = method()
generate (Matrix,Matrix,LieAlgebraRep) := Matrix => (ggens,Vgens,V) -> (
    g := algebra V;
    newDomain := totalDomain := gens trim image Vgens;
    while true do (
    	newDomain = gens trim image (((action V)*(ggens**newDomain))%totalDomain);
	if zero newDomain then return totalDomain;
	totalDomain = gens trim image (totalDomain|newDomain)
    	)
    )
generate (Matrix,LieAlgebraRep) := Matrix => (gen,V) -> (
    return generate(id_(module algebra V),gen,V)
    )
generate (Matrix,LieAlgebra) := Matrix => (gen,g) -> (
    return generate(gen,gen,adjointRep g)
    )
--f:h->g, w:W->V, tries to make W as h-rep from V as g-rep
subRep = method()
subRep (LieAlgebra,Matrix,Matrix,LieAlgebraRep) := LieAlgebraRep => (h,f,w,V) -> (
    g := algebra V;
    newact := ((action V)*(f**w))//w;
    if debugLevel > 0 and not zero(w*newact - (action V)*(f**w)) then << "warning: action may not be well-defined" << endl;
    return newRep(h,newact,source w)
    )
--f:g->h, w:V->W, tries to make W as h-rep from V as g-rep
quotientRep = method()
quotientRep (Matrix,LieAlgebra,LieAlgebraRep,Matrix) := LieAlgebraRep => (f,h,V,w) -> (
    g := algebra V;
    newact := dual ((dual (w*(action V)))//(dual (f**w)));
    if debugLevel > 0 and not zero(newact*(f**w) - w*(action V)) then << "warning: action may not be well-defined" << endl;
    return newRep(h,newact,target w)
    )


trivialRep = method()
trivialRep LieAlgebra := LieAlgebraRep => g -> (
    return newRep(g,map((ring module g)^1,module g,0),(ring module g)^1)
    )

--gl(F) as Lie algebra
glLie = method()
glLie Module := LieAlgebra => F -> (
    return newLieAlgebra(
	directSum(0=>F**(dual F)),
	id_F**(tr(F)*flip(dual F,F))**id_(dual F) - (flip(dual F,F)**tr(F))*(flip(F,(dual F)**F)**id_(dual F))
	)
    )
--sl(F) as Lie algebra, with generator data
slLie = method()
slLie Module := LieAlgebra => F -> (
    g := subAlgebra(isl(F),glLie(F)); n := rank F; kk := ring F;
    if n<=1 then (
	g.cache#"e" = g.cache#"f" = g.cache#"h" = g.cache#"alpha" = map(module g,kk^0,0)
	) else (
    	g.cache#"e" = fold(
	    apply(n-1,
    	    	i -> psl(F)*flip(dual F,F)*adjoint(map(F,F,{(i,i+1)=>1}),kk^1,F)
    	    	), (a,b)->a|b
	    );
    	g.cache#"f" = fold(
	    apply(n-1,
    	    	i -> psl(F)*flip(dual F,F)*adjoint(map(F,F,{(i+1,i)=>1}),kk^1,F)
    	    	), (a,b)->a|b
	    );
	g.cache#"h" = fold(
	    apply(n-1,
		i -> (bracket g)*(g.cache#"e"_{i}**g.cache#"f"_{i})
		), (a,b)->a|b
	    );
	CartanMatrix := fold(apply(n-1,i->((bracket g)*(g.cache#"h"**g.cache#"e"_{i}))//g.cache#"e"_{i}), (a,b)->a||b);
    	--"coroots"
    	g.cache#"alpha" = (g.cache#"h"*(inverse CartanMatrix));
        );
    return g
    )
--so(F + F') as Lie algebra, with generator data
soLie = method()
soLie Module := LieAlgebra => M -> (
    n := rank M; kk := ring M;
    MM := directSum("M"=>M, "M*" => dual M);
    --qform = MM_["M*"]*MM^["M"] + MM_["M"]*MM^["M*"]
    e := apply(
    	apply(toList(1..(n-1)),i -> (i-1,i)), (i,j) -> 
    	MM_["M"]*map(M,M,{(i,j)=>1})*MM^["M"] - MM_["M*"]*map(dual M, dual M,{(j,i)=>1})*MM^["M*"]
    	);
    e = e|{MM_["M"]*map(M,dual M,{(n-2,n-1)=>1})*MM^["M*"] - MM_["M"]*map(M,dual M,{(n-1,n-2)=>1})*MM^["M*"]};
    f := e/transpose;
    ee := fold(apply(e,x -> flip(dual MM, MM)*adjoint(x,kk^1,MM)), (a,b)->a|b);
    ff := fold(apply(f,x -> flip(dual MM, MM)*adjoint(x,kk^1,MM)), (a,b)->a|b);
    gl := glLie(MM);
    h := fold(apply(n, i -> (bracket gl)*(ee_{i}**ff_{i})), (a,b)->a|b);
    soinc := generate(ee|ff,gl);
    so := subAlgebra(soinc,gl);
    so.cache#"e" = ee//soinc; so.cache#"f" = ff//soinc; so.cache#"h" = h//soinc;
    CartanMatrix := fold(apply(n,i->((bracket so)*(so.cache#"h"**so.cache#"e"_{i}))//so.cache#"e"_{i}), (a,b)->a||b);
    --"coroots"
    so.cache#"alpha" = (so.cache#"h"*(inverse CartanMatrix));
    so.cache#"gl" = soinc;
    return so
    )

--standard rep F ** F* ** F -> F
glStandard = method()
glStandard Module := LieAlgebraRep => F -> (
    return newRep(glLie(F),id_F**tr(dual F),F)
    )

schurRep = method()
--should combine this and prev at some point
--actually should just write tensorRep and 
schurRep (List,Module) := LieAlgebraRep => (p,V) -> (
    return schurRep(p,glStandard V)
    )
schurRep (List,LieAlgebraRep) := LieAlgebraRep => (p,V) -> (
    if #p==0 then return trivialRep(algebra V);
    return schurRep(p,V,(schurModule(p,module V)).cache#"Schur"#0)
    )
schurRep (List,LieAlgebraRep,Matrix) := LieAlgebraRep => (p,V,fwedge) -> (
    F := module V;
    M := target fwedge;
    R := ring F; g := algebra V;
    if #p==0 then return trivialRep(g);
    --list of exterior powers in source of fwedge
    p' := conjugate p;
    exrep := tensorRep toSequence apply(#p',
    	i -> exteriorPowerRep(p'_i,V)
	);
    return quotientRep(id_(module g),g,exrep,fwedge)
    )

exteriorPowerRep = method()
exteriorPowerRep (ZZ,LieAlgebraRep) := LieAlgebraRep => (m,V) -> (
    g := algebra V;
    act := (
	wedgeProduct(1,m-1,module V)*((action V)**id_(exteriorPower(m-1,module V)))
	*(id_(module g)**wedgeDiag(1,m-1,module V))
	);
    return newRep(g,act,exteriorPower(m,module V))
    )

tensorRep = method(Dispatch => Thing)
tensorRep Sequence := LieAlgebraRep => VSeq -> (
    if #VSeq == 0 then error "tensorRep must take at least one input";
    if #VSeq == 1 then return VSeq_0;
    MSeq := VSeq/module;
    g := algebra VSeq_0; R := ring module g;
    act := sum(#VSeq, i -> (
	    (
		(id_(tensor((2:R^1)|take(MSeq,i)))**(action VSeq_i))
	    	*(flip(module g,tensor((2:R^1)|take(MSeq,i)))**id_(MSeq_i))
		)**id_(tensor((2:R^1)|take(MSeq,i-#VSeq+1)))
	    )
	);
    return newRep(g,act,tensor MSeq)
    )
LieAlgebraRep**LieAlgebraRep := LieAlgebraRep => (V1,V2) -> (
    return tensorRep(V1,V2)
    )
-*
LieAlgebraRep**LieAlgebraRep := LieAlgebraRep => (V1,V2) -> (
    if not (module algebra V1 == module algebra V2) then (
	error "inputs not representations of same Lie algebra!"
	) else g := algebra V1;
    return newRep(
	g,
	((action V1)**id_(module V2))
	+
	(id_(module V1)**(action V2))*(flip(module g,module V1)**id_(module V2)),
	(module V1)**(module V2)
	)
    );
*-

dualRep = method();
dualRep LieAlgebraRep := LieAlgebraRep => V -> (
    act := action V; M := module V; g := algebra V;
    return newRep(
        g,
	(-1)*adjoint'(dual act,module g,dual M)*flip(module g,dual M),
	dual M
	)
    )
    
actionHT = method()
actionHT LieAlgebraRep := HashTable => V -> (
    g := algebra V;
    gMIN := min indices module g; gMAX := max indices module g;
    VMIN := min indices module V; VMAX := max indices module V;
    ij := select(toList((gMIN,VMIN)..(gMAX,VMAX)), (i,j) -> i+j >= VMIN and i+j <= VMAX);
    return hashTable apply(ij, (i,j) -> (i,j) => V^[i+j]*(action V)*(g_[i]**V_[j]))
    )

--returns list of (basis of) equivariant maps between two gl(F)-reps.
--This is done by finding the invariants (trivial reps) in Hom.
--This assumes g = F ** F* where F is a free module of rank n.

--this was too slow to be useful

invariants = method();
invariants (Matrix,LieAlgebraRep) := Matrix => (ggens, V) -> (
    g := algebra V;
    W := id_(module V);
    for i from 0 to (numcols ggens)-1 do (
	Wnext := gens ker ((action V)*(ggens_{i}**W));
	W = W*Wnext
	);
    return W
    )

--find invariants of V1* ** V2
equivariantMaps = method();
equivariantMaps (Matrix,LieAlgebraRep,LieAlgebraRep) := List => (ggens,V1,V2) -> (
    g := algebra V1;
    --find highest weights if possible
    if g.cache#?"e" and g.cache#?"h" then (
	HWV1 := invariants(g.cache#"e",V1); HWV2 := invariants(g.cache#"e",V2);
	cartan := subAlgebra(g.cache#"h",g);
	HWV1rep := subRep(cartan,g.cache#"h",HWV1,V1);
	HWV2rep := subRep(cartan,g.cache#"h",HWV2,V2);
	Ltop := equivariantMaps(id_(module cartan),HWV1rep,HWV2rep);
	return apply(Ltop, i->extendMap(HWV1,V1,HWV2*i,V2))
	);
    V := (dualRep V1)**V2;
--    e := apply((n-1), i-> adjoint(dual map(F,F,{(i,i+1)=>1}),kk^1,dual F));
--    h := apply(n, i-> adjoint(dual map(F,F,{(i,i)=>1}),kk^1,dual F));
    W := invariants(ggens,V);
    -*
    for i from 0 to (n-2) do (
	--<< i << endl;
    	Wnext := gens ker ((action V)*((e_i)**W));
    	W = W*Wnext
    	);
    for i from 0 to (n-1) do (
	--<< i << endl;
    	Wnext := gens ker ((action V)*((h_i)**W));
    	W = W*Wnext
    	);
    *-
    return apply(numcols W, i -> adjoint'(W_{i},module V1, module V2))
    );

checkRep = method()
checkRep (LieAlgebraRep,ZZ,ZZ,ZZ) := Matrix => (V,i,j,k) -> (
    g := algebra V;
    return V^[i+j+k]*(
	(action V)*(g_[i]**((action V)*(g_[j]**V_[k]))) --XYv
	-(action V)*((g_[i+j]*g_(i,j))**(V_[k])) --[X,Y]v
	-(action V)*(g_[j]**((action V)*(g_[i]**V_[k])))*(flip(g_i,g_j)**id_(V_k)) --YXv
	)
    )

--------------------------------------------------
-- Completing partially-defined representations --
--------------------------------------------------
--uses the action of g_-1 and/or g_1 to deduce the action of g_i, |i|>1
completeGradedAction = method(Options => {Sign => 0});
completeGradedAction (LieAlgebra,HashTable,Module) := HashTable => o -> (g,partialHT,V) -> (
    MINg := min(indices module g); MINV := min indices V;
    MAXg := max(indices module g); MAXV := max indices V;
    HT := new MutableHashTable from partialHT;
    if o.Sign <= 0 then (
	for i from 2 to (-MINg) do (
	    for j from MINV+i to MAXV do (
	    	if not HT#?(-i,j) then (
	    	    f := (
	    	    	HT#(-i+1,j-1)*(id_(g_(-i+1))**HT#(-1,j))
	    	    	-
	    	    	HT#(-1,j-i+1)*(id_(g_(-1))**HT#(-i+1,j))
	    	    	*(flip(g_(-i+1),g_(-1))**id_(target V^[j]))
	    	    	);
	    	    f' := g_(-i+1,-1)**id_(target V^[j]);
	    	    HT#(-i,j) = (
	    	    	dual ((dual f)//(dual f'))
	    	    	)
		    )
	    	)
	    )
	);
    if o.Sign >= 0 then (
	for i from 2 to MAXg do (
	    for j from MINV to MAXV-i do (
	    	if not HT#?(i,j) then (
	    	    f := (
	    	    	HT#(i-1,j+1)*(id_(g_(i-1))**HT#(1,j))
	    	    	-
	    	    	HT#(1,j+i-1)*(id_(g_1)**HT#(i-1,j))
	    	    	*(flip(g_(i-1),g_1)**id_(target V^[j]))
	    	    	);
	    	    f' := g_(i-1,1)**id_(target V^[j]);
	    	    HT#(i,j) = (
	    	    	dual ((dual f)//(dual f'))
	    	    	)
		    ) 
	    	)
	    )
	);
    return new HashTable from HT
    );

--for irreps only!!
--uses action of g_(-1) on all parts and action of g_0 on top part to deduce action of
--g_0 and g_1 on all parts.
completeIrrepAction = method()
completeIrrepAction (LieAlgebra,HashTable,Module) := HashTable => (g,partialHT,VM) -> (
    kk := ring VM;
    MINV := min indices VM;
    MAXV := max indices VM;
    V := newRep(g,map(VM,(module g)**VM,0),VM);
    HT := new MutableHashTable from partialHT;
    HT#(1,MAXV) = map(kk^0,g_1**V_MAXV,0); HT#(-1,MAXV+1) = map(V_MAXV,kk^0,0);
    for i from 0 to 1 do (
    	for j in reverse(MINV..(MAXV-1)) do (
	    if not HT#?(i,j) then (
    	    	f := (
	    	    HT#(i-1,j+1)
	    	    *(g_(i,-1)**id_(V_(j+1)))
	    	    +
	    	    HT#(-1,i+j+1)
	    	    *(id_(g_(-1))**HT#(i,j+1))
	    	    *(flip(g_i,g_(-1))**id_(V_(j+1)))
	    	    );
    	    	f' := id_(g_i)**HT#(-1,j+1);
    	    	HT#(i,j) = dual((dual f)//(dual f'));
    	    	)
	    )
	);
    remove(HT,(1,MAXV)); remove(HT,(-1,MAXV+1));
    return HT
    )

--converts graded action into a rep
repFromGradedAction = method();
repFromGradedAction (LieAlgebra,HashTable,Module) := LieAlgebraRep => (g,act,V) -> (
    a := set (keys act);
    a' := set (toSequence\((indices module g)**(indices V)));
    actmatrix := sum(toList (a*a'), (i,j) -> (
	    V_[i+j]*(act#(i,j))*(g^[i]**V^[j])
	    ));
    return newRep(g,actmatrix,V)
    ) 

---------------------------------------
-- Completing partially-defined maps --
---------------------------------------
--starting from g1 <-i1- gens -i2-> g2
extendMap = method()
extendMap (Matrix,LieAlgebra,Matrix,LieAlgebra) := Matrix => (i1,g1,i2,g2) -> (
    totalDomain := startDomain := curDomain := gens trim image i1;
    togens := curDomain // i1;
    totalMap := startMap := curMap := i2*togens;
    while true do (
	f := (bracket g1)*(startDomain**curDomain);
	f' := (bracket g2)*(startMap**curMap);
	curDomain = gens trim image (f%totalDomain);
	if zero (curDomain) then (
	    if zero coker totalDomain then return dual((dual totalMap)//(dual totalDomain)) else
	    error "does not generate source Lie algebra"
	    );
	curMap = (dual ((dual f')//(dual f)));
	if debugLevel > 0 and not zero (curMap*f - f') then error "Lie algebra homomorphism extension failed";
	curMap = curMap*curDomain;
	newDomain := gens trim image (totalDomain|curDomain);
        totalMap = dual ((dual (totalMap|curMap))//(dual ((totalDomain|curDomain)//newDomain)));
	totalDomain = newDomain
	)
    )
extendMap (Matrix,LieAlgebraRep,Matrix,LieAlgebraRep) := Matrix => (i1,V1,i2,V2) -> (
    g := algebra V1;
    totalDomain := startDomain := curDomain := gens trim image i1;
    togens := curDomain // i1;
    totalMap := startMap := curMap := i2*togens;
    while true do (
	f := (action V1)*(id_(module g)**curDomain);
	f' := (action V2)*(id_(module g)**curMap);
	curDomain = gens trim image (f%totalDomain);
	if zero (curDomain) then (
	    if zero coker totalDomain then return dual((dual totalMap)//(dual totalDomain)) else
	    error "does not generate source representation"
	    );
	curMap = (dual ((dual f')//(dual f)));
	if debugLevel > 0 and not zero (curMap*f - f') then error "Lie algebra homomorphism extension failed";
	curMap = curMap*curDomain;
	newDomain := gens trim image (totalDomain|curDomain);
        totalMap = dual ((dual (totalMap|curMap))//(dual ((totalDomain|curDomain)//newDomain)));
	totalDomain = newDomain
	)
    )
