--format => Lie algebra name
--decides which Lie algebra implementation to use for given format
formatLookup = method()
formatLookup List := Sequence => frmt -> (
    if not frmt_0==1 then error "only implemented for cyclic module formats";
    --check alternating sum zero
    if not sum(#frmt, i -> (-1)^i*frmt_i)==0 then error "invalid format";
    if #frmt==4 then (
	if frmt_1==frmt_2 or frmt_1==4 then return ("D",frmt_2)
	);
    ELookup := hashTable{
    	{1,8,14,8,1} => ("E",8),
    	{1,5,8,4} => ("E",8),
    	{1,7,8,2} => ("E",8),
    	{1,7,12,7,1} => ("E",7),
    	{1,6,7,2} => ("E",7),
    	{1,5,7,3} => ("E",7),
    	{1,6,10,6,1} => ("E",6),
    	{1,5,6,2} => ("E",6),
    	{1,5,8,5,1} => ("E",5)
    	};
    if ELookup#?frmt then return ELookup#frmt;
    error "not implemented for this resolution format"
    )

---------------------------
-- defect variable setup --
---------------------------
--follow methods are for specifying the generic element of g_neg in the non-F grading
--in a way that matches existing notation conventions as much as possible.

--set up (dual of) defect Lie alg for length 3 in familiar convention
--so degree -1 piece is F3 ** wedge^2(dual F1) etc
--also returns a generic element with familiar defect variable notation
defectLieAlgebraDual = method();
defectLieAlgebraDual (List,List) := (Matrix,LieAlgebra) => (frmt,dvletters) -> (
    if not #frmt==4 then error "defectLieAlgebraDual only implemented for length 3 resolutions of cyclic modules";
    kk := QQ; (b1,b3) := (frmt_1,frmt_3);
    M := kk^(frmt_1-1); F3 := kk^(frmt_3);
    F1 := directSum("M"=>M,"kk"=>kk^1);
    F := directSum("M"=>M,"F3"=>F3);
    name := formatLookup frmt; n := name_1;--n is rank of F (i.e. F2)
    defvarletters := {null}|dvletters; if #dvletters==0 then (
	b := symbol b; c := symbol c; d := symbol d; e := symbol e; f := symbol f;
	defvarletters = {null}|{b,c,d,e,f}
	);
    LSchurHT := new MutableHashTable;
    LSchurHT#1 = {{1},{1,1}}; --degree -1 piece is always F3 ** wedge^2(dual F1)
    defvars := {};
    newvars := apply(toSequence\flatten\ (subsets(reverse(-b3..-1),1)**subsets(1..b1,2)),i -> defvarletters_1_i);
    defvars = defvars|newvars;
    degreeseq := #newvars:1;
    if frmt_3 > 1 then (
	LSchurHT#2 = {{1,1},{1,1,1,1}};
	newvars = apply(toSequence\flatten\ (subsets(reverse(-b3..-1),2)**subsets(1..b1,4)),i -> defvarletters_2_i);
        defvars = defvars|newvars;
    	degreeseq = degreeseq|(#newvars:2);
	);
    if name_0=="E" then (
	if frmt_3==2 then (
	    if n>=7 then (
		LSchurHT#3={{2,1},{1,1,1,1,1,1}}; --(1,6,7,2) and (1,7,8,2)
		newvars = apply(toSequence\flatten\ (subsets(reverse(-b3..-1),1)**subsets(1..b1,6)),i -> defvarletters_3_i);
                defvars = defvars|newvars;
    	        degreeseq = degreeseq|(#newvars:3);
		);
    	    if n==8 then (
		LSchurHT#4={{2,2},{2,1,1,1,1,1,1}}; --(1,7,8,2)
	    	newvars = apply(toSequence\flatten\ (subsets(reverse(-b3..-1),2)**subsets(1..b1,1)),i -> defvarletters_4_i);
                defvars = defvars|newvars;
    	        degreeseq = degreeseq|(#newvars:4);
		);
	    ) else (
	    if n>=7 then (
		LSchurHT#3={{1,1,1},{2,1,1,1,1}}; --(1,5,7,3) and (1,5,8,4)
		newvars = apply(toSequence\flatten\ (subsets(reverse(-b3..-1),3)**subsets(1..b1,1)),i -> defvarletters_3_i);
                defvars = defvars|newvars;
    	        degreeseq = degreeseq|(#newvars:3);
	    	if n==8 then ( --(1,5,8,4)
		    LSchurHT#4={{1,1,1,1},{2,2,2,1,1}};
		    newvars = apply(toSequence\flatten\ (subsets(reverse(-b3..-1),4)**subsets(1..b1,3)),i -> defvarletters_4_i);
                    defvars = defvars|newvars;
    	            degreeseq = degreeseq|(#newvars:4);
		    LSchurHT#5={{2,1,1,1},{2,2,2,2,2}};
		    newvars = apply(toSequence\flatten\ (subsets(reverse(-b3..-1),1)**subsets(1..b1,5)),i -> defvarletters_5_i);
                    defvars = defvars|newvars;
    	            degreeseq = degreeseq|(#newvars:5);
		    )
	    	)
	    )
	);
    NN := max keys LSchurHT;
    LT := hashTable (
	apply(toList(1..NN), i -> -i => schurModule(LSchurHT#i#0, F3)**schurModule(LSchurHT#i#1, dual F1))
	);
    L := directSum((pairs LT)/((k,v)->(k=>v)));
    Rg := QQ[defvars, Degrees => toList degreeseq];
    --the components of L are organized from -NN to -1, so:
    Lgen := L_(new Array from reverse (-NN..-1))*(dual vars Rg);
    if LieAlgebraCache#?frmt then return (Lgen,LieAlgebraCache#frmt);
    BT := new MutableHashTable;
    for j from 1 to (NN-1) do (
	p:=LSchurHT#j; w3 := position(p_0, i->i==p_0_0, Reverse=>true)+1; w1 := position(p_1, i->i==p_1_0, Reverse=>true)+1;
	a3 := min(frmt_3-w3,1);
	a1 := min(frmt_1-w1,2);
	BT#(-1,-j) = (
	    (id_(exteriorPower(1-a3,F3))**wedgeProduct(a3,w3,F3)**
		(
		    (wedgeProduct(w1,a1,dual F1)**id_(exteriorPower(2-a1,dual F1)))
		    *(id_(schurModule(p_1,dual F1))**wedgeDiag(a1,2-a1,dual F1))
		    )
		)
	    *(id_(F3)**flip(exteriorPower(2,dual F1),LT#(-j)))
	    )
	);
    --get [-2,*] for the two E8 formats
    if NN >= 4 then (
	BT = fillBracket(L,BT);
	g' := newLieAlgebra(L,BT); --"fake" lie algebra with just adj action of -1
	BT = completeGradedAction(g',BT,L,Sign=>-1); --deduce adj action of lower pieces
	);
    LieAlgebraCache#frmt = newLieAlgebra(L,BT);
    return (Lgen,LieAlgebraCache#frmt)
    )

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
	i = n-1-1; L3 = {}; L1 = (toList(1..(n-2))|{n})/(i->i-1)
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
--map LL* to g_(<=0) for length three formats
Ltog = method()
Ltog List := Matrix => frmt -> (
    kk := QQ; F3 := kk^(frmt_3); F1 := kk^(frmt_1);
    algname := formatLookup frmt; g := lieAlgebra algname; n := algname_1;
    --the deleted node depends on format
    if algname_0=="E" and frmt_3==2 then (
    	i := 3-1
	) else
    if algname_0=="E" then (
	i = 5-1
	) else 
    if algname_0=="D" and frmt_3==1 then (
	i = n-1-1
	) else
    if algname_0=="D" then (
	i = n-3-1
	);
    --eigenspaces of grd give L-grading on g
    --grd := action subRep(subAlgebra(g.cache#"alpha"_{i},g),g.cache#"alpha"_{i},id_(module g),adjointRep g);
    grd := (bracket g)*(g.cache#"alpha"_{i}**id_(module g));
    incL0 := L0tog frmt;
    L0 := subAlgebra(incL0,g);
    --map L0 to glF3,F1
    tglF3 := isl(F3)*L0^[0] - (dual tr(dual F3))*L0^[2];
    tglF1 := isl(F1)*L0^[1]; --+ (1/2)*(dual tr(dual F1))*L0^[2]
    L1raw := (
    	subRep(L0,tglF3,id_(dual F3),schurRep({1},F3))
    	**subRep(L0,tglF1,id_(exteriorPower(2,F1)),dualRep schurRep({1,1},F1))
    	);
    incpart := gens ker (grd+1);
    incL1 := incpart*(first equivariantMaps(id_(module L0),L1raw,subRep(L0,incL0,incpart,adjointRep g)));
    --make it map to g_(<= 0) instead of g
    g' := truncate(g,0); gMIN := min indices module g';
    incg' := g_(new Array from toList(gMIN..0))*g'^(new Array from toList(gMIN..0));
    incL1 = incL1//incg';
    L := (defectLieAlgebraDual(frmt,{}))_1;
    return extendMap(L_[-1],L,incL1,g');
    )

--match Jerzy's defect var notation for (1,n,2n-2,n,1)
genericGorIndexing = method();
genericGorIndexing (ZZ,List) := Matrix => (n,dvletters) -> (
    kk:=QQ;
    M := kk^(n-1); F := directSum(M=>M,kk=>kk^1);
    g := lieAlgebra("E",n);
    defvarletters := {null}|dvletters;
    defvars := (
    	apply(toList(1..(n-1)),i -> defvarletters_1_i)|
    	apply(toSequence\subsets(1..(n-1),3),i -> defvarletters_1_i)|
    	apply(toSequence\subsets(1..(n-1),5),i -> defvarletters_1_i)|
    	apply(toSequence\subsets(1..(n-1),7),i -> defvarletters_1_i)|
    	apply(toSequence\subsets(1..(n-1),6),i -> defvarletters_2_i)
	);
    if n==8 then defvars = (defvars|
    	apply(toList(1..(n-1)), i -> defvarletters_2_i)
    	);
    Rg := QQ[
    	defvars,
    	Degrees => {
	    (binomial(n-1,1):{0,1}),
	    (binomial(n-1,3):{1,1}),
	    (binomial(n-1,5):{2,1}),
	    (binomial(n-1,7):{3,1}),
	    (binomial(n-1,6):{2,2}),
	    (binomial(n-1,7)*(n-1):{3,2})}
    	];
    --inclusion into g
    --bigraded pieces, manually specified
    gNeg := directSum(
    	(0,-1)=>dual M,
    	(-1,-1)=>exteriorPower(3,dual M),
    	(-2,-1)=>exteriorPower(5, dual M),
    	(-3,-1)=>exteriorPower(7, dual M),
    	(-2,-2)=>exteriorPower(6, dual M),
    	(-3,-2)=>exteriorPower(7, dual M)**(dual M)
    	);
    gneg := truncate(g,0); --0 or -1
    gNeginc := (
	gneg_[0]*gneg_0_[0]*psl(F)*(F_[kk]**(dual F^[M]))*gNeg^[(0,-1)]
	+
    	gneg_[-1]*(dual exteriorPower(3,F^[M]))*gNeg^[(-1,-1)]
    	);
    if n>=6 then gNeginc = (gNeginc +
    	gneg_[-2]*(dual ((exteriorPower(5,F^[M])**(F^[kk]))*wedgeDiag(5,1,F)))*gNeg^[(-2,-1)]
	+
	gneg_[-2]*(dual exteriorPower(6,F^[M]))*gNeg^[(-2,-2)]
    	);
    if n==8 then gNeginc = (gNeginc +
    	gneg_[-3]*(dual F^[kk])*gNeg^[(-3,-1)]
	+
	gneg_[-3]*(dual F^[M])*gNeg^[(-3,-2)]
    	);
    return gNeginc*(dual vars Rg)
    );

-*
--task: given g(nonneg) in first grading, and h = (-1) part in second grading
--return generic matrix -> g(neg) first grading over bigraded polynomial ring
genericBigradeRaw = method();
genericBigradeRaw (LieAlgebra,Module) := Matrix => (g,h) -> (
    kk := ring h;
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
*-

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
	(k,v) -> (k,apply(toList(1..(numcols gens v)),i -> (x_((toSequence (-k))|(1:i)))_R))
	);
    return sum(keys hgrade, k -> (gens hgrade#k)*(transpose matrix{toList varHT#k}))
    )

----------------------------------------
-- differentials of (split exact)^top --
----------------------------------------
--a lot of ad-hoc identification of top pieces in non-F grading (now improved!)

topComplex = method();
topComplex (List,Matrix) := ChainComplex => (frmt,subm) -> (
    len := #frmt-1; R := ring subm;
    d := new MutableHashTable; targ := R^(frmt#0);
    if len==3 then (
	for i from 1 to len do (
	    d#i = map(targ,,topComplex(i,frmt,subm));
	    targ = source d#i
	    );
	) else
    if len==4 then (
	for i from 1 to 2 do (
	    d#i = map(targ,,topComplex(i,frmt,subm));
	    targ = source d#i
	    );
	G := directSum("M"=>R^(frmt_1-1),"M'"=>R^(frmt_1-1));
	d#3 = map(targ,,dual (d#2*(G_["M'"]*G^["M"]+G_["M"]*G^["M'"])));
	d#4 = map(source d#3,,dual d#1)
	);
    return chainComplex(apply(1..len,i->d#i))
    );
topComplex List := ChainComplex => frmt -> (
    if #frmt==5 then return topComplex(frmt,genericGorIndexing(frmt#1)) else
    return topComplex(frmt,genericBigrade(frmt,QQ))
    );
topComplex (ZZ,List,Matrix) := HashTable => (s,frmt,subm) -> (
    kk := QQ;
    algname := formatLookup frmt;
    g := lieAlgebra algname; n := algname_1; g' := truncate(g,0); F := kk^n;
    slF := slLie(F);
    ------------------------------------
    -- I: Format-specific preparation --
    ------------------------------------
    --V = rep
    --bottomreference = the sl(F)-rep to match the bottom piece with
    --topalg = sl(F1) or sl(F3) or so(G)
    --topalginc = inclusion of topalg into g
    --topreference = the topalg-rep to match the top piece with
    --i+1 = node of Dynkin diagram giving L-grading
    --
    --length 3
    if #frmt==4 then (
	F3 := kk^(frmt_3); F1 := kk^(frmt_1);
	L0 := directSum(sl(F3),sl(F1),kk^1); incL0 := L0tog frmt;
	if algname_0=="D" then (
	    if frmt_3==1 then (
		i := (n-1)-1;
		repdict := {,n,1,n-1}
		) else (
		i = (n-3)-1;
		repdict = {,n,n-1,1}
		)
	    ) else
	if algname_0=="E" then (
	    if frmt_3==2 then (
		i = 3-1;
		if n==6 then repdict = {,2,1,6} else repdict = {,2,n,1}
		) else (
		i = 5-1;
		repdict = {,2,1,n}
		)
	    );
	V := extremalRep(g,repdict_s);
	flipF := ((algname_0=="D" and frmt_3 > 1) or (algname_0=="E" and frmt_1 == 5));
	if s==1 then (
	    topalg := slLie(F1), topalginc := incL0*L0_[1];
	    topreference := subRep(topalg,isl(F1),id_(dual F1),dualRep glStandard(F1));
	    if algname_0=="D" and odd n then topreference = dualRep topreference;
	    bottomreference := trivialRep(slF)
	    ) else
	if s==2 then (
	    topalg = slLie(F1), topalginc = incL0*L0_[1];
	    topreference = subRep(topalg,isl(F1),id_F1,glStandard(F1));
	    if algname_0=="D" and odd n then topreference = dualRep topreference;
	    bottomreference = subRep(slF,isl(F),id_(dual F),dualRep glStandard(F));
	    if flipF then bottomreference = dualRep bottomreference
	    ) else
	if s==3 then (
	    topalg = slLie(F3), topalginc = incL0*L0_[0];
	    topreference = subRep(topalg,isl(F3),id_(dual F3),dualRep glStandard(F3));
	    bottomreference = subRep(slF,isl(F),id_F,glStandard(F));
	    if flipF then bottomreference = dualRep bottomreference
	    ) else error "invalid differential"
	) else
    --length 4
    if #frmt==5 then (
	M := kk^(frmt_1-1); G := directSum("M"=>M,"M*"=>dual M);
	i = 0;
	topalg = soLie(M);
	L := (reverse toList(2..n))/(i->i-1);
	topalginc = extendMap(topalg.cache#"e"|topalg.cache#"f",topalg,g.cache#"e"_L|g.cache#"f"_L,g);
	if member(s,{2,3}) then (
	    if n==6 then V = extremalRep(g,1) else V = extremalRep(g,n);
	    topreference = subRep(topalg,topalg.cache#"gl",id_(G),glStandard(G));
	    bottomreference = subRep(slF,isl(F),id_(dual F),dualRep glStandard(F));
	    if n==6 then bottomreference = dualRep bottomreference;
	    ) else
	if member(s,{1,4}) then (
	    if n==6 then V = extremalRep(g,n) else V = extremalRep(g,1);
	    topreference = trivialRep(topalg);
	    bottomreference = subRep(slF,isl(F),id_F, glStandard(F));
	    if n==6 then bottomreference = dualRep bottomreference;
	    ) else error "invalid differential"
	);
    ----------------------------------------
    -- II: Compute map from top to bottom --
    ----------------------------------------
    --get top two pieces in F-grading as g_(<=0) rep, then get action of g_1
    MAXV := max indices module V; MINV := min indices module V;
    Vtop2 := quotientRep(id_(module g'),g',V,V^[MAXV-1,MAXV]);
    Vtop2 = repFromGradedAction(
	g,
	completeIrrepAction(g,actionHT Vtop2,module Vtop2),
	module Vtop2);
    grd := (bracket g)*(g.cache#"alpha"_{i}**id_(module g));
    --get bottom piece in F-grading as slF-rep
    if debugLevel > 0 then << "identifying bottom" << endl;
    bottomid := first equivariantMaps(
	id_(sl(F)),
	subRep(slLie(F),g'_[0]*g'_0_[0],V_[MINV],V),
	bottomreference
	);
    --get top piece in L-grading as topalg-rep
    itop := invariants(gens ker (grd-1),Vtop2);
    if debugLevel > 0 then << "identifying top" << endl;
    topid := first equivariantMaps(
	id_(module topalg),
	topreference,
	subRep(topalg,topalginc,itop,Vtop2)
	);
    R := ring subm;
    rawd := (
	sub(bottomid*V^[MINV],R)
	*exp(parametricAction(V,subm))
	*sub(V_[MAXV-1,MAXV]*itop*topid,R)
	);
    -----------------------------------------------------------------------------
    -- III: return the differential, which may be the dual of the computed map --
    -----------------------------------------------------------------------------
    if #frmt==4 then (
    	if s==2 then return dual rawd else return rawd
	) else
    if #frmt==5 then (
	if s==1 then (
	    return dual rawd
	    ) else
	if s==2 then (
	    return rawd*dual(G_["M*"]*G^["M"]+G_["M"]*G^["M*"])
	    ) else
	if s==3 then (
	    return dual rawd
	    ) else
	if s==4 then return rawd
	)
    )
topComplex (ZZ,List) := HashTable => (s,frmt) -> (
    if #frmt==5 then return topComplex(s,frmt,genericGorIndexing(frmt#1)) else
    return topComplex(s,frmt,genericBigrade(frmt,QQ))
    );
