-------------------------------------
-- ad-hoc creation of Lie algebras --
-------------------------------------

lieAlgebra = method()
lieAlgebra (String,ZZ) := LieAlgebra => (fam,n) -> return lieAlgebra(fam,n,QQ);
--e.g. ("E", 7, QQ)
lieAlgebra (String,ZZ,Ring) := Thing => (fam,n,kk) -> (
    if LieAlgebraCache#?(fam,n,kk) then return LieAlgebraCache#(fam,n,kk);
    F := kk^n;
    if fam=="E" then (
	if n<6 or n>8 then (
    	    error "n must be between 6 and 8 for E_n"
    	    );
	LSchurHT := new MutableHashTable;
	LSchurHT#1 = {1,1,1};
	if n>=6 then LSchurHT#2 = {1,1,1,1,1,1};
	if n==8 then LSchurHT#3 = {2,1,1,1,1,1,1,1};
	NN := max keys LSchurHT;
	g0 := directSum (
	    {0 => directSum(sl(F),kk^1)} |
	    apply(toList(1..NN), i -> i => schurModule(LSchurHT#i, F)) |
	    apply(toList(1..NN), i -> -i => schurModule(LSchurHT#i, dual F))
	    );
	--placeholder Lie algebra
	g := newLieAlgebra(g0,map(g0,g0**g0,0));
        iglF := igl(F); --(1/n)*(g_0)_[1]*tr(F) + (g_0)_[0]*psl(F);
	tglF := inverse(iglF);
	bkt := new MutableHashTable;
        --[0,j] and positive and negative parts first
	--then [-1,1] and from that all other parts can be figured out
	--[0,0]
	bkt#(0,0) = (
    	    g_0_[0]
    	    *psl(F)
    	    *(id_F**(tr(F)*flip(dual F,F))**id_(dual F) - (flip(dual F,F)**tr(F))*(flip(F,(dual F)**F)**id_(dual F)))
    	    *(isl(F)**isl(F))
    	    *(g_0^[0]**g_0^[0])
    	    );
    	--[0,j]
	--this can be cleaned up a bit now
	for i from 1 to NN do (
    	    p := LSchurHT#i;
    	    bkt#(0,i) = (
    		(action schurRep(p,F))*(tglF**id_(g_(i)))
    		);
    	    bkt#(0,-i) = (
    		(action dualRep schurRep(p,F))*(tglF**id_(g_(-i)))
		)
    	    );
	--[1,j] for j>0
	if n>=6 then bkt#(1,1) = (
    	    wedgeProduct(3,3,F)
    	    );
	if n==8 then bkt#(1,2) = (
    	    (id_F**wedgeProduct(2,6,F))
    	    *(wedgeDiag(1,2,F)**id_(g_2))
    	    );
	--[-1,-j] by same matrices
	for j from 1 to (NN-1) do (
    	    bkt#(-1,-j) = map(g_(-j-1),g_(-1)**g_(-j),bkt#(1,j))
    	    );
	--[-1,1], might need to specify [-1,2] first and then test Jacobi identity on this
	bkt#(-1,1) = (
    	    (
		(-1)*iglF*(id_F**tr(exteriorPower(2,F))**id_(dual F))
		*((wedgeDiag(1,2,F))**(wedgeDiag(2,1,dual F)))
		+
		(1/3)*g_0_[1]*tr(exteriorPower(3,F))
		)
    	    *(flip(g_(-1),g_1))    
    	    );
	--everything else via Jacobi identity
	--the part below should be rewritten using
	--completeGradedAction for suitable truncations of g
	--completeGradedAction only needs bracket [+/-1,*] to be defined
	--[-i,j] for i>1, j<=1
	--"fake" g with adjoint action of -1 part
	bkt = fillBracket(g0,bkt);
	g1 := source g_(new Array from -NN..1);
	g' := newLieAlgebra(g1,bkt);
	bkt = fillBracket(g0,completeGradedAction(g',bkt,g1,Sign=>-1));
	--[i,any] for i>1 
        g' = newLieAlgebra(g0,bkt);
	bkt = completeGradedAction(g',bkt,g0,Sign=>+1)
	);
    if fam=="D" then ( --code is mostly copied and simplified from the E case
	F = kk^n;
	LSchurHT = new MutableHashTable;
	LSchurHT#1 = {1,1};
	g0 = directSum (
	    0 => directSum(sl(F),kk^1),
	    -1 => schurModule(LSchurHT#1, F),
	    1 => schurModule(LSchurHT#1, dual F)
	    );
	--placeholder Lie algebra
	g = newLieAlgebra(g0,map(g0,g0**g0,0));
        iglF = igl(F); --(1/n)*(g_0)_[1]*tr(F) + (g_0)_[0]*psl(F);
	tglF = inverse(iglF);
	bkt = new MutableHashTable;
	bkt#(0,0) = (
    	    g_0_[0]
    	    *psl(F)
    	    *(id_F**(tr(F)*flip(dual F,F))**id_(dual F) - (flip(dual F,F)**tr(F))*(flip(F,(dual F)**F)**id_(dual F)))
    	    *(isl(F)**isl(F))
    	    *(g_0^[0]**g_0^[0])
    	    );
	bkt#(0,1) = (
	    (action schurRep({1,1},F))*(tglF**id_(g_1))
	    );
	bkt#(0,-1) = (
	    (action dualRep schurRep({1,1},F))*(tglF**id_(g_(-1)))
	    );
        bkt#(-1,1) = (
    	    (
		iglF*(id_F**tr(F)**id_(dual F))
		*((wedgeDiag(1,1,F))**(wedgeDiag(1,1,dual F)))
		)
    	    *(flip(g_(-1),g_1))
    	    )
	);
    g = newLieAlgebra(g0,bkt,Name=>(fam,n)); V := adjointRep g;
    --put in generator information
    e := new MutableHashTable; f := new MutableHashTable; h := new MutableHashTable;
    for i from 1 to (n-1) do (
	e#i = g_[0]*igl(F)*flip(dual F,F)*adjoint(map(F,F,{(i-1,i)=>1}),kk^1,F);
	f#i = g_[0]*igl(F)*flip(dual F,F)*adjoint(map(F,F,{(i,i-1)=>1}),kk^1,F);
	h#i = (bracket g)*(e#i**f#i)
	);
    epos := fold(apply(toList(1..(n-1)),i->e#i),(a,b)->a|b);
    fpos := fold(apply(toList(1..(n-1)),i->f#i),(a,b)->a|b);
    e#0 = g_[1]*invariants(g^[0]*fpos,subRep(subAlgebra(g_[0],g),g_[0],g_[1],V));
    f#0 = g_[-1]*invariants(g^[0]*epos,subRep(subAlgebra(g_[0],g),g_[0],g_[-1],V));
    h#0 = (bracket g)*(e#0**f#0);
    --eall := e#0|epos; fall := f#0|fpos; hall := fold(apply(toList(0..(n-1)),i->h#i),(a,b)->a|b);
    --CM = fold(apply(n,i->((bracket g)*(hall**e#i))//e#i), (a,b)->a||b)
    if fam=="E" then (
	--so it looks like the situation is
    	--       0     vs Bourbaki notation:      2
    	-- 1 2 3 4 5 6                      7 6 5 4 3 1
    	--
    	--     0                          2
    	-- 1 2 3 4 5                  6 5 4 3 1
    	--
    	--         0                           2
    	-- 1 2 3 4 5 6 7               8 7 6 5 4 3 1
    	--switch to Bourbaki indexing (but unfortunately shifted by one because M2 indexing starts from 0):
	bourbaki := {n-1,0}|reverse toList(1..(n-2))
	) else (
	--                0                      n
	--    1 2 3 ...  n-2 n-1      1 2 3 ... n-2 n-1                 
	--
	--switch to Bourbaki indexing (but unfortunately shifted by one because M2 indexing starts from 0):
	bourbaki = toList(1..(n-1))|{0}
	);
    g.cache#"e" = fold(apply(bourbaki,i->e#i),(a,b)->a|b);
    g.cache#"f" = fold(apply(bourbaki,i->f#i),(a,b)->a|b);
    g.cache#"h" = fold(apply(bourbaki,i->h#i),(a,b)->a|b);
    CartanMatrix := fold(apply(n,i->((bracket g)*(g.cache#"h"**g.cache#"e"_{i}))//g.cache#"e"_{i}), (a,b)->a||b);
    --"coroots"
    g.cache#"alpha" = (g.cache#"h"*(inverse CartanMatrix));
    return LieAlgebraCache#(fam,n,kk) = g
    );

-*
--should be deprecated with overhaul
adj = method();
adj LieAlgebra := HashTable => g -> (
    MIN := min(keys components g); 
    MAX := max(keys components g);
    return hashTable apply(toList select((MIN,MIN)..(MAX,MAX),(i,j)->i+j>=MIN and i+j<=MAX),
	(i,j)->(i,j)=>g_(i,j)
	)
    );
*-

--m should be one of the extremal vertices when the Dynkin diagram is
--arranged as a T-shaped graph 
extremalRep = method();
extremalRep (LieAlgebra,ZZ) := LieAlgebraRep => (g,m) -> (
    if not g.cache#?"negreps" then g.cache#"negreps" = new MutableHashTable;
    if g.cache#"negreps"#?m then return g.cache#"negreps"#m;
    MIN := min indices module g;
    inc := g_(new Array from MIN..0); g' := subAlgebra(inc,g); --set truncation to 0 temporarily
    kk := ring(module g); adj := adjointRep g;
    --type E_n
    if (name g)_0=="E" then (
	--E_8
	if (name g)_1==8 then (
	    --adjoint is "8" and the others aren't implemented
	    if m==8 then (
		return g.cache#"negreps"#m = subRep(g',inc,id_(module adj),adj)
		)
	    ) else
	--E_7
	if (name g)_1==7 then (
	    --adjoint is "1" and beware that "2" is large
	    if m==1 then (
		return g.cache#"negreps"#m = subRep(g',inc,id_(module adj),adj)
		) else (
		return g.cache#"negreps"#m = repFromGradedAction E7rep(m)
		)
	    ) else
        --E_6
	if (name g)_1==6 then (
	    --adjoint is "2"
	    if m==2 then (
		return g.cache#"negreps"#m = subRep(g',inc,id_(module adj),adj)
		) else (
		return g.cache#"negreps"#m = repFromGradedAction E6rep(m)
		)
	    )
	) else 
    if (name g)_0=="D" then (
	return g.cache#"negreps"#m = repFromGradedAction Dnrep((name g)_1,m)
	);
    error "The requested representation is not implemented!"
    );

Dnrep = method();
-- (n)  n-2  n-3 ... 1
--      n-1
--
-- F = kk^n read from n-1 to 1
Dnrep (ZZ,ZZ) := (LieAlgebra,HashTable,Module) => (n,m) -> (
    gneg := truncate(lieAlgebra("D",n),0);
    kk := QQ; F := kk^n;
    if m==1 then (
	V := directSum{
	    0=>dual F,
	    1=>F
	    };
	A := hashTable{
	    (0,0) => (action dualRep schurRep({1},F))*((inverse igl(F))**id_(dual F)),
	    (0,1) => (action schurRep({1},F))*((inverse igl(F))**id_F),
    	    (-1,1) => (
    		(id_(dual F)**tr(dual F))
    		*(wedgeDiag(1,1,dual F)**id_F)
    		)
	    };
	return (gneg,A,V)
	) else
    if m==n then (
	--kk + ... + wedge^(2s) F
	s := n//2;
	V = directSum apply(0..s, i -> i=>exteriorPower(2*i,F));
	A = new MutableHashTable;
	for j from 0 to s do (
	    A#(0,j) = (
		(action schurRep(conjugate{2*j},F))*((isl(F)*gneg_0^[0])**id_(exteriorPower(2*j,F)))
		+
		(-n/2+2*j)*gneg_0^[1]**id_((components V)_j)
		)
	    );
	for j from 1 to s do (
	    A#(-1,j) = (
		(tr(exteriorPower(2,dual F))**id_(exteriorPower(2*j-2,F)))
		*(id_(gneg_(-1))**wedgeDiag(2,2*j-2,F))
		)
	    );
	return (gneg,A,V)
	) else
    if m==(n-1) then (
	--F + ... + wedge^(2s+1) F
	s = (n-1)//2;
	V = directSum apply(0..s, i -> i=>exteriorPower(2*i+1,F));
	A = new MutableHashTable;
	for j from 0 to s do (
	    A#(0,j) = (
		(action schurRep(conjugate{2*j+1},F))*((isl(F)*gneg_0^[0])**id_(exteriorPower(2*j+1,F)))
	    	+
		(-n/2+2*j+1)*gneg_0^[1]**id_((components V)_j)
		)
	    );
	for j from 1 to s do (
	    A#(-1,j) = (
		(tr(exteriorPower(2,dual F))**id_(exteriorPower(2*j-1,F)))
		*(id_(gneg_(-1))**wedgeDiag(2,2*j-1,F))
		)
	    );
	return (gneg,A,V)
	);
    error "The requested representation is not implemented!"
    )

E6rep = method();
E6rep (ZZ) := (LieAlgebra,HashTable,Module) => (m) -> (
    gneg := truncate(lieAlgebra("E",6),0);
    kk := QQ; F := kk^6;
    if m==1 then (
	V := directSum{
    	    0=>F,
    	    1=>exteriorPower(4,F),
    	    2=>exteriorPower(6,F)**F
    	    };
	A := hashTable{
	    (-1,1) => (
    		(tr(gneg_(-1))**id_F)
    		*(id_(gneg_(-1))**wedgeDiag(3,1,F))
    		),
	    (-1,2) => (
    		(tr(gneg_(-1))**wedgeProduct(3,1,F))
    		*(id_(gneg_(-1))**wedgeDiag(3,3,F)**id_F)
    		),
	    (0,0) => (
		(action schurRep({1},F))*((isl(F)*gneg_0^[0])**id_((components V)_0))
		+
		(-3)*gneg_0^[1]**id_((components V)_0)
		),
	    (0,1) => (
		(action schurRep({1,1,1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_1))
		+
		0*gneg_0^[1]**id_((components V)_1)
	    	),
	    (0,2) => (
		(action schurRep({2,1,1,1,1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_2))
		+
		3*gneg_0^[1]**id_((components V)_2)
		)
	    };
	return (gneg,completeGradedAction(gneg,A,V),V)
	) else
    if m==6 then (
	V = directSum{
    	    0=>dual F,
    	    1=>exteriorPower(2,F),
    	    2=>exteriorPower(5,F)
    	    };
	A = hashTable{
	    (-1,1) => (
    		(id_(dual F)**tr(exteriorPower(2,dual F)))
    		*(wedgeDiag(1,2,dual F)**id_((components V)#1))
    		),
	    (-1,2) => (
    		(tr(exteriorPower(3,dual F))**id_((components V)#1))
    		*(id_(gneg_(-1))**wedgeDiag(3,2,F))
    		),
	    (0,0) => (
		(action dualRep schurRep({1},F))*((isl(F)*gneg_0^[0])**id_((components V)_0))
	    	+
		(-3)*gneg_0^[1]**id_((components V)_0)
		),
	    (0,1) => (
		(action schurRep({1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_1))
		+
		0*gneg_0^[1]**id_((components V)_1)
		),
	    (0,2) => (
		(action schurRep({1,1,1,1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_2))
		+
		3*gneg_0^[1]**id_((components V)_2)
		)
	    };
	return (gneg,completeGradedAction(gneg,A,V),V)
	);
    error "The requested representation is not implemented!"
    );

E7rep = method();
E7rep (ZZ) := (LieAlgebra,HashTable,Module) => (m) -> (
    gneg := truncate(lieAlgebra("E",7),0);
    kk := QQ; F := kk^7;
    if m==7 then (
	V := directSum{
	    0=>dual F,
    	    1=>exteriorPower(2,F),
    	    2=>exteriorPower(5,F),
    	    3=>exteriorPower(7,F)**F
	    };
	A := hashTable{
	    (-1,1) => (
    		(id_((components V)#0)**tr(exteriorPower(2,dual F)))
    		*(wedgeDiag(1,2,dual F)**id_((components V)#1))
    		),
	    (-1,2) => (
    		(tr(exteriorPower(3,dual F))**id_((components V)#1))
    		*(id_(gneg_(-1))**wedgeDiag(3,2,F))
    		),
	    (-1,3) => (
    		(tr(gneg_(-1))**wedgeProduct(4,1,F))
    		*(id_(gneg_(-1))**wedgeDiag(3,4,F)**id_F)
    		),
	    (0,0) => (
		(action dualRep schurRep({1},F))*((isl(F)*gneg_0^[0])**id_((components V)_0))
		+(-9/2)*gneg_0^[1]**id_((components V)_0)
		),
	    (0,1) => (
		(action schurRep({1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_1))
		+(-3/2)*gneg_0^[1]**id_((components V)_1)
		),
	    (0,2) => (
		(action schurRep({1,1,1,1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_2))
		+(3/2)*gneg_0^[1]**id_((components V)_2)
		),
	    (0,3) => (
		(action schurRep({2,1,1,1,1,1,1},F))*((isl(F)*gneg_0^[0])**id_((components V)_3))
		+(9/2)*gneg_0^[1]**id_((components V)_3)
		)
	    };
	return (gneg,completeGradedAction(gneg,A,V),V);
	) else
    if m==2 then (
	schuropt := (p,F) -> (p=>schurModule(conjugate p,F));
	V = directSum{
	    0=>directSum(
	    	{}=>kk^1
	    	),
	    1=>directSum(
	    	schuropt({3},F)
	    	),
	    2=>directSum(
	    	schuropt({5,1},F),
	    	schuropt({6},F)
	    	),
	    3=>directSum(
	    	schuropt({7,1,1},F),
	    	schuropt({6,3},F),
	    	schuropt({7,2},F)
	    	),
	    4=>directSum(
	    	schuropt({7,4,1},F),
	    	schuropt({6,6},F),
	    	schuropt({7,5},F)
	    	),
	    5=>directSum(
	    	schuropt({7,6,2},F),
	    	schuropt({7,7,1},F)
	    	),
	    6=>directSum(
	    	schuropt({7,7,4},F)
	    	),
	    7=>directSum(
	    	schuropt({7,7,7},F)
	    	)
	    };
	fromwedge := p -> (schurModule(conjugate p,F)).cache#"Schur"#0;
	invtmaps := hashTable {
    	    {5,1}=>inverse(
		fromwedge{5,1}
		||wedgeProduct(5,1,F)
		),
    	    {7,1,1}=>inverse(
		fromwedge{7,1,1}
		||wedgeProduct(1,1,F)
		),
    	    {6,3}=>inverse(
		(wedgeProduct(6,1,F)**id_(exteriorPower(2,F)))*(id_(exteriorPower(6,F))**wedgeDiag(1,2,F))
		||fromwedge{6,3}
		),
    	    {6,6}=>inverse(
		fromwedge{6,6}
		||(wedgeProduct(6,1,F)**id_(exteriorPower(5,F)))*(id_(exteriorPower(6,F))**wedgeDiag(1,5,F))
		),
    	    {7,4,1}=>inverse(
		wedgeProduct(4,1,F)
		||fromwedge{7,4,1}
		),
    	    {7,6,2}=>inverse(
		fromwedge{7,6,2}
		||(wedgeProduct(6,1,F)**id_F)*(id_(exteriorPower(6,F))**wedgeDiag(1,1,F))
		)
    	    };
	HT := new MutableHashTable;
	HT#({3},{}) = (
	    tr(gneg_(-1))
	    );
	HT#({5,1},{3}) = (
	    (tr(gneg_(-1))**wedgeProduct(2,1,F))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,2,F)**id_F)
		    *invtmaps#{5,1}*(components V)#2_[{5,1}]^[{5,1},{6}]
		    ))
	    );
	HT#({6},{3}) = (
	    (tr(gneg_(-1))**id_(exteriorPower(3,F)))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,3,F))
		    ))
	    );
	HT#({6},{}) = (
	    (-2)*tr(gneg_(-2))
	    );
	HT#({7,1,1},{5,1}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{5,1}
		    *(wedgeProduct(4,1,F)**id_F)
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,4,F)**id_(F**F))
		    *invtmaps#{7,1,1}*(components V)#3_[{7,1,1}]^[{7,1,1},{7,2}]
		    ))
	    );
	HT#({7,2},{5,1}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{5,1}
		    *(wedgeProduct(4,1,F)**id_F)
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,4,F)**wedgeDiag(1,1,F)
		    ))
	    );
	HT#({7,2},{6}) = (
	    (tr(gneg_(-1))**(
		    wedgeProduct(4,2,F)
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,4,F)**id_(exteriorPower(2,F))
		    ))
	    );
	HT#({6,3},{5,1}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{5,1}
		    *(wedgeProduct(3,2,F)**id_F)
		    *(id_(exteriorPower(3,F))**wedgeDiag(2,1,F))
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,3,F)**id_(exteriorPower(3,F)))
		    *invtmaps#{6,3}*(components V)#3_[{6,3}]^[{7,2},{6,3}]
		    ))
	    );
	HT#({6,3},{6}) = (
	    (-1/2)*(tr(gneg_(-1))**(
		    (wedgeProduct(3,3,F))
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,3,F)**id_(exteriorPower(3,F)))
		    *invtmaps#{6,3}*(components V)#3_[{6,3}]^[{7,2},{6,3}]
		    ))
	    );
	HT#({7,2},{3}) = (
	    (-2)*(tr(gneg_(-2))**(
		    (wedgeProduct(1,2,F))
		    ))
	    *(id_(gneg_(-2))**(
		    (wedgeDiag(6,1,F)**id_(exteriorPower(2,F)))
		    ))
	    );
	HT#({6,3},{3}) = (
	    (-1)*(tr(gneg_(-2))**(
		    id_(exteriorPower(3,F))
		    ))
	    *(id_(gneg_(-2))**(
		    invtmaps#{6,3}*(components V)#3_[{6,3}]^[{7,2},{6,3}]
		    ))
	    );
	HT#({6,6},{6,3}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{6,3}
		    *flip(exteriorPower(3,F),exteriorPower(6,F))
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,3,F)**id_(exteriorPower(6,F)))
		    *invtmaps#{6,6}*(components V)#4_[{6,6}]^[{6,6},{7,5}]
		    ))
	    );
	HT#({7,5},{7,2}) = (
	    (tr(gneg_(-1))**(
		    id_(exteriorPower(2,F))
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,2,F)
		    ))
	    );
	HT#({7,5},{6,3}) = (
	    (-5/4)*(tr(gneg_(-1))**(
		    fromwedge{6,3}
		    *flip(exteriorPower(3,F),exteriorPower(6,F))
		    *(id_(exteriorPower(3,F))**wedgeProduct(1,5,F))
		    *(wedgeDiag(3,1,F)**id_(exteriorPower(5,F)))
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,4,F)**id_(exteriorPower(5,F)))
		    ))
	    );
	HT#({7,4,1},{7,1,1}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{7,1,1}
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,1,F)**id_F)
		    *invtmaps#{7,4,1}*(components V)#4_[{7,4,1}]^[{7,5},{7,4,1}]
		    ))
	    );
	HT#({7,4,1},{7,2}) = (
	    (-3/10)*(tr(gneg_(-1))**(
		    wedgeProduct(1,1,F)
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,1,F)**id_F)
		    *invtmaps#{7,4,1}*(components V)#4_[{7,4,1}]^[{7,5},{7,4,1}]
		    ))
	    );
	HT#({7,4,1},{6,3}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{6,3}
		    *(wedgeProduct(4,2,F)**wedgeProduct(2,1,F))
		    *(id_(exteriorPower(4,F))**wedgeDiag(2,2,F)**id_F)
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,4,F)**id_(exteriorPower(4,F)**F))
		    *invtmaps#{7,4,1}*(components V)#4_[{7,4,1}]^[{7,5},{7,4,1}]
		    ))
	    );
	HT#({6,6},{6}) = (
	    (-1)*(tr(gneg_(-2))**(
		    id_(exteriorPower(6,F))
		    ))
	    *(id_(gneg_(-2))**(
		    invtmaps#{6,6}*(components V)#4_[{6,6}]^[{6,6},{7,5}]
		    ))
	    );
	HT#({7,5},{5,1}) = (
	    (-5/2)*(tr(gneg_(-2))**(
		    fromwedge{5,1}
		    *(wedgeProduct(1,4,F)**id_F)
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**wedgeDiag(4,1,F)
		    ))
	    );
	-*
	HT#({7,5},{6}) = (
	    0*(tr(gneg_(-2))**(
		    wedgeProduct(1,5,F)
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**id_(exteriorPower(5,F))
		    ))
	    );
	*-
	HT#({7,4,1},{5,1}) = (
	    (-1)*(tr(gneg_(-2))**(
		    fromwedge{5,1}
		    *(wedgeProduct(1,4,F)**id_F)
		    ))
	    *(id_(gneg_(-2))**(
		    (wedgeDiag(6,1,F)**id_(exteriorPower(4,F)**F))
		    *invtmaps#{7,4,1}*(components V)#4_[{7,4,1}]^[{7,5},{7,4,1}]
		    ))
	    );
	HT#({7,6,2},{6,6}) = (
	    (-1)*(tr(gneg_(-1))**(
		    fromwedge{6,6}
		    *(wedgeProduct(4,2,F)**id_(exteriorPower(6,F)))
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,4,F)**flip(exteriorPower(6,F),exteriorPower(2,F)))
		    *invtmaps#{7,6,2}*(components V)#5_[{7,6,2}]^[{7,6,2},{7,7,1}]
		    ))
	    );
	HT#({7,6,2},{7,5}) = (
	    (-6/25)*(tr(gneg_(-1))**(
		    wedgeProduct(3,2,F)
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,3,F)**id_(exteriorPower(2,F)))
		    *invtmaps#{7,6,2}*(components V)#5_[{7,6,2}]^[{7,6,2},{7,7,1}]
		    ))
	    );
	HT#({7,6,2},{7,4,1}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{7,4,1}
		    *(wedgeProduct(3,1,F)**id_F)
		    *(id_(exteriorPower(3,F))**wedgeDiag(1,1,F))
		    ))
	    *(id_(gneg_(-1))**(
		    (wedgeDiag(3,3,F)**id_(exteriorPower(2,F)))
		    *invtmaps#{7,6,2}*(components V)#5_[{7,6,2}]^[{7,6,2},{7,7,1}]
		    ))
	    );
	HT#({7,6,2},{7,2}) = (
	    (3/5)*(tr(gneg_(-2))**(
		    id_(exteriorPower(2,F))
		    ))
	    *(id_(gneg_(-2))**(
		    invtmaps#{7,6,2}*(components V)#5_[{7,6,2}]^[{7,6,2},{7,7,1}]
		    ))
	    );
	HT#({7,6,2},{6,3}) = (
	    (tr(gneg_(-2))**(
		    fromwedge{6,3}
		    *(id_(exteriorPower(6,F))**wedgeProduct(1,2,F))
		    *(flip(F,exteriorPower(6,F))**id_(exteriorPower(2,F)))
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**id_(exteriorPower(6,F)**exteriorPower(2,F))
		    *invtmaps#{7,6,2}*(components V)#5_[{7,6,2}]^[{7,6,2},{7,7,1}]
		    ))
	    );
	HT#({7,7,1},{7,5}) = (
	    (12/25)*(tr(gneg_(-1))**(
		    wedgeProduct(4,1,F)
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,4,F)**id_F
		    ))
	    );
	HT#({7,7,1},{7,4,1}) = (
	    (tr(gneg_(-1))**(
		    fromwedge{7,4,1}
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,4,F)**id_F
		    ))
	    );
	HT#({7,7,1},{7,1,1}) = (
	    (-2)*(tr(gneg_(-2))**(
		    fromwedge{7,1,1}
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**id_F
		    ))
	    );
	-*
	HT#({7,7,1},{7,2}) = (
	    0*(tr(gneg_(-2))**(
		    wedgeProduct(1,1,F)
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**id_F
		    ))
	    );
	*-
	HT#({7,7,4},{7,6,2}) = (
	    2*(tr(gneg_(-1))**(
		    fromwedge{7,6,2}
		    *(wedgeProduct(4,2,F)**id_(exteriorPower(2,F)))
		    *(id_(exteriorPower(4,F))**wedgeDiag(2,2,F))
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,4,F)**id_(exteriorPower(4,F))
		    ))
	    );
	HT#({7,7,4},{7,7,1}) = (
	    (-1)*(tr(gneg_(-1))**(
		    id_F
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,1,F)
		    ))
	    );
	HT#({7,7,4},{7,5}) = (
	    (24/25)*(tr(gneg_(-2))**(
		    wedgeProduct(1,4,F)
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**id_(exteriorPower(4,F))
		    ))
	    );
	HT#({7,7,4},{7,4,1}) = (
	    2*(tr(gneg_(-2))**(
		    fromwedge{7,4,1}
		    *flip(F,exteriorPower(4,F))
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)**id_(exteriorPower(4,F))
		    ))
	    );
	HT#({7,7,7},{7,7,4}) = (
	    (tr(gneg_(-1))**(
		    id_(exteriorPower(4,F))
		    ))
	    *(id_(gneg_(-1))**(
		    wedgeDiag(3,4,F)
		    ))
	    );
	HT#({7,7,7},{7,7,1}) = (
	    2*(tr(gneg_(-2))**(
		    id_F
		    ))
	    *(id_(gneg_(-2))**(
		    wedgeDiag(6,1,F)
		    ))
	    );
    	pT := hashTable{
    	    0=>{{}},
    	    1=>{{3}},
    	    2=>{{5,1},{6}},
    	    3=>{{7,1,1},{7,2},{6,3}},
    	    4=>{{6,6},{7,5},{7,4,1}},
    	    5=>{{7,6,2},{7,7,1}},
    	    6=>{{7,7,4}},
    	    7=>{{7,7,7}}
    	    };
	E7act := (p,q) -> (
    	    n := ((sum q)-(sum p))//3;
    	    if HT#?(p,q) then return HT#(p,q) else
    	    if q=={} then return map(kk^1,gneg_n**schurModule(conjugate p,F),0) else
    	    --p won't be 0 in my use cases
    	    return map(schurModule(conjugate q,F),gneg_n**schurModule(conjugate p,F),0)
    	    );
	A = new MutableHashTable;
	for i from -2 to -1 do (
    	    for j from -i to 7 do (
		A#(i,j) = sum((pT#j**pT#(i+j))/toSequence, (p,q) -> (
			(components V)#(i+j)_[q]*E7act(p,q)*(id_(gneg_i)**(components V)#j^[p])
			)
	    	    )
		)
    	    );
	A#(0,0) = (-21/2)*gneg_0^[1]**id_((components V)_0);
	for j from 1 to 7 do (
	    A#(0,j) = sum(pT#j, p -> (
		    (components V)#j_[p]*(action schurRep(conjugate p,F))*((isl(F)*gneg_0^[0])**((components V)#j^[p]))
		    )
		)+(-21/2 + 3*j)*gneg_0^[1]**id_((components V)_j)
	    );
	return (gneg,A,V)
	);
    error "The requested representation is not implemented!"
    );
