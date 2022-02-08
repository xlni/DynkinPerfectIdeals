installPackage "DynkinPerfectIdeals";
-----------------------------------------------
-- 1. Constructing Ftop in familiar notation --
-----------------------------------------------
needsPackage "DynkinPerfectIdeals";

--for length 3:
frmt = {1,5,6,2}
(Lgen,L) = defectLieAlgebraDual(frmt,{b,c,d,e})
--map Lgen to g
S = ring Lgen; ggen = (Ltog frmt)*Lgen;
F = topComplex(frmt,ggen)

--a command to display degrees and #terms:
mapInfo F.dd_3

F.dd_3_(0,0)

--note in particular that this output is single-graded

--for length 4:
frmt = {1,6,10,6,1}
ggen = genericGorIndexing(frmt_1,{b,c,d,e}); S = ring ggen;
F = topComplex(frmt,ggen)

netList entries F.dd_4

----------------------------
-- 2. Multigraded version --
----------------------------
needsPackage "DynkinPerfectIdeals";

frmt = {1,5,6,2}; g = lieAlgebra(formatLookup frmt), g' = truncate(g,0);
--genericMultigrade produces a generic map to n_- in g
ggen = genericMultigrade(g,b); S = ring ggen;
--The variables of S are weight-graded, so in this case Z^6 graded--the first
--6 indices are the weights and the last index is just to distinguish variables
--of the same degree.
--
-- (2) 4  5  6
--    (3)
--     1
--
--keep only the variables with positive (2),(3)-bidegree
--(we follow Bourbaki ordering but indexing starts at zero hence the line says {1,2})
--those variables do not alter the behavior of the output complex, but slow down
--the computation significantly.
R = prune (S/ideal(select(gens S, i -> not all((degree i)_{1,2},j->j>0)))) 
ggen = sub(ggen,R);
--project onto g_(<=0)
inds = new Array from indices module g'
ggen' = g'_inds*g^inds*ggen;

F = topComplex(frmt,ggen')

--here are the multidegrees of the generators
matrix degrees source F.dd_1

-----------------------------------
-- 3. Multigraded specialization --
-----------------------------------
--using the multigrading set up in the preceding section, have finer control over
--specialization

Rran = ZZ/32003[x,y,z]

--given a projection X: QQ^6 -> QQ^1, substitutes for each multigraded
--generator of degree v a random form of degree Xv in Rran if possible
--(otherwise sets to 0).
subran = X -> (
    apply(gens R, i -> (
	    degvec := ((matrix{degree i})*(dual X))_(0,0);
	    if liftable(degvec,ZZ) then (
		return i => random(lift(degvec,ZZ),Rran)
		) else (
		return i => 0
		)
	    )
	)
    )

--example:
--here is a projection that yields generators of degree
--(2,2,5,5,5) #1
l = {-4,-3,4,0,0,3}

X = matrix {l}
gran = sub(ggen',subran X);
Fran = topComplex(frmt,gran); I = ideal F.dd_1;
isHomogeneous Fran
prune HH Fran
codim I
betti Fran

needsPackage "ResidualIntersections"
isLicci I

--here are more examples
--(2,3,4,4,6) #2
l = {4,-4,-1,2,0,1}

--(2,3,4,5,5) #3
l = {4,-3,0,0,1,1}

--(3,4,4,4,5) #7
l = {4,-1,-2,1,0,1}




--One can also do a link before specializing:
Igen = ideal F.dd_1;
J = ideal(Igen_0,Igen_1,Igen_2); codim J
Igen' = J:Igen; --Fgen' = res Igen'
--M = QQ**(matrix degrees source Fgen'.dd_2)

--(3,3,3,3,7) #4
l' = {-4,4,6,-5,0,0}

X = matrix {l'}
I' = sub(Igen',subran X); codim I'
F = res I'
isHomogeneous F
prune HH F
betti F

--other examples:
--(3,3,3,4,6) #5
l' = {-2,4,5,-5,0,0}

--(3,3,3,5,5) #6
l' = {0,4,4,-5,0,0}

-------------------------------------
-- 4: Working with representations --
-------------------------------------
--One of the next steps is to extend this package to allow for computation
--of higher structure maps for any starting resolution.
--Some of the tools below may be helpful for that
needsPackage "DynkinPerfectIdeals"

g = lieAlgebra("E",6)
V = adjointRep g

V' = schurRep({1,1},V,id_(exteriorPower(2,module V)))

--highest weight vectors
hwv = invariants(g.cache#"e",V');
--so there are two irreducible components

--here are their weights
--(luckily the two columns of the output were already h-eigenvectors)
(action V')*(g.cache#"h"**hwv_{0})//hwv_{0}
(action V')*(g.cache#"h"**hwv_{1})//hwv_{1}

--adjoint sitting inside V'
V1 = generate(hwv_{0},V');
--the other part
V2 = generate(hwv_{1},V');

