-----------------------------------------------------
-- A translation of Luis' Markov package to M2   -----
------------------------------------------------------

-- Give a graph as a hash table i => descendents

-- Make a graph
-- Input: a directed acyclic graph in the form of a 
--        list of lists of children.
--        the vertices must be named 1..n, some n.
--        ASSUMPTION: we assume that the descendents of vertex
--        i are all less than i.  This only represents DAGS.
-- Output: A hashtable G with keys 1..n, and G#i is the
--        the set of all children of the vertex i.
-- This routine produces a useful version of a 'graph'
-- which we use in routines throughout this package.
makeGraph = (g) -> (
     h := new MutableHashTable;
     scan(#g, i -> h#(i+1) = set g#i);
     new HashTable from h)

descendents = (G,v) -> (
     -- returns a set of vertices
     result := G#v;
     scan(reverse(1..v-1), i -> (
	  if member(i,result) then result = result + G#i;
     ));
     result)

nondescendents = (G,v) -> set(1..#G) - descendents(G,v) - set {v}

parents = (G,v) -> set select(1..#G, i -> member(v, G#i))

children = (G,v) -> G#v

  --------------------
  -- Graph features --
  --------------------
  subgraph = (G,vertices) -> (
       -- make a graph on 1..#vertices
       H := new MutableHashTable;
       scan(keys G, i -> H#i = set{});
       scan(#vertices, i -> H#(vertices#i) = set{i+1});
       tr := (s) -> if #s === 0 then {} else toList sum apply(toList s, i -> H#i);
       G' = apply(vertices, i -> tr(G#i));
       makeGraph G')

  H4a = makeGraph {{},{1},{2},{1,3}};
  H4b = makeGraph {{},{1},{1},{2,3}};

  is4cycle = (G) -> G === H4a or G === H4b
       -- G should be a graph on 4 elements


  n4cycles = (G) -> (
       x := subsets(toList(1..#G), 4);
       # select(x, s -> is4cycle subgraph(G,s)))
  ///
      G = makeGraph D5s_65
      G1 = subgraph(G,{1,2,3,4})
      n4cycles G
      G1 === H4b
      subgraph(G,{1,2,3,5})
      sort apply(#D5s, i -> (G := makeGraph D5s#i; {n4cycles G, i}))
      select(0..#D5s-1, i -> (n4cycles makeGraph D5s#i > 0))
      select(0..#D5s-1, i -> (n4cycles makeGraph D5s#i == 3))
      select(0..#D5s-1, i -> #D5s#1>=1 and  # parents(makeGraph D5s#i, 2) >= 3)
  ///
--------------------------
-- Statement calculus ----
--------------------------
-- A dependency is a list {A,B,C}
--  where A,B,C are (disjoint) subsets of positive integers.
--  The meaning is: A is independent of B given C.
-- A dependency list is a list of dependencies

-- No serious attempt is made to remove redundant dependencies.
-- However, we have several very simple routines to remove
-- the most obvious redundant elements

-- If S and T represent exactly the same dependency, return true.
equivStmts = (S,T) -> S#2 === T#2 and set{S#0,S#1} === set{T#0,T#1}

removeRedundants = (Ds) -> (
     -- Ds is a list of triples of sets {A,B,C}
     -- test1: returns true if D1 can be removed
     -- Return a sublist of Ds which removes any 
     --  that test1 declares not necessary.
     test1 := (D1,D2) -> (D1_2 === D2_2 and 
                          ((isSubset(D1_0, D2_0) and isSubset(D1_1, D2_1))
	               or (isSubset(D1_1, D2_0) and isSubset(D1_0, D2_1))));
     -- first remove non-unique elements, if any
     Ds = apply(Ds, d -> {set{d#0,d#1}, d#2});
     Ds = unique Ds;
     Ds = apply(Ds, d -> append(toList(d#0), d#1));
     c := toList select(0..#Ds-1, i -> (
	       a := Ds_i;
	       D0 := drop(Ds,{i,i});
	       all(D0, b -> not test1(a,b))));
     Ds_c)

-- return the set of variables which occur in some
-- dependency.  The input 'Ds' is a list of {A,B,C} 
-- dependencies
occuring = (Ds) -> sum apply(Ds, c -> sum c) 

cleardep = (Ds) -> (
     -- if there is any element which is in every b_i_2
     -- remove it.
     -- This is used to remove a variable if possible.
     -- USE IT WITH CAUTION: it will change the
     -- resulting ideal
     commons := product apply(Ds, c -> c_2);
     apply(Ds, c -> {c_0,c_1,c_2 - commons}))

--------------------------
-- Bayes ball algorithm --
--------------------------
bayesBall = (A,C,G) -> (
     -- A is a set in 1..n (n = #G)
     -- C is a set in 1..n (the "blocking set")
     -- G is a DAG
     -- Returns the subset B of 1..n which is
     --   independent of A given C.
     -- The algorithm is the Bayes Ball algorithm,
     -- as implemented by Luis Garcia, after
     -- the paper of Ross Schlacter
     n := #G;
     zeros := toList((n+1):false);
     visited := new MutableList from zeros;
     blocked := new MutableList from zeros;
     up := new MutableList from zeros;
     down := new MutableList from zeros;
     top := new MutableList from zeros;
     bottom := new MutableList from zeros;
     vqueue := sort toList A;
     -- Now initialize vqueue, set blocked
     scan(vqueue, a -> up#a = true);
     scan(toList C, c -> blocked#c = true);
     local pa;
     local ch;
     while #vqueue > 0 do (
	  v := vqueue#-1;
	  vqueue = drop(vqueue,-1);
	  visited#v = true;
	  if not blocked#v and up#v
	  then (
	       if not top#v then (
		    top#v = true;
		    pa = toList parents(G,v);
		    scan(pa, i -> up#i = true);
		    vqueue = join(vqueue,pa);
		    );
	       if not bottom#v then (
		    bottom#v = true;
		    ch = toList children(G,v);
		    scan(ch, i -> down#i = true);
		    vqueue = join(vqueue,ch);
		    );
	       );
	  if down#v
	  then (
	       if blocked#v and not top#v then (
		    top#v = true;
		    pa = toList parents(G,v);
		    scan(pa, i -> up#i = true);
		    vqueue = join(vqueue,pa);
		    );
	       if not blocked#v and not bottom#v then (
		    bottom#v = true;
		    ch = toList children(G,v);
		    scan(ch, i -> down#i = true);
		    vqueue = join(vqueue,ch);
		    );
	       );
	  ); -- while loop
     set toList select(1..n, i -> not blocked#i and not bottom#i)
     )
--------------------------
-- Markov relationships --
--------------------------
pairMarkov = (G) -> (
     -- given a graph G, returns a list of triples {A,B,C}
     -- where A,B,C are disjoint sets, and for every vertex v
     -- and non-descendent w of v,
     -- {v, w, nondescendents(G,v) - w}
     flatten apply(1..#G, v -> (
	       ND := nondescendents(G,v);
	       W := ND - parents(G,v);
	       apply(toList W, w -> {set {v}, set{w}, ND - set{w}}))))
			 
localMarkov = (G) -> (
     -- Given a graph G, return a list of triples {A,B,C}
     -- of the form {v, nondescendents - parents, parents}
     result := {};
     scan(1..#G, v -> (
	       ND := nondescendents(G,v);
	       P := parents(G,v);
	       if #(ND - P) > 0 then
	         result = append(result,{set{v}, ND - P, P})));
     result)

globalMarkov = (G) -> (
     -- Given a graph G, return a complete list of triples {A,B,C}
     -- so that A and B are d-separated by C (in the graph G).
     -- If G is large, this should maybe be rewritten so that
     -- one huge list of subsets is not made all at once
     n := #G;
     vertices := toList(1..n);
     result := {};
     AX := subsets vertices;
     AX = drop(AX,1); -- drop the empty set
     AX = drop(AX,-1); -- drop the entire set
     scan(AX, A -> (
	       A = set A;
	       Acomplement := toList(set vertices - A);
	       CX := subsets Acomplement;
	       CX = drop(CX,-1); -- we don't want C to be the entire complement
	       scan(CX, C -> (
			 C = set C;
			 B := bayesBall(A,C,G);
			 if #B > 0 then (
			      B1 := {A,B,C};
			      if all(result, B2 -> not equivStmts(B1,B2))
			      then 
			          result = append(result, {A,B,C});
	       )))));
     result
     )
---------------------------
-- Constructing the ring --
---------------------------
probring = d -> (
     -- Returns a ring in d1*...*dn variables
     -- d should be a list of integers (d1, d2, ..., dn)
     -- where each di >= 1
     start := (#d):1;
     QQ[(symbol p)_start .. (symbol p)_d])

probring1 = (parents, d) -> (
     -- Returns a ring with variables
     --   a_(i1,...,ir) and q_(j2,...,jn), where
     -- r-1 is the number of parents of 1
     -- each j_p ranges over 1..d_p
     -- each i_p ranges over 1..(d_(parents_p))
     -- parents should be a list of indices 1..#d which 
     -- are the parents of vertex 1.
     -- d should be a sequence of integers (d1, d2, ..., dn)
     -- where each di >= 1
     start := (#d-1):1;
     lastd := drop(d,1);
     startpa := (#parents+1):1;
     lastpa := toSequence(prepend(d#0, apply(parents, i -> d#(i-1))));
     QQ[(symbol a)_startpa .. (symbol a)_lastpa, (symbol q)_start .. (symbol q)_lastd])

toring1 = (parents,d,R,R1) -> (
     -- R should be probring d
     -- R1 should be probring(parents,d)
     -- Constructs a ring map F : R --> R1
     -- which is the partial factorization map
     F := toList apply(((#d):1) .. d, i -> (
	       pa := toSequence(prepend(i#0, apply(parents, j -> i#(j-1))));
	       a_pa * q_(drop(i,1))));
     map(R1,R,F)
     )

margin1 = (d,R) -> (
     -- R should be probring d.
     -- construct the ring map which replaces p_(1,i2,...,in)
     --   with the sum of all p_(j,i2,...,in), all j.
     F := toList apply(((#d):1) .. d, i -> (
	       if i#0 > 1 then p_i
	       else (
		    i0 := drop(i,1);
		    p_i - sum(apply(toList(2..d#0), j -> p_(prepend(j,i0)))))));
     map(R,R,F))

margin = (v) -> (d,R) -> (
     -- R should be probring d.
     -- construct the ring map which replaces p_(1,i2,...,in)
     --   with the sum of all p_(j,i2,...,in), all j.
     v = v-1;
     F := toList apply(((#d):1) .. d, i -> (
	       if i#v > 1 then p_i
	       else (
		    i0 := drop(i,1);
		    p_i - sum(apply(toList(2..d#v), j -> (
			      newi := join(take(i,v), {j}, take(i,v-#d+1));
			      print p_newi;
			      p_newi))))));
     map(R,R,F))
-------------------------------------------------------
-- Constructing the ideal of a independence relation --
-------------------------------------------------------
cartesian = (L) -> (
     if #L == 1 then 
	return toList apply (L#0, e -> singleton e);
     L0 := L#0;
     Lrest := drop (L,1);
     C := cartesian Lrest;
     flatten apply (L0, s -> apply (C, c -> prepend (s,c))))

possibleValues = (d,A) ->
     cartesian (toList apply(1..#d, i -> 
	       if member(i,A) 
	       then toList(1..d#(i-1)) 
	       else {0}))

prob = (d,s) -> (
     L := cartesian toList apply (#d, i -> 
	   if s#i === 0 
	   then toList(1..d#i) 
	   else {s#i});
     sum apply (L, v -> p_v))

indepMatrices = (d,A,B,C) -> (
     -- d is a sequence of integers
     -- A,B,C should be disjoint sets of integers in 1..#d
     Avals = possibleValues(d,A);
     Bvals = possibleValues(d,B);
     Cvals = possibleValues(d,C);
     apply(Cvals, c -> (
       matrix apply(Avals, a -> apply(Bvals, b -> (
		      e := toSequence(toList a + toList b + toList c);
		      prob(d,e))))))
     )

indepIdeal = (d,A,B,C) -> 
     sum apply(indepMatrices(d,A,B,C), m -> minors(2,m))

Ideps = (d, Ds) -> (
     R = probring d;
     sum apply(Ds, D -> indepIdeal(d,D_0,D_1,D_2)))

-----------------------------------------------------
-- local Markov ideal
localMarkovIdeal = (d,gr) -> (
     R = probring d;
     G := makeGraph gr;
     D := localMarkov G;
     D = removeRedundants D;
     sum apply(D, D0 -> indepIdeal(d, D0_0,D0_1,D0_2)))

----------------------
-- Binary variables --
----------------------
  -- binaryR#0, binaryR#1 are not very useful...
binaryD = apply(0..7, d -> toSequence(d:2));
binaryR = apply(binaryD, probring);

simplifyDeps = (b) -> (
     b = removeRedundants b;
     b = cleardep b;
     s := sort toList occuring b;
     d := #s;
     h := new MutableHashTable;
     scan(d, i -> h#(s#i) = i+1);
     g := b/(c -> (
	       -- c is a list of three sets
	       {set apply(toList c#0, j -> h#j),
		set apply(toList c#1, j -> h#j),
		set apply(toList c#2, j -> h#j)}));
     R = binaryR#d;
     use R;
     g)     

IBinaryDeps = (b) -> (
     -- Given a set of dependencies, compute the
     -- ideal in the smallest possible ring.
     -- IE, if any variables don't occur, use a smaller
     -- size ring.
     s := sort toList occuring b;
     d := #s;
     h := new MutableHashTable;
     scan(d, i -> h#(s#i) = i+1);
     g = b/(c -> (
	       -- c is a list of three sets
	       {set apply(toList c#0, j -> h#j),
		set apply(toList c#1, j -> h#j),
		set apply(toList c#2, j -> h#j)}));
     R = binaryR#d;
     use R;
     << "using" << endl;
     g/print;
     sum apply(g, D -> indepIdeal(binaryD#d,D_0,D_1,D_2)))

localMarkovConditions = (gr) -> (
     D := localMarkov makeGraph gr;
     --simplifyDeps D
     removeRedundants D
     )

globalMarkovConditions = (gr) -> (
     D := globalMarkov makeGraph gr;
     --simplifyDeps D
     removeRedundants D
     )
     
localIdeal = (gr) -> (
     D := localMarkov makeGraph gr;
     D = simplifyDeps D;
     d := #(occuring D);
     J := sum apply(D, c -> indepIdeal(binaryD#d, c_0,c_1,c_2));
     F := margin1(binaryD#d, binaryR#d);
     F J)

globalIdeal = (gr) -> (
     D := globalMarkov makeGraph gr;
     D = simplifyDeps D;
     d := #(occuring D);
     J := sum apply(D, c -> indepIdeal(binaryD#d, c_0,c_1,c_2));
     F := margin1(binaryD#d, binaryR#d);
     F J)

Iglobal = (D) -> (
     -- D is a list of dependencies
     -- d is the largest variable which occurs
     d := max apply(D, b -> max join(apply(b, c -> max toList c)));
     J := sum apply(D, c -> indepIdeal(binaryD#d, c_0,c_1,c_2));
     F := margin1(binaryD#d, binaryR#d);
     F J)
///
-- tests and examples of using these routines
restart
load "markov.m2" -- this file
G = makeGraph{{}, {1}, {2}, {1, 2, 3}, {4}}
parents(G,1)
parents(G,2)
parents(G,3)
parents(G,4)
parents(G,5)
descendents(G,5)
descendents(G,4)
descendents(G,3)
nondescendents(G,3)
G

scan(pairMarkov G, D -> print toString D)
scan(localMarkov G, D -> print toString D)
scan(globalMarkov G, D -> print toString D)
scan(removeRedundants globalMarkov G, D -> print toString D)
Ds = removeRedundants globalMarkov G;
occuring Ds

R = probring(2,3,3,3)
numgens R
gens R

-- Here are useful already created values for 
-- up through 7 random variables
binaryD_5
binaryR_5

R = binaryR_4

-- Marginalizing over vertex 1.
-- This often simplifies the Markov ideals.
F = margin1((2,2,2,2),R)
transpose F.matrix
F p_(1,1,1,1)

-- The partial factorization map
R1 = probring1({2,3},(2,2,2,2))
  -- {2,3} is the list of parents of 1.
F = toring1({2,3},(2,2,2,2),R,R1)
transpose F.matrix

-- prob
use R
gens R
prob((2,2,2,2),{0,1,1,0})

-- making the ideals/matrices
-- Use the binary 4 variable ring R from above
indepMatrices((2,2,2,2),set{1,2},set{3},set{4})
J = indepIdeal((2,2,2,2),set{1,2},set{3},set{4})
(codim J, degree J)

-- local Markov ideal, starting with an externally
-- constructed graph (ie: a list of children.)
-- This defines the ring too, removes redundant
-- variables.  WARNING: it might remove random
-- variables which appear as the dependent in every dependency.
-- (This simplifies the ideal).

J = localMarkovIdeal((2,2,2,2),{{},{1},{2},{3}})
transpose gens J

G = makeGraph{{},{1},{2},{3}}
D = localMarkov G
J1 = Ideps D


R = probring(2,2,3)
R = probring(4:2)
prob((2,2,2,2),{0,1,0,2})
gens R
#oo
cartesian{{1,2},{1,2},{1,2,3}}
possibleValues((2,2,2,2),set(1,3))
indepMatrices((2,2,2,2),set{1},set{2},set{3,4})
J = indepIdeal((2,2,2,2),set{1},set{2},set{3,4})

-- Test of Bayes Ball
G = makeGraph{{}, {1}, {2}, {1, 2, 3}, {4}}
Ds = globalMarkov G
oo/print;
removeRedundants Ds
oo/print;
bayesBall(set{1},set{2},G)

restart
load "luis.m2"  -- this is THIS file
J = localIdeal{{}, {1}, {2}, {1, 2, 3}, {4}};
JG = globalIdeal{{}, {1}, {2}, {1, 2, 3}, {4}};
F = margin1(binaryD#4, R)
J = F J
JG = F JG;
apply(flatten entries gens JG, f -> (<< "." << flush; J : f));
intersect oo;
intersect(o35,JG) == J -- yes
C = primaryDecomposition o35;
transpose gens J
transpose gens JG
load "facGB.m2"
load "primdecomp-tools.m2"
JG1 = ideal compress((gens JG) % J);
JG1 = flatten entries gens JG1;
JG1 = ideal select(JG1, f -> size f === 2);
transpose gens JG1
J1 = J : JG1;
J1 = J : JG_0;
J2 = J1 : JG_1;
L = apply(flatten entries gens JG, f -> J : f);
info J
info JG
J1 = J : JG
J = localMarkovIdeal((2,2,2,2,2), {{}, {1}, {2}, {1, 2, 3}, {4}});


info J
(margin1((2,2,2,2),R)) J
transpose gens oo

R = probring(2,2,2,2,2)
R1 = probring1({2,3},(2,2,2,2,2))
toring1({2,3},(2,2,2,2,2),R,R1)
margin1((2,2,2,2,2),R)
transpose oo.matrix

D1 = {set{1},set{2},set{3,4}}
D2 = {set{1},set{2},set{3}}
R = probring(2,2,2,2)
J1 = indepIdeal((2,2,2,2),D1_0,D1_1,D1_2)
J2 = indepIdeal((2,2,2,2),D2_0,D2_1,D2_2)
codim J1
codim J2
(gens J2) % J1
(gens J1) % J2
///
