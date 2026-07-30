#############################################################################
##
##  verify.g     GAP verification for
##               "Coprime actions and nonvanishing characters"
##
##  Usage:   gap -q verify.g      (or  gap> Read("verify.g");  )
##
##  WHAT CAN AND CANNOT BE CHECKED HERE
##
##  The counterexample of the paper has |G| = 2^135.  No computer algebra
##  system can build that group, and the paper never asks one to: the proof
##  is by hand.  What GAP *can* do, and does below, is check every ingredient
##  the counterexample is assembled from, using its own character theory
##  rather than any formula of the paper.
##
##  The counterexample is: (machinery) + (one arithmetic identity).
##
##    machinery   For A of odd order acting on an F_2-space V with C_V(A)=0,
##                and G = B x| V with B = F_2^V the Boolean functions:
##                  (M1)  C_G(A) = B^A, elementary abelian of rank the
##                        number of A-orbits on V;
##                  (M2)  |Irr_A(G)| = |C/C'|;
##                  (M3)  for u = delta_0, the character chi_u = Ind_B^G
##                        lambda_u is irreducible, A-invariant, of degree
##                        |V|, and  chi_u(c) = |V| - 2|supp c|  for c in B^A.
##                        [Lemma 2.10 -- the lemma that produces the zero]
##
##    arithmetic  At dim V = 7 with |A| = 21 the orbit sizes are
##                1,3,3,3,3,3,7,21,21,21,21,21 and 1+21+21+21 = 64 = |V|/2,
##                so some c in B^A has |supp c| = |V|/2 and (M3) gives
##                chi_u(c) = 0.
##
##  Section 1 checks the arithmetic at dim V = 7 exactly (no group needed).
##  Section 2 checks the machinery (M1)-(M3) against GAP's Irr, Centralizer
##            and InducedClassFunction, in the *same* family G = C_2 wr V,
##            for dim V = 2 and 3 (|G| = 2^6 and 2^11).  Note G = C_2 wr V
##            is exactly B x| V, since B = F_2^V is the regular F_2[V]-module.
##  Section 3 counts |N_A(G)| and |C/C'| from first principles in those
##            small groups, confirming they agree there -- as the paper
##            predicts, since those V are not balanced.
##  Section 4 (optional, slower) does the same for a *balanced* V, obtained
##            by dropping the fixed-point-free hypothesis, where GAP can
##            therefore exhibit an actual vanishing invariant character.
##
#############################################################################

Print("\n=== Section 1: the arithmetic at dim V = 7 ===\n\n");

# V = F_4^2 (+) F_8 as F_2^7; T = mult by (omega, omega, zeta).
# Companion matrices of x^2+x+1 over F_2 (order 3) and x^3+x+1 (order 7).
C3 := [[0,1],[1,1]] * One(GF(2));;
C7 := [[0,1,0],[0,0,1],[1,1,0]] * One(GF(2));;
T7 := NullMat(7,7,GF(2));;
T7{[1,2]}{[1,2]} := C3;;
T7{[3,4]}{[3,4]} := C3;;
T7{[5,6,7]}{[5,6,7]} := C7;;

Print("order of T = ", Order(T7), "  (want 21)\n");

V7 := GF(2)^7;;
pts7 := Elements(V7);;
orb7 := Orbits(Group(T7), pts7, OnRight);;
sizes7 := SortedList(List(orb7, Length));;
Print("orbit sizes  = ", sizes7, "\n");
Print("number of orbits = ", Length(orb7), "   so |B^A| = 2^", Length(orb7),
      " = ", 2^Length(orb7), "\n");

fix7 := Filtered(pts7, v -> v * T7 = v);;
Print("C_V(A) = 0 ?  ", fix7 = [Zero(V7)], "\n");

# the balanced subset used in the paper: {0} together with three 21-orbits
big := Filtered(orb7, o -> Length(o) = 21);;
Sset := Union(Concatenation([[Zero(V7)]], big{[1,2,3]}));;
Print("|{0} u three 21-orbits| = ", Length(Sset),
      "   = |V|/2 ?  ", Length(Sset) = 64, "\n");
Print("  (1 + 21 + 21 + 21 = ", 1+21+21+21, ")\n");

# how many A-stable halves are there?  the paper says twenty
halves := 0;;
for m in [0 .. 2^Length(orb7) - 1] do
  t := 0;
  for i in [1 .. Length(orb7)] do
    if QuoInt(m, 2^(i-1)) mod 2 = 1 then t := t + Length(orb7[i]); fi;
  od;
  if t = 64 then halves := halves + 1; fi;
od;
Print("A-stable subsets of V of size 64: ", halves, "   (paper: 20)\n");


#############################################################################

Print("\n=== Section 2: the machinery, checked against GAP's character theory ===\n");

# Build G = B x| V = C_2 wr V (V regular on its own 2^n points), together
# with A = <T> acting on it, all inside C_2 wr (V x| A).
BuildFamily := function(n, Tmat)
  local Vsp, pts, d, idx, transperm, Vreg, Tperm, S, K, W, topemb,
        bgen, B, Vtop, A, G, i;
  Vsp  := GF(2)^n;
  pts  := Elements(Vsp);
  d    := Length(pts);                        # = |V| = 2^n
  idx  := v -> Position(pts, v);
  transperm := w -> PermList(List(pts, v -> idx(v + w)));
  Vreg := Group(List(BasisVectors(Basis(Vsp)), transperm));
  Tperm := PermList(List(pts, v -> idx(v * Tmat)));
  S    := ClosureGroup(Vreg, Tperm);          # V x| A inside Sym(2^n)
  K    := CyclicGroup(2);
  W    := WreathProduct(K, S);                # C_2 wr (V x| A)
  bgen := List([1 .. d],
               i -> Image(Embedding(W, i), GeneratorsOfGroup(K)[1]));
  B    := Group(bgen);                        # the base, = F_2^V
  topemb := Embedding(W, d + 1);
  Vtop := Image(topemb, Vreg);
  A    := Image(topemb, Group(Tperm));
  G    := ClosureGroup(B, Vtop);              # = B x| V
  return rec(n := n, V := Vsp, pts := pts, d := d, idx := idx,
             B := B, bgen := bgen, G := G, A := A, Tmat := Tmat);
end;;

# value of a class function at a group element
ValAt := function(chi, ccl, g)
  return chi[PositionProperty(ccl, c -> g in c)];
end;;

CheckMachinery := function(F)
  local G, A, B, d, ccl, orbs, k, C, lam, cclB, i0, chi, ok, S, c, v, pred, got;
  G := F.G;; A := F.A;; B := F.B;; d := F.d;;
  Print("\n--- dim V = ", F.n, ",  |V| = ", d,
        ",  |G| = 2^", Length(Factors(Size(G))), " = ", Size(G), " ---\n");

  orbs := Orbits(Group(F.Tmat), F.pts, OnRight);;
  k := Length(orbs);;
  Print("A-orbits on V: sizes ", SortedList(List(orbs, Length)),
        ",  k = ", k, "\n");

  # (M1)  C_G(A) = B^A, elementary abelian of rank k
  C := Centralizer(G, A);;
  Print("(M1) |C_G(A)| = ", Size(C), ",  predicted 2^k = ", 2^k, "   -> ",
        Size(C) = 2^k, "\n");
  Print("     C <= B ?  ", IsSubset(B, C),
        ";   C elementary abelian ?  ", IsElementaryAbelian(C), "\n");

  # (M3)  chi_{delta_0} = Ind_B^G lambda_{delta_0}
  cclB := ConjugacyClasses(B);;
  i0 := F.idx(Zero(F.V));;
  lam := First(Irr(B),
               l -> ValAt(l, cclB, F.bgen[i0]) = -1 and
                    ForAll(Difference([1 .. d], [i0]),
                           i -> ValAt(l, cclB, F.bgen[i]) = 1));;
  chi := InducedClassFunction(lam, G);;
  Print("(M3) Ind_B^G lambda irreducible ?  ",
        ScalarProduct(chi, chi) = 1,
        ";   degree = ", chi[1], "  (want |V| = ", d, ")\n");

  # Lemma 2.10 on every A-stable subset of V
  ccl := ConjugacyClasses(G);;
  ok := true;;
  for S in Combinations([1 .. k]) do
    v := Union(orbs{S});
    c := Product(List(v, x -> F.bgen[F.idx(x)]), One(G));
    pred := d - 2 * Length(v);
    got  := ValAt(chi, ccl, c);
    if pred <> got then
      ok := false;
      Print("     MISMATCH at |supp c| = ", Length(v),
            ": GAP ", got, " vs formula ", pred, "\n");
    fi;
  od;
  Print("     chi(c) = |V| - 2|supp c| for all ", 2^k,
        " A-stable c ?  ", ok, "\n");
  return rec(C := C, chi := chi, ccl := ccl, k := k, orbs := orbs);
end;;

F2 := BuildFamily(2, C3);;                       # A = C_3 on F_4
r2 := CheckMachinery(F2);;

C7b := [[0,1,0],[0,0,1],[1,1,0]] * One(GF(2));;
F3 := BuildFamily(3, C7b);;                      # A = C_7 on F_8
r3 := CheckMachinery(F3);;


#############################################################################

Print("\n=== Section 3: |Irr_A(G)|, |N_A(G)| and |C/C'| from first principles ===\n");

CountNA := function(F, r)
  local G, A, C, ccl, reps, a, sig, inv, Cel, nonvan, cc;
  G := F.G;; A := F.A;; C := r.C;; ccl := r.ccl;;
  reps := List(ccl, Representative);;
  a := GeneratorsOfGroup(A)[1];;
  sig := PermList(List(reps, x -> PositionProperty(ccl, c -> x^a in c)));;
  inv := Filtered(Irr(G),
                  chi -> ForAll([1 .. Length(ccl)], i -> chi[i^sig] = chi[i]));;
  Cel := Elements(C);;
  nonvan := Filtered(inv, chi -> ForAll(Cel, c -> ValAt(chi, ccl, c) <> 0));;
  cc := Index(C, DerivedSubgroup(C));
  Print("\n--- dim V = ", F.n, " ---\n");
  Print("|Irr(G)|      = ", Length(Irr(G)), "\n");
  Print("|Irr_A(G)|    = ", Length(inv), "\n");
  Print("|C/C'|        = ", cc, "\n");
  Print("|N_A(G)|      = ", Length(nonvan), "\n");
  Print("(M2) |Irr_A(G)| = |C/C'| ?   ", Length(inv) = cc, "\n");
  Print("Problem 21.100 holds here ?  ", Length(nonvan) = cc,
        "   (expected: true, since this V is not balanced)\n");
  return rec(inv := Length(inv), nonvan := Length(nonvan), cc := cc);
end;;

s2 := CountNA(F2, r2);;
s3 := CountNA(F3, r3);;


#############################################################################

Print("\n=== Section 4: a balanced V that GAP can actually build ===\n");
Print("Dropping C_V(A) = 0 (which the paper assumes) allows a balanced V in\n");
Print("dimension 3.  Here GAP can exhibit a vanishing invariant character\n");
Print("directly, and we ask whether |N_A(G)| = |C/C'| still holds.\n");

# A = C_3 acting on V = F_4 (+) F_2, trivially on the second summand.
Tb := NullMat(3,3,GF(2));;
Tb{[1,2]}{[1,2]} := C3;;
Tb[3][3] := One(GF(2));;

Fb := BuildFamily(3, Tb);;
orbsb := Orbits(Group(Tb), Fb.pts, OnRight);;
Print("\norbit sizes = ", SortedList(List(orbsb, Length)),
      ";  |V|/2 = ", Fb.d / 2, "\n");
Print("C_V(A) = 0 ?  ",
      Filtered(Fb.pts, v -> v * Tb = v) = [Zero(Fb.V)], "\n");

# G is a 2-group, so move to a Pc representation for the character theory.
Cb   := Centralizer(Fb.G, Fb.A);;
ab   := GeneratorsOfGroup(Fb.A)[1];;
homb := IsomorphismPcGroup(Fb.G);;
Gp   := Image(homb);;
Cp   := Image(homb, Cb);;
cclb := ConjugacyClasses(Gp);;
repsb:= List(cclb, Representative);;
# automorphism of Gp induced by conjugation by the generator of A
alphab := g -> Image(homb, PreImagesRepresentative(homb, g) ^ ab);;
sigb := PermList(List(repsb,
          r -> PositionProperty(cclb, c -> alphab(r) in c)));;
invb := Filtered(Irr(Gp),
          chi -> ForAll([1 .. Length(cclb)], i -> chi[i^sigb] = chi[i]));;
Celb := Elements(Cp);;
nonvanb := Filtered(invb, chi -> ForAll(Celb, c -> ValAt(chi, cclb, c) <> 0));;

Print("|G| = ", Size(Fb.G), ",  |C| = ", Size(Cb),
      ",  C abelian ? ", IsAbelian(Cb), "\n");
Print("|Irr_A(G)| = ", Length(invb),
      ",  |C/C'| = ", Index(Cp, DerivedSubgroup(Cp)),
      ",  |N_A(G)| = ", Length(nonvanb), "\n");
Print("|Irr(C)| = ", Length(Irr(Cp)),
      "   -- Glauberman predicts |Irr_A(G)| = |Irr(C)| ?  ",
      Length(invb) = Length(Irr(Cp)), "\n");
Print("some invariant character vanishes somewhere on C ?  ",
      Length(nonvanb) < Length(invb), "\n");
Print("Problem 21.100 holds for this action ?  ",
      Length(nonvanb) = Index(Cp, DerivedSubgroup(Cp)), "\n\n");
Print("Reading: GAP sees genuine vanishing of invariant characters here, but\n");
Print("21.100 survives because C is nonabelian, so |C/C'| is strictly less\n");
Print("than |Irr(C)| = |Irr_A(G)| and there is slack to absorb the zeros.\n");
Print("The paper's fixed-point-free hypothesis is exactly what removes that\n");
Print("slack: it forces C elementary abelian, so |Irr_A(G)| = |C/C'| and a\n");
Print("single zero refutes the count.  That is the mechanism of Theorem 2.11.\n");

Print("\n=== done ===\n\n");


#############################################################################

Print("\n=== Section 5: the Carter subgroup statements (Section 9 of the paper) ===\n");
Print("Proposition 9.1 says K = C x A is a Carter subgroup of Gamma = G x| A.\n");
Print("Nothing above tested that, so we test it here in the small cases.\n");

CheckCarter := function(F, label)
  local G, A, Gamma, C, K, hom, Gp, Kp, ccl, Kel, nonvan, kk;
  G := F.G;; A := F.A;;
  Gamma := ClosureGroup(G, A);;
  C := Centralizer(G, A);;
  K := ClosureGroup(C, A);;
  Print("\n--- ", label, ":  |Gamma| = ", Size(Gamma),
        ",  |K| = ", Size(K), " ---\n");
  Print("K = C x A ?              ", Size(K) = Size(C) * Size(A), "\n");
  Print("K nilpotent ?            ", IsNilpotent(K), "\n");
  Print("K self-normalizing ?     ", Normalizer(Gamma, K) = K, "\n");
  Print("=> K is a Carter subgroup of Gamma ?  ",
        IsNilpotent(K) and Normalizer(Gamma, K) = K, "\n");

  # count irreducible characters of Gamma nowhere zero on K
  hom := IsomorphismPcGroup(Gamma);;
  if hom = fail then
    Print("(Gamma not solvable; skipping the character count)\n");
    return;
  fi;
  Gp := Image(hom);;
  Kp := Image(hom, K);;
  ccl := ConjugacyClasses(Gp);;
  Kel := Elements(Kp);;
  nonvan := Filtered(Irr(Gp),
              chi -> ForAll(Kel, c -> ValAt(chi, ccl, c) <> 0));;
  kk := Index(Kp, DerivedSubgroup(Kp));
  Print("|Irr(Gamma)| = ", Length(Irr(Gp)),
        ",  |K/K'| = ", kk,
        ",  # nowhere zero on K = ", Length(nonvan), "\n");
  Print("Problem 6.7 holds here ?  ", Length(nonvan) = kk, "\n");
end;;

CheckCarter(F2, "dim V = 2, A = C_3, fixed-point-free (unbalanced)");
CheckCarter(F3, "dim V = 3, A = C_7, fixed-point-free (unbalanced)");
CheckCarter(Fb, "dim V = 3, A = C_3, NOT fixed-point-free (balanced)");


#############################################################################

Print("\n=== Section 6: is there a small counterexample to Problem 21.100? ===\n");
Print("The paper proves none exists inside its own family below |G| = 2^135.\n");
Print("Here we search outside the family: every group of order at most the\n");
Print("bound below, against every cyclic A of coprime order acting on it.\n");

SearchSmall := function(bound)
  local N, G, aut, cl, a, A, ordA, C, Cgens, hom, Gp, Cp, ccl, reps,
        sig, inv, Cel, nonvan, cc, tested, bad, n, i, alpha;
  tested := 0;; bad := [];;
  for n in [2 .. bound] do
    for i in [1 .. NrSmallGroups(n)] do
      G := SmallGroup(n, i);
      aut := AutomorphismGroup(G);
      for cl in ConjugacyClasses(aut) do
        a := Representative(cl);
        ordA := Order(a);
        if ordA > 1 and GcdInt(ordA, n) = 1 then
          A := Group(a);
          Cgens := Filtered(Elements(G), g -> Image(a, g) = g);
          C := Subgroup(G, Cgens);
          hom := IsomorphismPcGroup(G);
          if hom = fail then continue; fi;
          Gp := Image(hom); Cp := Image(hom, C);
          ccl := ConjugacyClasses(Gp);
          reps := List(ccl, Representative);
          alpha := g -> Image(hom, Image(a, PreImagesRepresentative(hom, g)));
          sig := PermList(List(reps,
                   r -> PositionProperty(ccl, c -> alpha(r) in c)));
          inv := Filtered(Irr(Gp),
                   chi -> ForAll([1 .. Length(ccl)], j -> chi[j^sig] = chi[j]));
          Cel := Elements(Cp);
          nonvan := Filtered(inv,
                      chi -> ForAll(Cel, c -> ValAt(chi, ccl, c) <> 0));
          cc := Index(Cp, DerivedSubgroup(Cp));
          tested := tested + 1;
          if Length(nonvan) <> cc then
            Add(bad, [n, i, ordA, Length(nonvan), cc]);
            Print("  COUNTEREXAMPLE: SmallGroup(", n, ",", i, "), |A| = ",
                  ordA, ": |N_A(G)| = ", Length(nonvan), " vs |C/C'| = ",
                  cc, "\n");
          fi;
        fi;
      od;
    od;
  od;
  Print("\npairs (G, A) tested with |G| <= ", bound, ": ", tested, "\n");
  Print("counterexamples found: ", Length(bad), "\n");
  if Length(bad) = 0 then
    Print("Problem 21.100 holds for every coprime cyclic action on every\n");
    Print("group of order at most ", bound, ".\n");
  fi;
  return bad;
end;;

bad := SearchSmall(63);;

Print("\n=== done ===\n\n");
