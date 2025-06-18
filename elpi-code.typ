#set page("a4")

#let at = [#h(5pt) \@ #h(5pt)]
#let ssquare = "⧈"

== Trocq elpi process.

Example: We have in or contexts:
- $bb(N) at square^α ~ N because N_R$
- $0_(bb(N)) at bb(N) ~ N because N_0$
- $S_(bb(N)) at bb(N) arrow bb(N) ~ S_N because N_S$

(Everything is a global reference)

We want to translate the following term:

$T_bb(N) = forall (P : N -> square), P 0_N ->
    (forall n : N, P n -> P (S_N n)) -> forall n, P n$

$T_bb(N) = Pi [P : N -> square][h_0 : P(0_N)]
    [h_S : Pi (n : N)(h_r : P(n)), P (S_N n)][n : N] P(n)$


First step: We want to infer $T_bb(N) at square^(0,1) ~ ? because ?$

Then we init the constraint graph `cstr.init` i.e.
- We initialize an empty constraint graph `G`
- We add a blocking constraint `c.graph G`
  - Keeps track of the current «global» graph
  - Unlocked only when call `c.reduce-graph`
- We add a blocking constraint `c.vars []`

Then we make an annotated goal `AG` where we replace every occurence of `Type` to `PType m n` with fresh variables `m` and `n`.

All the `m` and `n` values created that way are `univ-link`ed to an unknown variable.

Then, from the annotated goal `AG` and the objective type `T` we translate into a new goal `G'` with witness `GR`.
We infer using the rules of Trocq calculus defined in the paper.

=== Execution flow

- `solve InitialGoal NewGoals`
- `translate-goal DB Ty G α G' GR'`
- `param AG T G' GR`
- `cstr.reduce-graph`

== Trocq DB

The following predicates «output» the corresponding rocq constant
- `trocq.db.ptype`
- `trocq.db.pprop`
- `trocq.db.weaken`
- `trocq.db.paths`
- `trocq.db.sym-rel`

== Constraint graph

A constraint graph is represented as a directed graph with two kinds of nodes:
- Values of $cal(A)$ (i.e. $(0,1)$, $(4,4)$, …)
- Constraint nodes with a constraint type ($Π$, $arrow$, $square$, $<=$)
- Gref-constraints nodes, that carries the following data:
  - A GRef GR
  - A Rocq type T
  - A term Tm'
  - A GRef GRR
  Which describes a trocq judgment $"GR" at "T" ~ "Tm'" because "GRR"$



`empty G`: Makes an empty graph `G`

`add-dep-pi ID IDA IDB G G'`: Adds a π-node between the classes `ID` `IDA` `IDB` in graph `G`, gives graph `G'`

`add-dep-arrow ID IDA IDB G G'`: Same for arrow nodes

`add-dep-type ID IDB G G'`: Same for type node

`add-dep-gref ID GR T Tm' GRR IDs`: Adds a gref node (`GR`,`T`,`Tm'`,`GRR`) from node `ID` to all nodes `IDs`

`add-geq X Y`: Adds a $<=$ node between the class-ids. If X or Y are param classes, we directly connect the param class node to the other node (either higher or lower)


`minimal-class ID G Class`: compute the minimal possible constant class `Class` for a variable class `ID` in the constraint graph `G` i.e. the least upper bound of all the lower constant classes

`instantiate ID C G G'`: Remplace la variable `ID` par la classe constante `C`, et simplifie le graphe pour résoudre les contraintes entre constantes.

== Trocq rules, remastered

==== TrocqPi
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,

  [suffix $N$ `"'"` $N'$],
  [suffix $N$ `"R"` $N_R$],
  $D_Pi(M_1,M_2) = ((M_(1A),M_(2A)),(M_(1B),M_(2B)))$,
  $floor.l Δ floor.r tack_R square #h(2em) (= "TyA")$,
  $Δ tack_t A at square^(M_(1A),M_(2A)) ~ A' because A_R$,
  $Δ :: N at A ~ N' tack_t B[N] at square^(M_(1B),M_(2B)) ~ B'[N] because B_R N N'$,
  table.hline(),
  $Δ tack_t Pi_(N : A) B[N] at square^(M_1,M_2) ~ Pi_(N' : A') B'[N'] because
  p_Pi^(M_1,M_2) A A' A_R (λ N:A, B[N]) …$,$ … (λ N' : A', B'[N'])
  (λ N : A, λ N' : A', λ N_R : ssquare^(M_(1A),M_(2A)) A A' N N', B_R N N' N_R)$
)

==== TrocqLam
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,

  $"FunTy" equiv_"unify" Pi_(\_ : T) "TF"$,
  [suffix $N$ `"'"` $N'$],
  [suffix $N$ `"R"` $N_R$],
  $Δ tack_t T at square^(0,0) ~ T' because "TR"$,
  $Δ :: N at T ~ x' because "xR" tack_t F[N] at "TF"[N] ~ F'[N'] because "FR" N N' "xR"$,
  
  table.hline(),
  $Δ tack_t λ N : T, F[N] at "FunTy" ~ λ N' : T', F'[N'] because
  λ N : T, λ N' : T', λ "NR" : (ssquare^(0,0) T T' "TR" N N'), "FR" N N' "xR"$
)


==== TrocqConv for F (argument B in param.args) + TrocqApp
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,

  $"Ty" equiv_"unify" Pi_(\_ : T_1) Pi_(\_ : T_2) … Pi_(\_ : T_n) "TF"$,
  $forall i <= n, "Xs"_i at T_i ~ "Xs'"_i because "XR"_i$,
  $"XsR" = "Xs"_1,"Xs'"_1,"XR"_1,"Xs"_2,"Xs'"_2,"XR"_2,…"Xs"_n,"Xs'"_n,"XR"_n$,
  $"TF" <=_"type" B$,
  [$"AppR" = "FR"[overline("XsR")]$ (we subst in the body of FR the variables by $overline("XsR")$)],
  $tack_t F at "FTy" ~ F' because "FR"$,
  $tack^+ F : "FTy"$,
  table.hline(),
  $Δ tack_t F overline("Xs") at B ~ F' overline("Xs'") because arrow.b.double^"TF"_B "AppR"$
)

==== TrocqSort
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,
  $((M,N),("MR","NR")) in D_square$,
  table.hline(),
  $Δ tack_t square^("MR","NR") at square^("M","N") ~ square because p_square^(M,N) "MR" "NR"$
)

==== TrocqConv + TrocqVar
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,
  $T <=_"type" T'$,
  $x at T ~ x' because "XR" in Δ$,
  table.hline(),
  $Δ tack_t x at T' ~ x' because (arrow.b.double^T_T' "XR")$
)

==== TrocqConv + TrocqConst
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,
  $tack^+ "GR" : T$,
  $T <=_"type" T'$,
  `cstr.dep-gref GR T Tm' GRR`,
  table.hline(),
  $Δ tack_t "GR" at T' ~ "Tm"' because arrow.b.double^T_T' "GRR"$
)

==== TrocqConv + TrocqConst (fresh-type)
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,
  `cstr.dep-gref GR T' Tm' GRR`,
  table.hline(),
  $Δ tack_t "GR" at T' ~ "Tm"' because "GRR"$
)

== Trocq rules with relations

=== Checks

$Δ tack_t t at R ~ t' because t_R$

means

$floor.l Δ floor.r tack t : T$

$floor.l Δ floor.r tack t' : T'$

$floor.l Δ floor.r tack R : T -> T' -> square$

$floor.l Δ floor.r tack t_R : R t t'$
=== Règles

==== TrocqSort
#table(
  columns: (1fr),
  align: (x, y) => if x == 2 {right} else {center},
  stroke: none,
  table.hline(),
  $Δ tack_t square_i @ ssquare^β_(i+1) ~ square_i because p_(square_i)^(α,β)$
)