#set page("a4")

#let at = [#h(5pt) \@ #h(5pt)]

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