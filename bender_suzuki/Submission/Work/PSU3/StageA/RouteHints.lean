
-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
/-
# Route hints for the Stage A case analysis (`PSU3`, Ch. VI §1–§3)

This module contains no declarations: it is a *note* imported by the Stage A nodes so that the
route below travels with the request.  It records the Feit–Thompson-free way to run Peterfalvi's
"Réduction" (Ch. VI §3, p. 264) for cases a) and b) of Ch. VI §1, and how case c) is reached.

## The three cases of Ch. VI §1 (p. 259)

With `q = |Q0sub H| = |Inv H| + 1`:

* **a)** `Q = Q0sub H` (elementary abelian, so `|Q| = q`) and `orderOf (s * t) = 3`;
* **b)** `Q` non-abelian of order `q² = |Q0sub H|²`, `orderOf (s * t) = 5`, `W = ⊥`;
* **c)** `|Q| = q³`, `orderOf (s * t) = 3`, `W ≠ ⊥`.

Two facts are available *without* Appendix X / Feit–Thompson:

1. `Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub` (**proved**): case a) forces `W = ⊥` (inputs: the
   structure identity via `centD_eq_centralizer_s`, `Work.ThmF.L5.Kset_regular`,
   `Work.RankOneUniqueness.closure_Q_t_eq_top`, simplicity).
2. `Work.PSU3.StageA.caseC_involutions_comm` (**proved**): the involutions of `H` commute, so
   `Q0sub H = ⟨Inv H ∪ {1}⟩` is elementary abelian (`Work.ThmF.ChV12.Q0sub_elementary`).

## THE KEY LEMMA: `V = 1` from `t X t ⊆ X · Kset · t · X`

Set `D = twoPoint H t`, `V = centD H t = C_D(t)`, `Kset = Kset H t = J(D,t)` and
`Ksub = Ksub H t = ⟨Kset⟩`.  Suppose `X ≤ Q` is one of `Q`, `Q0sub H` and

  **(∗)  `t * X * t ⊆ X · Kset · t · X`  (as sets).**

Then:

* `X` is normalised by `Ksub`: for `X = Q` or `X = Q0sub H`, conjugation by `k ∈ Kset ⊆ D ≤ H`
  permutes `Inv H` (involutions of `H` stay involutions of `H`) and hence fixes `X` setwise.
* `t` inverts every element of `Ksub`: `t k t = k⁻¹` for `k ∈ Kset`
  (`Work.ThmF.mem_Kset_iff`) extends multiplicatively: for `x = k₁···kₙ` (`kᵢ ∈ Kset`),
  `t x t = (t kₙ t)···(t k₁ t) = kₙ⁻¹···k₁⁻¹ = x⁻¹`.
* `G₀ := ⟨X, Ksub, t⟩ = X·Ksub ∪ X·Ksub·t·X` **is a subgroup**: `X·Ksub` is a subgroup,
  `(X Ksub t X)(X Ksub t X) = X Ksub t (X t X) Ksub`, and `t X t ⊆ X Kset t X ⊆ X Ksub t X`;
  likewise `t G₀ t ⊆ G₀`.
* If `X = Q` then `G₀ ⊇ {Q, t}`, so `G = ⟨Q,t⟩ ⊆ G₀`
  (`Work.RankOneUniqueness.closure_Q_t_eq_top`), i.e. `G₀ = ⊤`; if `X = Q0sub H` then
  `G₀ ⊇ {Q0sub H, t}` and in case a) `Q = Q0sub H`, so again `G = ⟨Q,t⟩ ⊆ G₀`.
* `V ≤ D ≤ H`, and `(X·Ksub·t·X) ∩ H = ∅` (if `x·k·t·x' ∈ H` with `x, x' ∈ X ⊆ H`,
  `k ∈ Ksub ⊆ H`, then `t ∈ H`, contradicting `IsSplitRankOne.not_mem`); hence `V ⊆ X·Ksub`.
* `(X·Ksub) ∩ D = Ksub`: if `x·k ∈ D` with `x ∈ X ⊆ Q`, `k ∈ Ksub ⊆ D`, then
  `x = (xk)k⁻¹ ∈ D`, so `x ∈ Q ∩ D = ⊥` and `x·k = k` (`IsSplitRankOne.inf_eq`).
* So `V ⊆ Ksub`.  But every `v ∈ V` is fixed by `t` and every element of `Ksub` is inverted by
  `t`, so `v = v⁻¹`; as `V ≤ D` has odd order, `v = 1`.  Hence **`V = 1`**, contradicting
  `Work.PSU3.StageA.centD_ne_bot`, equivalently `¬ IsZassenhaus H`.

**(∗) is the whole content.**  It holds

* in case a) with `X = Q0sub H`: Ch. V §2 Lemma 5 — `tst = sts` gives, for `k ∈ Kset`,
  `t s^k t = (k s k⁻¹) · k² · t · (k s k⁻¹)` with `k s k⁻¹ ∈ Q0sub` and `k² ∈ Kset`
  (`Work.ThmF.pow_mem_Kset`); since `Inv H = {s^k | k ∈ Kset}` (`Work.ThmF.L5.Kset_regular`) and
  `x ↦ t x t` is multiplicative, (∗) follows;
* in case b) with `X = Q`: Ch. VI §2 Prop. (p. 261) — `h(x) ∈ Kset` for every `x ∈ Q#`, proved
  by the canonical-form computation with the orbit representatives `s, r, r⁻¹, r r⁻ᵏ`.

So `not_caseA` and `not_caseB` are reachable **without** `K = J(D,t)` being a subgroup; only the
*set* `Kset` and its closure `Ksub` are used.  This is exactly the point at which the book uses
Ch. V §1 Prop. 2 (App. X, i.e. Feit–Thompson).  (`Work.PSU3.StageA.caseB_centD_eq_bot` records
the same argument for case b.)

## Case c) data

`HigmanProp` gives `|Q| ∈ {q², q³}` for the Suzuki 2-group `Q` (`Work.ThmF.ChV12.corProp2` plus
the `Higman` area files `Work.Higman.typeB`, `Work.Higman.layers_card_dichotomy_alt`,
`Work.Higman.scalar_module_of_layers`), and case b) is excluded by the argument above.  In case
c) one has `W ≠ ⊥`; conversely `W ≠ ⊥` gives `Ksub = Kset` and `IsCyclic Ksub`
(`Work.PSU3.StageA.Ksub_eq_Kset_of_W_ne_bot`, proved), hence the whole of Ch. V §1 is available
(`Work.ThmF.ChV12.prop3`, `corProp2`, `Work.ThmF.ChV12.lemma5a`), which identifies `Q₀ ⋊ K` with
`F_q ⋊ F_q^*` and yields `|Q| = q³`, `orderOf (s * t) = 3`.
-/
