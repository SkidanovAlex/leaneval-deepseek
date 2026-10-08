import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.sec3_lemma2
import Submission.Work.ThreePoints.three_involutions_even
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.ThreePoints.EvenCardSource.prop2_uncond
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156–157) in the *source's own form*, i.e. with **no**
hypothesis on the `2`-rank of `F` and **no** two-transitivity hypothesis: `K ≤ F` is strongly
embedded, `p ≠ 2` is a prime, and `Q ≤ K` is a `p`-subgroup maximal among the `p`-subgroups of `K`
with at least three fixed points of `Ω = F ⧸ K`.  Then `|N_K(Q)|` is even (there is an involution
of `K` normalising `Q`).

This is the input consumed by Ch. II §4 Prop. 1(a) (p. 168) inside `F₁ = C_G(O^p(X))·P`, where
`K = F₁ ⊓ M`, `F = F₁` and `Ω` is the class `Ξ` of proper Bender groups of `F₁`.  Unlike
`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` and its `_unconditional` sibling,
which both assume `HasFourGroup F` (plus `hA`), this statement is the one the source can actually
supply in `F₁`: the `2`-rank of `F₁` is *not* known there.

Route (`REFS/peterfalvi_I_ch1_2.md` pp. 154–157; everything but §3 Prop. 1 is BrSz-free):

* §4 Lemma 1: for `D = H ⊓ H'` (`H ≠ H' ∈ Ω`), `(D,H) ∈ R_p` ⟺ `D` has a `p`-Sylow `P` with
  `|N_H(P)|` even ⟺ `P` has a `p`-Sylow normalised by some involution of `H`; uses §2 Prop. 2(b)
  (`D` transitive on `Inv(H)`) and App. I (1),(3).
* §4 Prop. 1: `R_p = ∅` iff there is a `p`-subgroup with exactly two fixed points; if `R_p = ∅`
  then `F` is **two-transitive** on `Ω` (proof: take `P` a `p`-Sylow of a two-point stabiliser; if
  `|Ω_P| ≥ 3` then §4 Lemma 2 forces `R_p ≠ ∅`; otherwise App. II (4) gives 2-transitivity).  This
  is how 2-transitivity is obtained without any `2`-rank hypothesis.
* §4 Lemma 2: if `P` is maximal among the `p`-subgroups of `F` with `≥ 3` fixed points and contains
  a `p`-Sylow of an element of `𝒟`, then `P` is a `p`-Sylow of `H ⊓ H'` for all distinct
  `H,H' ∈ Ω_P` and `(H ⊓ H',H) ∈ R_p`; uses §3 Prop. 1 and §3 Lemma 1.
* §4 Prop. 2: *Case 1* (`R_p = ∅`): `F` is 2-transitive by §4 Prop. 1, so `Q` is maximal among the
  `p`-subgroups of `F` with `≥ 3` fixed points and `N_F(Q)` is transitive on `Ω_Q` (App. II (6),
  which here only needs §4 Prop. 1's 2-transitivity); §3 Prop. 1 then gives some `H ∈ Ω_Q` with
  `|N_H(Q)|` even, and transitivity of `N_F(Q)` on `Ω_Q` transfers this to the given `K`.
  *Case 2* (`R_p ≠ ∅`): §3 Lemma 1 + §4 Lemma 2 directly.
* §3 Prop. 1 in Case 2 needs the involutions `t₁,t₂,t` of Ch. I §3 Lemma 3 and the fact that
  `t₁t₂t` has even order; that is `Work.ThreePoints.three_involutions_even`, proved (BrSz-free at
  the point of use).

Reusable pieces already in the tree: `Work.ThreePoints.sec3_lemma1`, `sec3_lemma3` and
`app2_6_general` (BrSz-free) in `Submission/Work/ThreePoints/even_card_normalizer_of_maximal_p_subgroup.lean`,
and `Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf`. -/
theorem even_card_normalizer_of_maximal_p_subgroup_source {F : Type} [Group F] [Finite F]
    {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  -- `Work.ThreePoints.EvenCardSource.prop2_uncond` is the source's Ch. I §4 Prop. 2
  -- (pp. 156–157) in exactly the present generality — no hypothesis on the `2`-rank of `F`, no
  -- two-transitivity hypothesis — with the Brauer–Suzuki hypothesis eliminated: its Ch. I §3
  -- Prop. 1 input (`sec3_prop1_exists_uncond`) uses, for the `2`-rank-`1` case of the source's
  -- p. 154 argument, only `Work.ThreePoints.three_involutions_even`, which is the
  -- Brauer–Suzuki-free form of "`M/O_{2'}(M)` has a unique involution" used at that point.
  -- `Q` is maximal among the `p`-subgroups of `K` with at least three fixed points
  have hmax : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3,
      fun R hRp hRK hR3 hQR => le_of_eq (hQmax R hQR hRK hRp hR3)⟩
  have h : Even (Nat.card ↥(Subgroup.normalizer (Q : Set F) ⊓ K)) :=
    (Work.ThreePoints.EvenCardSource.prop2_uncond (H := K) (P := Q) hK hp hp2 hmax).2
  -- `N_K(Q)` is the intersection of `K` with `N_F(Q)`
  rw [Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hQK, inf_comm]
  exact h

end Work.ThreePoints
