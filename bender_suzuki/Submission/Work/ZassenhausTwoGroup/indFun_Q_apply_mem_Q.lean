import Mathlib
import Submission.Work.ZassenhausTwoGroup.zetaStar_aux
import Submission.Work.ZassenhausTwoGroup.conj_mem_Q_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit's value formula `Ind_Q^G φ(q) = ∑_{d ∈ D} φ(q^d)` for `1 ≠ q ∈ Q`

In the split rank-one set-up `IsSplitRankOne H Q t` (so `H = Q ⋊ D` with `D = twoPoint H t`,
`Q ⊴ H` and `N_G(Q) = H`-in-the-TI-sense: `conj_mem_Q_iff`), the value at a non-identity
`q ∈ Q` of the induced function `Ind_Q^G φ` is obtained by summing `φ` over the `H`-conjugates
of `q`, each of which is `d q d⁻¹` for a unique `d ∈ D` (the `Q`-conjugation being invisible
because `ℂˣ` is abelian and `φ` is multiplicative).

The proof: an `x ∈ G` contributes to `Ind_Q^G φ (q)` only if `x q x⁻¹ ∈ Q`, and
`conj_mem_Q_iff` says that forces `x ∈ H`. Conjugating by `a * d` with `a ∈ Q`, `d ∈ D` gives
`a (d q d⁻¹) a⁻¹`, on which `φ` takes the value `φ (d q d⁻¹)`, so the sum over `H` collapses to
`|Q|` copies of the sum over `D`, and the `|Q|⁻¹` of `indFun` cancels.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- `φ : Q →* ℂˣ` composed with the coercion to `ℂ` is conjugation invariant (the target `ℂˣ`
is abelian, so the coercion to `ℂ` is multiplicative and commutes with conjugation). -/
private lemma units_coe_conj {G : Type} [Group G] {Q : Subgroup G} (φ : ↥Q →* ℂˣ) (a c : ↥Q) :
    (φ (a * c * a⁻¹) : ℂ) = (φ c : ℂ) := by
  have h : φ (a * c * a⁻¹) = φ c := by
    rw [map_mul, map_mul, map_inv, mul_comm (φ a) (φ c), mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg (fun u : ℂˣ => (u : ℂ)) h

/-- The conjugate of `q` by `qdEquiv h (a, d) = a * d` is `a * (d q d⁻¹) * a⁻¹`. -/
private lemma conjQ_qdEquiv {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (a : ↥Q) (d : ↥(twoPoint H t)) (q : ↥Q) :
    conjQ h (qdEquiv h (a, d)) q = a * conjQD h d q * a⁻¹ := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_mul, Subgroup.coe_inv, conjQD_coe, qdEquiv_coe]
  group

open Classical in
theorem indFun_Q_apply_mem_Q {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (φ : ↥Q →* ℂˣ) {q : ↥Q} (hq : q ≠ 1) :
    Work.Induction.indFun Q (fun x : ↥Q => (φ x : ℂ)) (q : G)
      = ∑ d : ↥(Submission.Blueprint.twoPoint H t),
          (φ (Work.ZassenhausTwoGroup.conjQD h d q) : ℂ) := by
  have hqG : (q : G) ≠ 1 := fun hh => hq (Subtype.ext hh)
  have hcard : (Nat.card Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [Work.Induction.indFun_apply_def]
  -- Only `x ∈ H` contributes to the defining sum: for `x ∉ H`, `x q x⁻¹ ∉ Q` with `q ≠ 1`.
  have hstep : ∀ x : G,
      (if hx : x * (q : G) * x⁻¹ ∈ Q then
        ((fun y : ↥Q => (φ y : ℂ)) ⟨x * (q : G) * x⁻¹, hx⟩) else 0)
      = (if hx : x ∈ H then
        ((fun y : ↥H => (φ (conjQ h y q) : ℂ)) ⟨x, hx⟩) else 0) := by
    intro x
    by_cases hxH : x ∈ H
    · have hxQ : x * (q : G) * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (h.normal hxH) (q : G)).mp q.2
      rw [dite_eq_left hxQ, dite_eq_left hxH]
      exact congrArg (fun y : ↥Q => (φ y : ℂ)) (Subtype.ext rfl)
    · have hxQ : x * (q : G) * x⁻¹ ∉ Q :=
        fun hc => hxH (conj_mem_Q_iff h q.2 hqG x hc)
      rw [dite_eq_right hxQ, dite_eq_right hxH]
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  rw [Work.Induction.sum_dite_mem_subgroup H (fun y : ↥H => (φ (conjQ h y q) : ℂ))]
  -- Reindex `H = Q ⋊ D` through `qdEquiv` and evaluate `φ` on `a (d q d⁻¹) a⁻¹`.
  rw [sum_H_eq h (fun y : ↥H => (φ (conjQ h y q) : ℂ))]
  have hinner : ∀ a : ↥Q,
      (∑ d : ↥(twoPoint H t), (φ (conjQ h (qdEquiv h (a, d)) q) : ℂ))
      = ∑ d : ↥(twoPoint H t), (φ (conjQD h d q) : ℂ) := by
    intro a
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [conjQ_qdEquiv]
    exact units_coe_conj φ a (conjQD h d q)
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  -- The summand is now independent of `a ∈ Q`, leaving `|Q|` copies; cancel `|Q|⁻¹`.
  have hsum : (∑ _a : ↥Q, ∑ d : ↥(twoPoint H t), (φ (conjQD h d q) : ℂ))
      = (Nat.card Q : ℂ) * ∑ d : ↥(twoPoint H t), (φ (conjQD h d q) : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Work.ZassenhausTwoGroup
