import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.sum_FinsetCZ_card_mul_card_sub_one_eq_card_sigma
import Submission.Work.ZassenhausSuzuki.card_sigma_centralizer_eq_card_mul_numClasses

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Conjugation preserves strongly-real elements. -/
private theorem stronglyReal_conj_aux {g x : G}
    (hx : Work.ZassenhausSuzuki.IsStronglyReal x) :
    Work.ZassenhausSuzuki.IsStronglyReal (g * x * g⁻¹) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  exact ⟨g * a * g⁻¹, g * b * g⁻¹,
    by rw [conj_mul, ha, mul_one, mul_inv_cancel],
    by rw [conj_mul, hb, mul_one, mul_inv_cancel], conj_mul⟩

/-- The set of strongly-real, non-identity, non-involution elements is invariant under
conjugation: the hypothesis `hX` of
`Work.ZassenhausSuzuki.card_sigma_centralizer_eq_card_mul_numClasses` for `X` the set of
`x` that are strongly real with `x ≠ 1` and `x * x ≠ 1`. -/
private theorem conj_mem_stronglyRealSet (g x : G)
    (hx : x ∈ {x : G | Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}) :
    g * x * g⁻¹ ∈ {x : G | Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1} := by
  obtain ⟨hxsr, hx1, hx2⟩ := hx
  refine ⟨stronglyReal_conj_aux (g := g) hxsr, ?_, ?_⟩
  · intro hcon
    refine hx1 ?_
    have key : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have h5 := congrArg (fun z : G => g⁻¹ * z * g) hcon
    rw [key] at h5
    simpa using h5
  · intro hcon
    refine hx2 ?_
    have key : g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g = x * x := by group
    have h5 := congrArg (fun z : G => g⁻¹ * z * g) hcon
    rw [key] at h5
    simpa using h5

/-- **Suzuki 1962, §10 (class count / Proposition 13).**  The Bender–Suzuki family `ℱ`
(`FinsetCZ`) satisfies `Σ_{A ∈ ℱ} |A|(|A| - 1) = |G| (q - 1)`.

This is the composition of two counts:

* `Work.ZassenhausSuzuki.Odd.sum_FinsetCZ_card_mul_card_sub_one_eq_card_sigma` rewrites the
  left-hand side as `Σ_{x ∈ X} |C_G(x)|` over the set `X` of strongly-real, non-identity,
  non-involution elements (the fibres `A ∖ {1}` of `ℱ` partition `X`);
* `Work.ZassenhausSuzuki.card_sigma_centralizer_eq_card_mul_numClasses` (Burnside) evaluates
  that sum as `|G| · numClasses X`;
* `Work.ZassenhausSuzuki.numClasses_stronglyReal_general` (Suzuki Prop. 13) gives
  `numClasses X = |Q₀sub H| - 1 = q H - 1`. -/
theorem sum_card_mul_card_sub_one (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    ∑ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G), Nat.card ↥A * (Nat.card ↥A - 1)
      = Nat.card G * (Work.ZassenhausSuzuki.Odd.q H - 1) := by
  have h1 := sum_FinsetCZ_card_mul_card_sub_one_eq_card_sigma h
  have h2 := Work.ZassenhausSuzuki.card_sigma_centralizer_eq_card_mul_numClasses
    (X := {x : G | Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1})
    (fun g x hx => conj_mem_stronglyRealSet g x hx)
  have h3 := Work.ZassenhausSuzuki.numClasses_stronglyReal_general h.hsplit h.hzass h.h2
  have h4 : Nat.card G * Work.ZassenhausSuzuki.numClasses
        {x : G | Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}
      = Nat.card G * (q H - 1) := by
    rw [h3]
    simp only [q]
  exact h1.trans (h2.trans h4)

end Work.ZassenhausSuzuki.Odd
