import Mathlib
import Submission.Work.CR.Flat.Holder

/-!
# Pairing a `C^{0,α}` continuous-linear-map-valued function with a `C^{0,α}` vector field

This file proves `holderNorm_zero_clm_apply_le`: if `A : X → E →L[ℝ] ℂ` is bounded by `ε` and
`ε`-Hölder of order `α` on `Ω`, and `u : X → E` is bounded by `M` and `ε`-Hölder of order `α` on
`Ω`, then the pointwise pairing `x ↦ A x (u x)` has `C^{0,α}`-norm at most `ε * (2 * M + ε)` on
`Ω`.

The route is the pointwise product (Leibniz) estimate

`A x (u x) - A y (u y) = A x (u x - u y) + (A x - A y) (u y)`

together with the general `holderNorm 0` bound `holderNorm_zero_le_ofReal_add_of_bounds`.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `holderNorm 0 α f Ω ≤ ofReal A + ofReal B` from a sup bound `A` and an `α`-seminorm bound `B`.

(The hypotheses `0 ≤ A`, `0 ≤ B` are not needed for the inequality itself, but are recorded so
that the statement is a drop-in description of "the sup-norm is at most `A` and the
`C^{0,α}`-seminorm is at most `B`".) -/
lemma holderNorm_zero_le_ofReal_add_of_bounds {α : ℝ} {Ω : Set X} {f : X → ℂ} {A B : ℝ}
    (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (h1 : ∀ x ∈ Ω, ‖f x‖ ≤ A)
    (h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖f x - f y‖ ≤ B * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal A + ENNReal.ofReal B := by
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
  refine add_le_add ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    exact ENNReal.ofReal_le_ofReal (by simpa using h1 x hx)
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hne => ?_
    rw [show ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ from by
      simpa [dist_eq_norm] using dist_iteratedFDerivWithin_zero (𝕜 := ℝ) f Ω x f Ω y]
    by_cases h0 : x = y
    · subst h0; simp
    · have hpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h0)) α
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hpos]
      exact h2 x hx y hy

/-- **Pairing of a `C^{0,α}` continuous-linear-map-valued function with a `C^{0,α}`
vector-valued function.** -/
theorem holderNorm_zero_clm_apply_le {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (A : X → E →L[ℝ] ℂ) (u : X → E) (Ω : Set X)
    (hA0 : ∀ x ∈ Ω, ‖A x‖ ≤ ε)
    (hAα : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖A x - A y‖ ≤ ε * ‖x - y‖ ^ α)
    (hu0 : ∀ x ∈ Ω, ‖u x‖ ≤ M)
    (huα : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖u x - u y‖ ≤ ε * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α (fun x => A x (u x)) Ω
      ≤ ENNReal.ofReal (ε * (2 * M + ε)) := by
  -- Abbreviate the pairing `x ↦ A x (u x)`.
  set f : X → ℂ := fun x => A x (u x) with hf
  -- Sup bound: `‖A x (u x)‖ ≤ ε * M`.
  have h1 : ∀ x ∈ Ω, ‖f x‖ ≤ ε * M := by
    intro x hx
    show ‖A x (u x)‖ ≤ ε * M
    exact (ContinuousLinearMap.le_opNorm (A x) (u x)).trans
      (mul_le_mul (hA0 x hx) (hu0 x hx) (norm_nonneg _) hε)
  -- Hölder bound: `‖A x (u x) - A y (u y)‖ ≤ ε * (ε + M) * ‖x - y‖ ^ α`.
  have h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖f x - f y‖ ≤ ε * (ε + M) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hsplit : f x - f y = A x (u x - u y) + (A x - A y) (u y) := by
      rw [hf]; simp only [map_sub, sub_apply]; abel
    calc ‖f x - f y‖ = ‖A x (u x - u y) + (A x - A y) (u y)‖ := by rw [hsplit]
      _ ≤ ‖A x (u x - u y)‖ + ‖(A x - A y) (u y)‖ := norm_add_le _ _
      _ ≤ ‖A x‖ * ‖u x - u y‖ + ‖A x - A y‖ * ‖u y‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ε * (ε * ‖x - y‖ ^ α) + (ε * ‖x - y‖ ^ α) * M := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hA0 x hx) (huα x hx y hy) (norm_nonneg _) hε
          · exact mul_le_mul (hAα x hx y hy) (hu0 y hy) (norm_nonneg _) (mul_nonneg hε hr)
      _ = ε * (ε + M) * ‖x - y‖ ^ α := by ring
  -- Assemble: `ofReal (ε * M) + ofReal (ε * (ε + M)) = ofReal (ε * (2 * M + ε))`.
  refine (holderNorm_zero_le_ofReal_add_of_bounds (f := f) (Ω := Ω) (A := ε * M)
    (B := ε * (ε + M)) (mul_nonneg hε hM) (mul_nonneg hε (add_nonneg hε hM)) h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (mul_nonneg hε hM) (mul_nonneg hε (add_nonneg hε hM))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end Work.NN.Final
