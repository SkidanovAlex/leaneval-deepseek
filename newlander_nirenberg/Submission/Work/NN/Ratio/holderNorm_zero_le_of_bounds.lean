import Mathlib
import Submission.Work.CR.Flat.Holder

set_option linter.unusedVariables false

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Ratio

/-- The norm of the difference of the `0`-th iterated derivatives is the distance of the values:
the `0`-th iterated derivative is just the function itself, read as a `0`-multilinear map. -/
private lemma norm_iteratedFDerivWithin_zero_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (v : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 v Ω x - iteratedFDerivWithin ℝ 0 v Ω y‖ = ‖v x - v y‖ := by
  have h := dist_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := v) (s := Ω) (x := x)
    (g := v) (t := Ω) (y := y)
  rw [dist_eq_norm, dist_eq_norm] at h
  exact h

/-- If `v` is bounded by `A` on `Ω` and `B`-Hölder of order `α` on `Ω`, then the `C^{0,α}`-norm
of `v` on `Ω` is at most `ofReal A + ofReal B`. -/
theorem holderNorm_zero_le_of_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {Ω : Set X} {v : X → ℂ}
    (h1 : ∀ x ∈ Ω, ‖v x‖ ≤ A) (h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖v x - v y‖ ≤ B * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α v Ω ≤ ENNReal.ofReal A + ENNReal.ofReal B := by
  have hiter : Work.CR.Flat.iterDerivNorm 0 v Ω ≤ ENNReal.ofReal A := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    exact iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (h1 x hx)
  have hsemi : Work.CR.Flat.holderSeminorm 0 α v Ω ≤ ENNReal.ofReal B := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    apply ENNReal.ofReal_le_ofReal
    rw [norm_iteratedFDerivWithin_zero_sub v Ω x y]
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hd : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hpos α
    rw [div_le_iff₀ hd]
    exact h2 x hx y hy
  have hnorm : Work.CR.Flat.holderNorm 0 α v Ω =
      Work.CR.Flat.iterDerivNorm 0 v Ω + Work.CR.Flat.holderSeminorm 0 α v Ω := by
    simp [Work.CR.Flat.holderNorm]
  rw [hnorm]
  exact add_le_add hiter hsemi

end Work.NN.Ratio
