import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear

namespace Work.NN.Newton.Defect

/-- If the `C^{0,α}` Hölder seminorm of `g` on `P` is at most `K`, then `g` is
pointwise Hölder continuous on `P` with constant `K`: for `z, z' ∈ P`,
`‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α`.

This is the pointwise form of the definition of `holderSeminorm` at order `0`:
the seminorm is the supremum of the quotient `‖g z - g z'‖ / ‖z - z'‖ ^ α`. -/
theorem norm_sub_le_of_holderSeminorm_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α K : ℝ} (hK : 0 ≤ K) {g : X → ℂ} {P : Set X}
    (h : Work.CR.Flat.holderSeminorm 0 α g P ≤ ENNReal.ofReal K)
    {z z' : X} (hz : z ∈ P) (hz' : z' ∈ P) :
    ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α := by
  rcases eq_or_ne z z' with rfl | hne
  · rw [sub_self, norm_zero, sub_self, norm_zero]
    exact mul_nonneg hK (Real.rpow_nonneg (le_refl 0) α)
  · -- The `z ≠ z'` term of the defining supremum is at most `ofReal K`.
    have hH : ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ 0 g P z - iteratedFDerivWithin ℝ 0 g P z'‖ / ‖z - z'‖ ^ α)
        ≤ ENNReal.ofReal K := by
      refine le_trans (Work.CR.Flat.Holder.le_hSN 0 α hz hz' hne) ?_
      simpa only [Work.CR.Flat.Holder.hSN_complex_eq] using h
    rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub] at hH
    -- `ofReal` is injective on nonnegative values, and `K ≥ 0`.
    have hle : ‖g z - g z'‖ / ‖z - z'‖ ^ α ≤ K :=
      (ENNReal.ofReal_le_ofReal_iff hK).mp hH
    have hpos : 0 < ‖z - z'‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
    exact (div_le_iff₀ hpos).mp hle

end Work.NN.Newton.Defect
