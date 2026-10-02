import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory

theorem beltramiOf_ae_bound_and_dilatation {g : ℂ → ℂ} {U : Set ℂ} {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hdil : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      z ∈ U → ‖Work.MRMT.dzbar g z‖ ≤ k * ‖Work.MRMT.dz g z‖) :
    (∃ k' : ℝ, k' < 1 ∧ ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        z ∈ U → ‖Work.MRMT.beltramiOf g z‖ ≤ k') ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        z ∈ U → Work.MRMT.dzbar g z = Work.MRMT.beltramiOf g z * Work.MRMT.dz g z) := by
  -- On the a.e. set where the dilatation bound holds, `∂̄g = 0` wherever `∂g = 0`.
  have hzero : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      z ∈ U → (Work.MRMT.dz g z = 0 → Work.MRMT.dzbar g z = 0) := by
    filter_upwards [hdil] with z hz hU hdz
    have h := hz hU
    simp only [hdz, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  refine ⟨⟨k, hk1, ?_⟩, ?_⟩
  · filter_upwards [hdil, hzero] with z hz hz0 hU
    by_cases hd : Work.MRMT.dz g z = 0
    · rw [Work.MRMT.beltramiOf, hz0 hU hd, hd, div_zero, norm_zero]
      exact hk
    · rw [Work.MRMT.beltramiOf, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.mpr hd)]
      exact hz hU
  · filter_upwards [hzero] with z hz0 hU
    by_cases hd : Work.MRMT.dz g z = 0
    · rw [Work.MRMT.beltramiOf, hz0 hU hd, hd, div_zero, zero_mul]
    · rw [Work.MRMT.beltramiOf]
      exact (div_mul_cancel₀ _ hd).symm

end Work.MRMT.QC
