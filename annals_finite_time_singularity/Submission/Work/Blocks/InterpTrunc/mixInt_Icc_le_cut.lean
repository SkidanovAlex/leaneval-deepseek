/-
Copyright: work module for the Elgindi finite-time singularity project.

# The inner-region inequality `∫_{[δ,R]} sl (D_z∂_θ G) ≤ mixInt (ζ_k G)`

For `k` large enough that `[δ,R] ⊂ (1/k, k)`, the truncated function `ζ_k G` coincides with `G`
on the whole strip `(1/k, k) × ℝ` together with its derivative `D_z∂_θ`; hence the `mixInt`
integrand of `ζ_k G` dominates the restriction of the `mixInt` integrand of `G` to `[δ,R]`.
This is the "lower bound" half of the truncation argument.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Blocks.InterpTruncDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

theorem Iθ_subset_Ioo_strip : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem mixInt_Icc_le_cut {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    (hF : Work.FTS.EllipticEst.FourInt G) {δ R : ℝ} (hδ : 0 < δ) (hR : δ < R) {k : ℕ}
    (hk : 2 ≤ k) (hk1 : 1 / (k : ℝ) < δ) (hk2 : R < k)
    (hFc : Work.FTS.EllipticEst.FourInt (cut φ k G)) :
    (∫ z in Set.Icc δ R, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
      ≤ Work.FTS.EllipticEst.mixInt (cut φ k G) := by
  -- the two `sl`-integrands agree on `[δ,R]`
  have hsubset : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := Iθ_subset_Ioo_strip
  have hζ : ∀ z ∈ Set.Icc δ R, zeta φ k z = 1 := by
    intro z hz
    refine zeta_eq_one_of_mem hφ hk ?_ ?_
    · have : (0 : ℝ) < (k : ℝ) := by positivity
      exact le_of_lt (lt_of_lt_of_le hk1 hz.1)
    · exact le_of_lt (lt_of_le_of_lt hz.2 hk2)
  have hE : ∀ z ∈ Set.Icc δ R, zE φ k z = 0 := by
    intro z hz
    exact zE_eq_zero_of_mem hφ hk (lt_of_lt_of_le hk1 hz.1) (lt_of_le_of_lt hz.2 hk2)
  have hcongr : ∀ z ∈ Set.Icc δ R,
      sl (Work.Spaces.Dz (Work.Spaces.pth G)) z
        = sl (Work.Spaces.Dz (Work.Spaces.pth (cut φ k G))) z := by
    intro z hz
    show (Work.Spaces.w z) ^ 2 * inn (Work.Spaces.Dz (Work.Spaces.pth G)) z
      = (Work.Spaces.w z) ^ 2 * inn (Work.Spaces.Dz (Work.Spaces.pth (cut φ k G))) z
    congr 1
    rw [inn, inn]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [cut_DzPth hφ hk hG (lt_of_lt_of_le (by positivity) hz.1) (hsubset hθ), hE z hz,
      hζ z hz]
    ring
  -- the restriction is bounded by the full integral
  have h1 : (∫ z in Set.Icc δ R, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
      = ∫ z in Set.Icc δ R,
          sl (Work.Spaces.Dz (Work.Spaces.pth (cut φ k G))) z :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc hcongr
  rw [h1, mixInt_eq_int_sl]
  refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
  · exact ((fourInt_iff (cut φ k G)).mp hFc).1
  · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici]
      with z hz
    exact sl_nonneg _ z
  · exact Filter.Eventually.of_forall (fun z hz => le_trans hδ.le hz.1)

end Work.Blocks.InterpTrunc
