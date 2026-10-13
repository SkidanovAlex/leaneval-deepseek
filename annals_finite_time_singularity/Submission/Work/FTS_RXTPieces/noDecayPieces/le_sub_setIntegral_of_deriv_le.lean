import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

open MeasureTheory Set

theorem le_sub_setIntegral_of_deriv_le {F F' G : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0 : ℝ)))
    (hmeas : MeasureTheory.AEStronglyMeasurable F' (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' x) x)
    (hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |F' x| ≤ G x)
    (hGint : MeasureTheory.IntegrableOn G (Set.Ioi 0))
    (hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] G)
    {z : ℝ} (hz : 0 < z) :
    ∀ x, z ≤ x → F z - (∫ t in Set.Ioi 0, G t) ≤ F x := by
  intro x hzx
  -- On `[z,x]` (with `z > 0`) the function `F'` is dominated by the integrable, a.e. nonnegative
  -- `G`; the fundamental theorem of calculus then writes `F z - F x` as the integral of `-F'`.
  have hsub : Set.Ioc z x ⊆ Set.Ioi (0 : ℝ) := fun y hy => lt_trans hz hy.1
  have hIntG : IntervalIntegrable G volume z x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzx]
    exact hGint.mono_set hsub
  have hIntF' : IntervalIntegrable F' volume z x := by
    refine hIntG.mono_fun' (hmeas.mono_set ?_) ?_
    · rw [uIoc_of_le hzx]; exact hsub
    · rw [uIoc_of_le hzx]
      exact ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => by
        have h := hbd y (hsub hy)
        simpa [Real.norm_eq_abs] using h)
  have hFTC : ∫ y in z..x, F' y = F x - F z := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hzx] at hy
      exact hderiv y (lt_of_lt_of_le hz hy.1)
    · exact hIntF'
  have hmono : ∫ y in z..x, -F' y ≤ ∫ y in z..x, G y := by
    apply intervalIntegral.integral_mono_on hzx hIntF'.neg hIntG
    intro y hy
    have h := hbd y (lt_of_lt_of_le hz hy.1)
    rw [abs_le] at h
    show -(F' y) ≤ G y
    linarith [h.1]
  have hmono2 : ∫ y in z..x, G y ≤ ∫ t in Set.Ioi 0, G t := by
    rw [intervalIntegral.integral_of_le hzx]
    exact setIntegral_mono_set hGint hGnn (Filter.Eventually.of_forall hsub)
  have h1 : F z - F x ≤ ∫ t in Set.Ioi 0, G t := by
    calc F z - F x = -(F x - F z) := by ring
      _ = -∫ y in z..x, F' y := by rw [← hFTC]
      _ = ∫ y in z..x, -F' y := intervalIntegral.integral_neg.symm
      _ ≤ ∫ y in z..x, G y := hmono
      _ ≤ ∫ t in Set.Ioi 0, G t := hmono2
  linarith

end Work.FTS_RXTPieces.noDecayPieces
