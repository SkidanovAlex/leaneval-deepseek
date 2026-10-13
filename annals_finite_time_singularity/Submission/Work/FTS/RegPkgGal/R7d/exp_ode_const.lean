import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open MeasureTheory intervalIntegral

/-- Uniqueness for the linear ODE `G' = cs * G`: the integrating factor
`F t = G t * exp (-∫_0^t cs)` is constant on `[0,T]` because its derivative vanishes
on the open interval, whence `G 0 = F 0 = F T = G T * exp (-∫_0^T cs) = 0`. -/
theorem exp_ode_const {G cs : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hG : ∀ t ∈ Set.Ioo 0 T, HasDerivAt G (cs t * G t) t)
    (hGc : ContinuousOn G (Set.Icc 0 T)) (hcs : ContinuousOn cs (Set.Icc 0 T))
    (hzero : G T = 0) : G 0 = 0 := by
  let F : ℝ → ℝ := fun t => G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))
  -- the integrating factor has vanishing derivative on the open interval
  have hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt F 0 t := by
    intro t ht
    have hcs_at : ContinuousAt cs t := hcs.continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hcsI : IntervalIntegrable cs volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1.le (hcs.mono (Set.Icc_subset_Icc le_rfl ht.2.le))
    have hmeas : StronglyMeasurableAtFilter cs (nhds t) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hcs.mono (by intro x hx; exact ⟨hx.1.le, hx.2.le⟩)) t ht
    have hPderiv : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, cs s) (cs t) t :=
      intervalIntegral.integral_hasDerivAt_right hcsI hmeas hcs_at
    have hexp : HasDerivAt (fun u => Real.exp (-(∫ s in (0:ℝ)..u, cs s)))
        (Real.exp (-(∫ s in (0:ℝ)..t, cs s)) * (-(cs t))) t := hPderiv.neg.exp
    have hprod : HasDerivAt (fun u => G u * Real.exp (-(∫ s in (0:ℝ)..u, cs s)))
        (cs t * G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))
          + G t * (Real.exp (-(∫ s in (0:ℝ)..t, cs s)) * -(cs t))) t := (hG t ht).mul hexp
    have hz : cs t * G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))
          + G t * (Real.exp (-(∫ s in (0:ℝ)..t, cs s)) * -(cs t)) = 0 := by ring
    simpa only [F] using hprod.congr_deriv hz
  -- continuity of the integrating factor on the closed interval
  have hcontP : ContinuousOn (fun u => ∫ s in (0:ℝ)..u, cs s) (Set.Icc 0 T) := by
    have h_int : IntegrableOn cs (Set.uIcc 0 T) volume := by
      rw [Set.uIcc_of_le hT.le]
      exact hcs.integrableOn_Icc
    have h2 := intervalIntegral.continuousOn_primitive_interval (f := cs) (a := (0:ℝ)) (b := T)
      (μ := volume) h_int
    rwa [Set.uIcc_of_le hT.le] at h2
  have hFc : ContinuousOn F (Set.Icc 0 T) := by
    change ContinuousOn (fun t => G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))) (Set.Icc 0 T)
    exact hGc.mul (Real.continuous_exp.comp_continuousOn hcontP.neg)
  -- fundamental theorem of calculus: `F T = F 0`
  have hFT : F T = F 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hFc hderiv
      intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h
    linarith [h]
  have hF0 : F 0 = G 0 := by simp [F]
  have hFT0 : F T = 0 := by simp [F, hzero]
  rw [← hF0, ← hFT, hFT0]

end Work.FTS.RegPkgGal.R7d
