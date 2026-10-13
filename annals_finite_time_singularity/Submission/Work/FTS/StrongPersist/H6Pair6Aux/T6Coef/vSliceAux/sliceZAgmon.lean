import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux

theorem sliceZAgmon : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ),
    0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
    Work.FTS.EllipticEst.SmoothOpen f →
    MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz →
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 f z θ) ^ 2
      ≤ 2 * ∫ s in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro α f z θ hz hθ hF hin0 hin1
  -- `sin(2θ) > 0`, so the angular weight `c := sin(2θ)^{-γ}` is a positive constant
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set c := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hsin _
  have hcne : c ≠ 0 := ne_of_gt hc
  -- the two integrability hypotheses, with the constant `c` factored out
  have hA : MeasureTheory.IntegrableOn
      (fun x => (Work.Spaces.mixed 0 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2) Work.Spaces.Iz := by
    have h0 : MeasureTheory.IntegrableOn
        (fun x => c * ((Work.Spaces.mixed 0 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2))
        Work.Spaces.Iz := by
      refine hin0.congr_fun ?_ measurableSet_Ici
      intro x hx; ring
    have h1 : MeasureTheory.IntegrableOn
        (fun x => c⁻¹ * (c * ((Work.Spaces.mixed 0 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)))
        Work.Spaces.Iz := h0.const_mul c⁻¹
    refine h1.congr_fun ?_ measurableSet_Ici
    intro x hx
    show c⁻¹ * (c * (Work.Spaces.mixed 0 1 f x θ ^ 2 * Work.Spaces.w x ^ 2))
      = Work.Spaces.mixed 0 1 f x θ ^ 2 * Work.Spaces.w x ^ 2
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  have hB : MeasureTheory.IntegrableOn
      (fun x => (x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := by
    have h0 : MeasureTheory.IntegrableOn
        (fun x => c * ((Work.Spaces.mixed 1 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2))
        Work.Spaces.Iz := by
      refine hin1.congr_fun ?_ measurableSet_Ici
      intro x hx; ring
    have h1 : MeasureTheory.IntegrableOn
        (fun x => c⁻¹ * (c * ((Work.Spaces.mixed 1 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)))
        Work.Spaces.Iz := h0.const_mul c⁻¹
    refine h1.congr_fun ?_ measurableSet_Ici
    intro x hx
    show c⁻¹ * (c * (Work.Spaces.mixed 1 1 f x θ ^ 2 * Work.Spaces.w x ^ 2))
      = (x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ * Work.Spaces.w x) ^ 2
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    rw [show x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ
        = Work.Spaces.mixed 1 1 f x θ from rfl, mul_pow]
  -- the radial Hardy bound on the single angular slice `x ↦ D_θ f (x,θ)`
  have hmain := Work.FTS.StrongPersist.N6Trans.SixAux.zslice6_hardy
    (h := fun x => Work.Spaces.mixed 0 1 f x θ)
    (h' := fun x => Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ)
    hz (fun x hx => (hF.DthIter 1).hasDerivAt_slice hθ hx)
    (((hF.DthIter 1).curry_z hθ).continuousOn)
    ((((hF.DthIter 1).pz).curry_z hθ).continuousOn) hA hB
  have hIntEq : (∫ x in Work.Spaces.Iz,
        (x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ * Work.Spaces.w x) ^ 2)
      = ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed 1 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x hx => ?_)
    rw [show x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ
        = Work.Spaces.mixed 1 1 f x θ from rfl, mul_pow]
  rw [hIntEq] at hmain
  have hsplit : (∫ s in Work.Spaces.Iz,
        (c * (Work.Spaces.mixed 1 1 f s θ) ^ 2) * (Work.Spaces.w s) ^ 2)
      = c * ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x hx => by ring)
  calc c * (Work.Spaces.mixed 0 1 f z θ) ^ 2
      ≤ c * (2 * ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hc)
    _ = 2 * ∫ s in Work.Spaces.Iz,
          (c * (Work.Spaces.mixed 1 1 f s θ) ^ 2) * (Work.Spaces.w s) ^ 2 := by
        rw [hsplit]; ring

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux
