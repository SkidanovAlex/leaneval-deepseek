import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-- The pointwise derivative of the primitive `Φ`. -/
theorem Phi_hasDerivAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Phi f)
      ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2
            * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
  have hs := sin_two_pos hθ
  have hcd : ContDiffAt ℝ 2 f θ := hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd.differentiableAt two_ne_zero).hasDerivAt
  have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((hcd.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsinD : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h := hlin.sin
    refine h.congr_deriv ?_
    ring
  have hcosD : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-2 * Real.sin (2 * θ)) θ := by
    have h := hlin.cos
    refine h.congr_deriv ?_
    ring
  -- the rpow relation used to absorb the derivative of `cos (2·)`
  have key1 : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_comm]
    have h := Real.rpow_add hs (-(1 + Work.Spaces.eta)) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [show (-(1 + Work.Spaces.eta) + (1 : ℝ)) = -(Work.Spaces.eta) by ring] at h
    exact h.symm
  have hsig1 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      (-2 * Work.Spaces.eta * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) θ := by
    have h := hsinD.rpow_const (p := -(Work.Spaces.eta)) (Or.inl hs.ne')
    refine h.congr_deriv ?_
    rw [show (-(Work.Spaces.eta) - 1 : ℝ) = -(1 + Work.Spaces.eta) by ring]
    ring
  have hsig2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-(1 + Work.Spaces.eta)))
      (-2 * (1 + Work.Spaces.eta) * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := hsinD.rpow_const (p := -(1 + Work.Spaces.eta)) (Or.inl hs.ne')
    refine h.congr_deriv ?_
    rw [show (-(1 + Work.Spaces.eta) - 1 : ℝ) = -(2 + Work.Spaces.eta) by ring]
    ring
  have hgg : HasDerivAt
      (fun t : ℝ => (2 * Real.cos (2 * t)) * (Real.sin (2 * t)) ^ (-(1 + Work.Spaces.eta)))
      (-4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        - 4 * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := (hcosD.const_mul 2).mul hsig2
    refine h.congr_deriv ?_
    rw [show (2 * (-2 * Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        = -4 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) by ring,
      key1]
    ring
  have hA := (hdf.mul hdf').mul hsig1
  have hB := ((hdf.pow 2).const_mul (Work.Spaces.eta / 2)).mul hgg
  have hsum := hA.add hB
  have hfun : Phi f = fun t : ℝ => f t * deriv f t * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))
      + (Work.Spaces.eta / 2) * (f t) ^ 2
        * ((2 * Real.cos (2 * t)) * (Real.sin (2 * t)) ^ (-(1 + Work.Spaces.eta))) := by
    funext t
    simp only [Phi, Work.FTS.EllipticEst.thEta]
    ring
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp only [Work.FTS.EllipticEst.thEta, Pi.mul_apply, Pi.pow_apply,
    show (2:ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- The integration by parts in primitive form. -/
theorem PhiIdentity {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    Phi f b - Phi f a
      = ∫ θ in a..b, ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
          - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2
              * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
  have hmem : ∀ θ ∈ Set.uIcc a b, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1, ha], by linarith [hθ.2, hb]⟩
  have hcontf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcontdf : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hmem
  have hcontddf : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) :=
    (((hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num))).mono hmem
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontth : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ) (Set.uIcc a b) := by
    simpa only [Work.FTS.EllipticEst.thEta] using
      hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos (hmem θ hθ))))
  have hconts2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      (Set.uIcc a b) :=
    hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos (hmem θ hθ))))
  have hcontcos2 : ContinuousOn (fun θ : ℝ => (Real.cos (2 * θ)) ^ 2) (Set.uIcc a b) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2)
  have ht1 : ContinuousOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.uIcc a b) := (hcontdf.pow 2).mul hcontth
  have ht2 : ContinuousOn
      (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) (Set.uIcc a b) :=
    (hcontf.mul hcontddf).mul hcontth
  have ht3 : ContinuousOn (fun θ : ℝ => 2 * Work.Spaces.eta * (f θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) (Set.uIcc a b) :=
    (continuousOn_const.mul (hcontf.pow 2)).mul hcontth
  have ht4 : ContinuousOn (fun θ : ℝ => 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
      * (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) (Set.uIcc a b) :=
    ((continuousOn_const.mul (hcontf.pow 2)).mul hcontcos2).mul hconts2
  have hint : IntervalIntegrable (fun θ : ℝ => ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
      - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))) volume a b :=
    (((ht1.add ht2).sub ht3).sub ht4).intervalIntegrable
  have hderiv : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (Phi f) (((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2
            * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))) θ :=
    fun θ hθ => Phi_hasDerivAt hf (hmem θ hθ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  exact hFTC.symm

end Work.EllipticEst.Core.i0Aux
