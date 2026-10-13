/-
Copyright: work module for the Elgindi finite-time singularity project.

# The truncated slice identity `∫_a^b σ f f'' = [Φ f]_a^b - ∫_a^b Ψ f`

With `η = Work.Spaces.eta = 99/100`, `σ θ = sin(2θ)^{-η}`,

  `Φ f θ = σ θ · f θ · f' θ - cos(2θ)·sin(2θ)^{-(1+η)}·f θ²`
  `Ψ f θ = 2σ θ f θ² + (1-η²)cos(2θ)² sin(2θ)^{-(2+η)} f θ²
             + sin(2θ)^{-(2+η)}·(f' θ·sin 2θ - (1+η)cos(2θ) f θ)²`

the pointwise identity

  `σ θ · (f θ · f'' θ) = (Φ f)' θ - Ψ f θ`      (`θ ∈ (0, π/2)`)

(proved here as `sst_hasDerivAt_Phi`, from `f ∈ C²` on the open interval; the algebraic
core is `sst_sig_eq_sig1_mul_sin`, `sst_sig1_eq_sig2_mul_sin`) integrates to

  `∫_a^b σ f f'' = Φ f b - Φ f a - ∫_a^b Ψ f`      (`0 < a ≤ b < π/2`).

The interval is kept strictly inside `(0, π/2)`, so no endpoint analysis is needed: `f` is
`C²` on a neighbourhood of `[a, b]`, which makes every integrand continuous on `[a, b]` and
the fundamental theorem of calculus applies.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-! ## Elementary facts about the weight -/

/-- `sin (2θ) > 0` on the open interval `(0, π/2)`. -/
lemma sst_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- `σ = σ₁ · sin(2θ)`, i.e. `sin(2θ)^{-η} = sin(2θ)^{-(1+η)}·sin(2θ)`. -/
lemma sst_sig_eq_sig1_mul_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig θ = sig1 θ * Real.sin (2 * θ) := by
  have hs := sst_sin_two_pos hθ
  simp only [sig, sig1]
  rw [show -(Work.Spaces.eta) = -(1 + Work.Spaces.eta) + 1 by ring,
    Real.rpow_add hs, Real.rpow_one]

/-- `σ₁ = σ₂ · sin(2θ)`, i.e. `sin(2θ)^{-(1+η)} = sin(2θ)^{-(2+η)}·sin(2θ)`. -/
lemma sst_sig1_eq_sig2_mul_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig1 θ = sig2 θ * Real.sin (2 * θ) := by
  have hs := sst_sin_two_pos hθ
  simp only [sig1, sig2]
  rw [show -(1 + Work.Spaces.eta) = -(2 + Work.Spaces.eta) + 1 by ring,
    Real.rpow_add hs, Real.rpow_one]

/-! ## The derivatives of the weights -/

/-- `(σ)' = -2η cos(2θ) σ₁`. -/
lemma sst_hasDerivAt_sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt sig (-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) θ := by
  have hs := sst_sin_two_pos hθ
  have hinner : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(Work.Spaces.eta)))
      (-(Work.Spaces.eta) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1))
      (Real.sin (2 * θ)) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hs))
  refine (houter.comp θ hinner).congr_deriv ?_
  rw [show (-(Work.Spaces.eta) - 1 : ℝ) = -(1 + Work.Spaces.eta) by ring]
  simp only [sig1]
  ring

/-- `(σ₁)' = -2(1+η) cos(2θ) σ₂`. -/
lemma sst_hasDerivAt_sig1 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt sig1 (-2 * (1 + Work.Spaces.eta) * Real.cos (2 * θ) * sig2 θ) θ := by
  have hs := sst_sin_two_pos hθ
  have hinner : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(1 + Work.Spaces.eta)))
      (-(1 + Work.Spaces.eta) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta) - 1))
      (Real.sin (2 * θ)) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hs))
  refine (houter.comp θ hinner).congr_deriv ?_
  rw [show (-(1 + Work.Spaces.eta) - 1 : ℝ) = -(2 + Work.Spaces.eta) by ring]
  simp only [sig2]
  ring

/-! ## The pointwise identity -/

/-- **The pointwise slice identity**: for `f ∈ C²` on `(0, π/2)` and `θ ∈ (0, π/2)`,
`(Φ f)' θ = σ θ · (f θ · f'' θ) + Ψ f θ`, i.e. `σ θ f θ f'' θ = (Φ f)' θ - Ψ f θ`. -/
lemma sst_hasDerivAt_Phi {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Phi f) (sliceIntegrand f θ + Psi f θ) θ := by
  have hinner : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have hcos : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-2 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  have hfd : DifferentiableOn ℝ f (Set.Ioo 0 (Real.pi / 2)) := hf.differentiableOn (by simp)
  have hf1 : HasDerivAt f (deriv f θ) θ :=
    (hfd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hdf : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hf2 : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((hdf.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hp1 : HasDerivAt (fun θ => sig θ * (f θ * deriv f θ))
      ((-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) * (f θ * deriv f θ)
        + sig θ * (deriv f θ * deriv f θ + f θ * deriv (deriv f) θ)) θ :=
    (sst_hasDerivAt_sig hθ).mul (hf1.mul hf2)
  have hp2 : HasDerivAt (fun θ => (Real.cos (2 * θ) * sig1 θ) * (f θ) ^ 2)
      (((-2 * Real.sin (2 * θ)) * sig1 θ
          + Real.cos (2 * θ) * (-2 * (1 + Work.Spaces.eta) * Real.cos (2 * θ) * sig2 θ))
        * (f θ) ^ 2
        + (Real.cos (2 * θ) * sig1 θ) * (2 * f θ ^ (2 - 1) * deriv f θ)) θ :=
    (hcos.mul (sst_hasDerivAt_sig1 hθ)).mul (hf1.pow 2)
  have h0 : HasDerivAt (fun θ => sig θ * (f θ * deriv f θ) - Real.cos (2 * θ) * sig1 θ * (f θ) ^ 2)
      _ θ :=
    hp1.sub hp2
  refine h0.congr_deriv ?_
  unfold sliceIntegrand Psi
  rw [sst_sig_eq_sig1_mul_sin hθ, sst_sig1_eq_sig2_mul_sin hθ]
  ring_nf

/-- The pointwise slice identity in the `deriv` form (the statement of the sibling leaf
`slice_second_identity`, obtained here as a by-product of `sst_hasDerivAt_Phi`). -/
lemma sst_slice_second_identity {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sliceIntegrand f θ = deriv (Phi f) θ - Psi f θ := by
  have h := (sst_hasDerivAt_Phi hf hθ).deriv
  linarith

/-! ## The truncated integral identity -/

theorem slice_second_trunc {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    (∫ θ in a..b, Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f θ)
      = Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f b
        - Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f a
        - ∫ θ in a..b, Work.FTS.EllipticEst.Cores.AeStep2Aux.Psi f θ := by
  -- `[a,b]` sits inside the open interval where everything is smooth
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    exact ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  have hsne : ∀ θ ∈ Set.uIcc a b, Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    have h := hsub hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2]))
  -- continuity of everything on `[a,b]`
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.uIcc a b) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcsig : ContinuousOn sig (Set.uIcc a b) :=
    hsin2.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (hsne θ hθ))
  have hcsig2 : ContinuousOn sig2 (Set.uIcc a b) :=
    hsin2.rpow_const (p := -(2 + Work.Spaces.eta)) (fun θ hθ => Or.inl (hsne θ hθ))
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hsub
  have hcdf : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn.mono hsub
  have hcddf : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) :=
    ((hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num)).continuousOn.mono hsub
  have hcslice : ContinuousOn (sliceIntegrand f) (Set.uIcc a b) :=
    hcsig.mul (hcf.mul hcddf)
  have hA : ContinuousOn (fun θ => 2 * sig θ * (f θ) ^ 2) (Set.uIcc a b) :=
    (continuousOn_const.mul hcsig).mul (hcf.pow 2)
  have hB : ContinuousOn
      (fun θ => (1 - Work.Spaces.eta ^ 2) * (Real.cos (2 * θ)) ^ 2 * sig2 θ * (f θ) ^ 2)
      (Set.uIcc a b) :=
    ((continuousOn_const.mul (hcos2.pow 2)).mul hcsig2).mul (hcf.pow 2)
  have hC : ContinuousOn (fun θ => sig2 θ * (deriv f θ * Real.sin (2 * θ)
      - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2) (Set.uIcc a b) :=
    hcsig2.mul (((hcdf.mul hsin2).sub ((continuousOn_const.mul hcos2).mul hcf)).pow 2)
  have hcPsi : ContinuousOn (Psi f) (Set.uIcc a b) := by
    change ContinuousOn (fun θ => 2 * sig θ * (f θ) ^ 2
      + (1 - Work.Spaces.eta ^ 2) * (Real.cos (2 * θ)) ^ 2 * sig2 θ * (f θ) ^ 2
      + sig2 θ * (deriv f θ * Real.sin (2 * θ) - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2)
      (Set.uIcc a b)
    exact (hA.add hB).add hC
  have hint_slice : IntervalIntegrable (sliceIntegrand f) volume a b := hcslice.intervalIntegrable
  have hint_Psi : IntervalIntegrable (Psi f) volume a b := hcPsi.intervalIntegrable
  have hint_sum : IntervalIntegrable (fun θ => sliceIntegrand f θ + Psi f θ) volume a b :=
    (hcslice.add hcPsi).intervalIntegrable
  -- the fundamental theorem of calculus
  have hderiv : ∀ θ ∈ Set.uIcc a b, HasDerivAt (Phi f) (sliceIntegrand f θ + Psi f θ) θ :=
    fun θ hθ => sst_hasDerivAt_Phi hf (hsub hθ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_sum
  rw [intervalIntegral.integral_add hint_slice hint_Psi] at hFTC
  linarith

end Work.FTS.EllipticEst.Cores.AeStep2Aux
