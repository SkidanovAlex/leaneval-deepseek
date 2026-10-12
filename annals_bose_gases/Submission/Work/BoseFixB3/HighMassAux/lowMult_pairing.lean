import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMassAux.lowMult_pairing`

The pairing identity for the low-momentum multiplier of FS `sec:3Q`:

for `φ` integrable (any `L¹` function on `ℝ³`; no box restriction is needed), `Ψ`
integrable on the box `acube ℓ`, and the momentum cut-off `p ↦ f(‖p‖/κ)` compactly
supported,

`∫_x φ(x)·(f_L(√−Δ)(θΨ))(x) = (2π)⁻³ ∫_p Re( conj(kinFT φ p) · f(‖p‖/κ) · kinFT(θΨ) p )`,

where `f_L(√−Δ)` is `Work.BoseBoxFix.lowMult` (the `p`-convention Fourier multiplier
`f(‖p‖/κ)` applied to the box-extension `θΨ = 1_{acube ℓ}·Ψ`).

## The argument

With `c p := (f(‖p‖/κ) : ℂ) · kinFT θΨ p` (`lowMultCoeff`, integrable by
`integrable_lowMultCoeff_aux` — the cut-off has compact support and `kinFT θΨ` is
bounded, indeed continuous since `θΨ ∈ L¹`), the definition of `lowMult` gives
pointwise

`lowMult fc κ ℓ Ψ x = (2π)⁻³ (∫_p c p · e^{i⟪p,x⟫})^ℜ`   (`lowMult_eq_coeff`),

so the position-space pairing is the double integral `∫_x ∫_p φ x · Re(c p e^{i⟪p,x⟫})`.
The mixed integrability (`|φ x|·|c p|` is a product of `L¹` functions, `kinFT` being
unitarity in the exponent) lets Fubini interchange the two integrals
(`fourier_pairing_re_aux`, stated for arbitrary `L¹` functions `u`, `c`), and the inner
`x`-integral is identified by the conjugate Fourier identity
`∫_x φ x e^{i⟪p,x⟫} dx = conj(kinFT φ p) ∈ ℝ` (`conj_kinFT_integral`).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB3.HighMassAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

local notation "kcE3" => Submission.BoseGases.kcE3

/-- The momentum-space coefficient of the low-momentum multiplier: the cut-off
`f(‖p‖/κ)` times the Fourier transform of the box-extension of `Ψ`.  This is the function
whose `L¹`-integrability (`integrable_lowMultCoeff_aux`) feeds the Fubini step. -/
noncomputable def lowMultCoeff (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (Ψ : kcE3 → ℝ) (p : kcE3) : ℂ :=
  ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
    Submission.BoseGases.kinFT (fun z : kcE3 =>
      (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p

/-- **The pointwise form of `lowMult`**: the low-momentum multiplier of `Ψ` at `x` is the
(real part of the) inverse Fourier transform of the coefficient `lowMultCoeff`, at the
momentum `x`.  This is the definition of `lowMult` with the real scalar `(2π)⁻³` pulled
through `Re`. -/
lemma lowMult_eq_coeff (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (Ψ : kcE3 → ℝ) (x : kcE3) :
    Work.BoseBoxFix.lowMult fc κ ℓ Ψ x
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : kcE3,
          lowMultCoeff fc κ ℓ Ψ p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re := by
  unfold Work.BoseBoxFix.lowMult lowMultCoeff
  rw [Complex.re_ofReal_mul]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  ring

/-! ## The two analytic inputs -/

/-- The unimodularity of the phase `e^{i⟪p,x⟫}`. -/
private lemma norm_exp_I_inner (p x : kcE3) :
    ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

/-- The conjugate Fourier identity: `∫_x u x e^{i⟪p,x⟫} dx = conj(kinFT u p)` for real `u`.
This is the `L¹`-identity `∫ conj(f) = conj(∫ f)` applied to the `kinFT` integrand. -/
private lemma conj_kinFT_integral {u : kcE3 → ℝ} (hu : MeasureTheory.Integrable u) (p : kcE3) :
    ∫ x : kcE3, (u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ))
      = (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z : kcE3 => (u z : ℂ)) p) := by
  rw [Submission.BoseGases.kinFT, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_neg]
  ring

/-- **The Fubini half of the pairing identity**, for arbitrary `L¹` functions: the pairing of
`u` with the inverse Fourier transform of `c` equals the `p`-integral of `Re(conj(kinFT u p)·c p)`.

Only the product integrability `|u|·|c| ∈ L¹(ℝ³×ℝ³)` is used, so the statement needs no `L²`
hypothesis. -/
private theorem fourier_pairing_re_aux {u : kcE3 → ℝ} (hu : MeasureTheory.Integrable u)
    {c : kcE3 → ℂ} (hc : MeasureTheory.Integrable c) :
    ∫ x : kcE3, u x * (∫ p : kcE3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re
      = ∫ p : kcE3,
          ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z : kcE3 => (u z : ℂ)) p)
            * c p).re := by
  -- the `p`-integrand of the LHS is integrable for each fixed `x`
  have hcx : ∀ x : kcE3,
      Integrable (fun p : kcE3 => c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) := by
    intro x
    refine hc.norm.mono' ?_ ?_
    · exact hc.1.mul (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_id.prodMk continuous_const))))).aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul, norm_exp_I_inner, mul_one]
  -- the joint integrand `(x,p) ↦ u x · Re(c p e^{i⟪p,x⟫})` is `L¹` for the product measure
  have hInt : Integrable (Function.uncurry
      (fun x p : kcE3 => u x * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re))
      (volume.prod volume) := by
    refine Integrable.mono' (hu.norm.mul_prod hc.norm) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun q : kcE3 × kcE3 => u q.1) (volume.prod volume) :=
        hu.1.comp_fst
      have h2 : Continuous (fun q : kcE3 × kcE3 =>
          Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_snd.prodMk continuous_fst))))
      have h3 : AEStronglyMeasurable (fun q : kcE3 × kcE3 =>
          (c q.2 * Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))).re) (volume.prod volume) :=
        Complex.continuous_re.comp_aestronglyMeasurable
          ((hc.1.comp_snd).mul h2.aestronglyMeasurable)
      exact h1.mul h3
    · filter_upwards with q
      change ‖u q.1 * (c q.2 * Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))).re‖ ≤
        ‖u q.1‖ * ‖c q.2‖
      calc ‖u q.1 * (c q.2 * Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))).re‖
          = |u q.1| * |(c q.2 * Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))).re| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |u q.1| * ‖c q.2 * Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
        _ = |u q.1| * ‖c q.2‖ := by rw [norm_mul, norm_exp_I_inner, mul_one]
        _ = ‖u q.1‖ * ‖c q.2‖ := by rw [Real.norm_eq_abs]
  -- turn the pairing into the iterated integral
  have hstep1 : (∫ x : kcE3, u x * (∫ p : kcE3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
      = ∫ x : kcE3, ∫ p : kcE3, u x * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re := by
    apply integral_congr_ae
    filter_upwards with x
    have hre : (∫ p : kcE3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re
        = ∫ p : kcE3, (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re := by
      simpa only [Complex.reCLM_apply] using (Complex.reCLM.integral_comp_comm (hcx x)).symm
    rw [hre, ← integral_const_mul]
  rw [hstep1, integral_integral_swap hInt]
  apply integral_congr_ae
  filter_upwards with p
  have hInt2 : Integrable (fun x : kcE3 =>
      c p * ((u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))) := by
    refine (hu.norm.const_mul ‖c p‖).mono' ?_ ?_
    · exact AEStronglyMeasurable.const_mul
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable hu.1).mul
          (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
            (continuous_inner.comp (continuous_const.prodMk continuous_id))))).aestronglyMeasurable)
        (c p)
    · filter_upwards with x
      have h1 : ‖(u x : ℂ)‖ = ‖u x‖ := RCLike.norm_ofReal (u x)
      rw [norm_mul, norm_mul, norm_exp_I_inner, mul_one, h1]
  have hstep2 : (∫ x : kcE3, u x * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
      = ∫ x : kcE3, (c p * ((u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
    apply integral_congr_ae
    filter_upwards with x
    rw [← Complex.re_ofReal_mul (u x) (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))]
    congr 1
    ring
  have hre2 : (∫ x : kcE3, c p * ((u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re
      = ∫ x : kcE3, (c p * ((u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
    simpa only [Complex.reCLM_apply] using (Complex.reCLM.integral_comp_comm hInt2).symm
  rw [hstep2, ← hre2, integral_const_mul, conj_kinFT_integral hu p]
  ring_nf

/-- **Integrability of the momentum-space coefficient.**  `kinFT θΨ` is continuous (indeed
bounded, `θΨ ∈ L¹` because `Ψ` is integrable on the box), and the cut-off factor is compactly
supported, so the product is integrable. -/
private lemma integrable_lowMultCoeff_aux {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {Ψ : kcE3 → ℝ}
    (hΨ : MeasureTheory.IntegrableOn Ψ (Submission.BoseGases.acube ℓ))
    (hcs : HasCompactSupport (fun p : kcE3 => fc.f (‖p‖ / κ))) :
    MeasureTheory.Integrable (fun p : kcE3 =>
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : kcE3 =>
          (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) := by
  have h1 : MeasureTheory.Integrable (fun z : kcE3 =>
      (Submission.BoseGases.acube ℓ).indicator Ψ z) :=
    (MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr hΨ
  have hu : MeasureTheory.Integrable (fun z : kcE3 =>
      (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) := by
    refine h1.norm.mono' ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable h1.1
    · filter_upwards with z
      exact le_of_eq (RCLike.norm_ofReal _)
  have hcont : Continuous (fun p : kcE3 =>
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : kcE3 =>
          (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) :=
    (Complex.continuous_ofReal.comp
      (fc.smooth.continuous.comp (continuous_norm.div_const κ))).mul
      (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hu)
  have hsupp : Function.support (fun p : kcE3 =>
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : kcE3 =>
          (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p)
      ⊆ Function.support (fun p : kcE3 => fc.f (‖p‖ / κ)) := by
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    intro hf
    exact hp (by rw [hf]; simp)
  exact hcont.integrable_of_hasCompactSupport (hcs.mono hsupp)

/-! ## The target -/

theorem lowMult_pairing {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hℓ : 0 < ℓ)
    {φ : Submission.BoseGases.kcE3 → ℝ} (hφ : MeasureTheory.Integrable φ)
    (hφcs : HasCompactSupport φ)
    {Ψ : Submission.BoseGases.kcE3 → ℝ}
    (hΨ : MeasureTheory.IntegrableOn Ψ (Submission.BoseGases.acube ℓ))
    (hcs : HasCompactSupport (fun p : Submission.BoseGases.kcE3 => fc.f (‖p‖ / κ))) :
    ∫ x : Submission.BoseGases.kcE3, φ x * Work.BoseBoxFix.lowMult fc κ ℓ Ψ x
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : Submission.BoseGases.kcE3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT (fun z => (φ z : ℂ)) p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT
              (fun z : Submission.BoseGases.kcE3 =>
                (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
  have hc : MeasureTheory.Integrable (lowMultCoeff fc κ ℓ Ψ) :=
    integrable_lowMultCoeff_aux (κ := κ) hΨ hcs
  calc ∫ x : Submission.BoseGases.kcE3, φ x * Work.BoseBoxFix.lowMult fc κ ℓ Ψ x
      = ∫ x : Submission.BoseGases.kcE3, φ x * (((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : Submission.BoseGases.kcE3,
            lowMultCoeff fc κ ℓ Ψ p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [lowMult_eq_coeff]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ x : Submission.BoseGases.kcE3, φ x *
          (∫ p : Submission.BoseGases.kcE3,
            lowMultCoeff fc κ ℓ Ψ p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re := by
        rw [show (∫ x : Submission.BoseGases.kcE3, φ x * (((2 * Real.pi) ^ 3)⁻¹ *
              (∫ p : Submission.BoseGases.kcE3,
                lowMultCoeff fc κ ℓ Ψ p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re))
            = ∫ x : Submission.BoseGases.kcE3, ((2 * Real.pi) ^ 3)⁻¹ * (φ x *
              (∫ p : Submission.BoseGases.kcE3,
                lowMultCoeff fc κ ℓ Ψ p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
            from integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
        rw [integral_const_mul]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : Submission.BoseGases.kcE3,
          ((starRingEnd ℂ) (Submission.BoseGases.kinFT
              (fun z : Submission.BoseGases.kcE3 => (φ z : ℂ)) p)
            * lowMultCoeff fc κ ℓ Ψ p).re := by
        rw [fourier_pairing_re_aux hφ hc]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : Submission.BoseGases.kcE3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT (fun z => (φ z : ℂ)) p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT
              (fun z : Submission.BoseGases.kcE3 =>
                (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [lowMultCoeff]
        ring_nf

end Work.BoseFixB3.HighMassAux
