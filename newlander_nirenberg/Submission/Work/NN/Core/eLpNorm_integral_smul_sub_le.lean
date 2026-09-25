import Mathlib

/-
# Convolution with a probability density does not increase the `L²` norm
(Young's inequality with exponents `(p,q,r) = (1,2,2)`), vector valued.

This file proves `Work.NN.Core.eLpNorm_integral_smul_sub_le`.  The auxiliary lemmas below
are the direct generalisation, to an arbitrary normed space `E` of values, of the
`ℂ`-valued development in `Submission/Work/NN/Core/eLpNorm_convolution_le.lean`
(whose helpers `enorm_convolution_lsmul_sq_le_lintegral`, `lintegral_convolution_lsmul_eq`
and `eLpNorm_convolution_le` are stated for `f : (Fin n → ℂ) → ℂ`).

The strategy: if `ρ ≥ 0` is integrable with `∫ ρ = 1`, then for every `x`
`‖(ρ ⋆ f) x‖ ≤ ∫⁻ t, ofReal (ρ t) * ‖f (x - t)‖`, and the weighted Cauchy–Schwarz
inequality `(∫⁻ w v)² ≤ (∫⁻ w) · (∫⁻ w v²)` with `w = ofReal ∘ ρ` gives the pointwise
square bound `‖(ρ ⋆ f) x‖² ≤ ∫⁻ t, ofReal (ρ t) * ‖f (x - t)‖²`.  Integrating in `x`
and using Tonelli together with the translation invariance of Lebesgue measure yields
`∫⁻ ‖ρ ⋆ f‖² ≤ (∫⁻ ofReal ρ) · ∫⁻ ‖f‖² = ∫⁻ ‖f‖²`, whence the claim.
-/

namespace Work.NN.Core

namespace eLpNormIntegralSmulSub

open MeasureTheory ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- `x ^ (1/2) * x ^ (1/2) = x` for extended nonnegative reals. -/
lemma rpow_half_mul_self (x : ℝ≥0∞) : x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rcases eq_or_ne x ⊤ with rfl | htop
  · rw [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)]; simp
  · rw [← ENNReal.rpow_add _ _ h0 htop]; norm_num

/-- `(x ^ (1/2)) ^ 2 = x` for extended nonnegative reals (real exponent). -/
lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1/2:ℝ)) ^ (2:ℝ) = x := by
  rw [← ENNReal.rpow_mul]; norm_num

/-- `(x ^ (1/2)) ^ 2 = x` for extended nonnegative reals (natural exponent). -/
lemma rpow_half_sq_nat (x : ℝ≥0∞) : (x ^ (1/2:ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast (x ^ (1/2:ℝ)) 2]; exact rpow_half_sq x

/-- Cauchy--Schwarz inequality for the Lebesgue integral, extended-nonnegative valued:
`(∫ w · v)² ≤ (∫ w) · (∫ w · v²)`. -/
lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w v : α → ℝ≥0∞}
    (hw : AEMeasurable w μ) (hv : AEMeasurable v μ) :
    (∫⁻ x, w x * v x ∂μ) ^ 2 ≤ (∫⁻ x, w x ∂μ) * (∫⁻ x, w x * v x ^ 2 ∂μ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
      (f := fun x => w x ^ (1/2:ℝ)) (g := fun x => w x ^ (1/2:ℝ) * v x)
      (hw.pow_const _) ((hw.pow_const _).mul hv)
  have hfun : (fun x => ((fun y => w y ^ (1/2:ℝ)) * (fun y => w y ^ (1/2:ℝ) * v y)) x)
      = (fun x => w x * v x) := by
    funext x; simp only [Pi.mul_apply]; rw [← mul_assoc, rpow_half_mul_self]
  have hXfun : (fun x => (fun y => w y ^ (1/2:ℝ)) x ^ (2:ℝ)) = (fun x => w x) := by
    funext x; exact rpow_half_sq (w x)
  have hYfun : (fun x => ((fun y => w y ^ (1/2:ℝ) * v y) x) ^ (2:ℝ))
      = (fun x => w x * v x ^ 2) := by
    funext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), rpow_half_sq]
    congr 1
    exact ENNReal.rpow_natCast (v x) 2
  rw [hfun, hXfun, hYfun] at hholder
  calc (∫⁻ x, w x * v x ∂μ) ^ 2
      ≤ ((∫⁻ x, w x ∂μ) ^ (1/2:ℝ) * (∫⁻ x, w x * v x ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 := by
        gcongr
    _ = ((∫⁻ x, w x ∂μ) ^ (1/2:ℝ)) ^ 2 * ((∫⁻ x, w x * v x ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 := by
        rw [mul_pow]
    _ = (∫⁻ x, w x ∂μ) * (∫⁻ x, w x * v x ^ 2 ∂μ) := by
        rw [rpow_half_sq_nat, rpow_half_sq_nat]

/-- Pointwise `L²` bound for the convolution of a probability density `φ` with `f`: the square
of the `enorm` of `(φ ⋆ f) x` is bounded by the `φ`-weighted integral of `‖f‖²`. -/
theorem enorm_convolution_lsmul_sq_le_lintegral {n : ℕ} {φ : (Fin n → ℂ) → ℝ}
    {f : (Fin n → ℂ) → E} (hφ0 : ∀ x, 0 ≤ φ x) (hφi : Integrable φ volume)
    (hφ1 : ∫ x, φ x ∂volume = 1) (hf : AEStronglyMeasurable f volume) (x : Fin n → ℂ) :
    ‖convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2 ∂volume := by
  rw [MeasureTheory.convolution_lsmul]
  set w : (Fin n → ℂ) → ℝ≥0∞ := fun t => ENNReal.ofReal (φ t) with hwdef
  set v : (Fin n → ℂ) → ℝ≥0∞ := fun t => ‖f (x - t)‖ₑ with hvdef
  have hφae : AEMeasurable φ volume := hφi.aestronglyMeasurable.aemeasurable
  have hwae : AEMeasurable w volume := by
    rw [hwdef]; exact ENNReal.measurable_ofReal.comp_aemeasurable hφae
  have hvae : AEMeasurable v volume := by
    rw [hvdef]
    exact (hf.aemeasurable.enorm).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left volume x)
  have hw1 : ∫⁻ t, w t ∂volume = 1 := by
    rw [hwdef, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφi
      (Filter.Eventually.of_forall hφ0), hφ1]
    simp
  have hsmul : ∀ t, ‖φ t • f (x - t)‖ₑ = w t * v t := by
    intro t
    rw [hwdef, hvdef, enorm_smul, Real.enorm_eq_ofReal (hφ0 t)]
  have hI := MeasureTheory.enorm_integral_le_lintegral_enorm
    (μ := volume) (f := fun t => φ t • f (x - t))
  have hcs := lintegral_mul_sq_le (μ := volume) hwae hvae
  rw [hw1, one_mul] at hcs
  calc ‖∫ t, φ t • f (x - t) ∂volume‖ₑ ^ 2
      ≤ (∫⁻ t, ‖φ t • f (x - t)‖ₑ ∂volume) ^ 2 := by gcongr
    _ = (∫⁻ t, w t * v t ∂volume) ^ 2 := by rw [lintegral_congr hsmul]
    _ ≤ ∫⁻ t, w t * v t ^ 2 ∂volume := hcs
    _ = ∫⁻ t, ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2 ∂volume := by rw [hwdef, hvdef]

/-- The `L²` mass of the `φ`-weighted translate integral is the `L²` mass of `f`, times the
total mass of `φ`: `∫⁻ x, ∫⁻ t, φ t ‖f (x-t)‖² = (∫⁻ φ) · ∫⁻ x, ‖f x‖²`. -/
theorem lintegral_convolution_lsmul_eq {n : ℕ} {φ : (Fin n → ℂ) → ℝ} {f : (Fin n → ℂ) → E}
    (hφm : AEMeasurable φ volume) (hfm : AEMeasurable f volume) :
    (∫⁻ x, (∫⁻ t, ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2 ∂volume) ∂volume)
      = (∫⁻ t, ENNReal.ofReal (φ t) ∂volume) * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume) := by
  have hwae : AEMeasurable (fun t : Fin n → ℂ => ENNReal.ofReal (φ t)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hφm
  have hjoint : AEMeasurable (Function.uncurry
      (fun x t : Fin n → ℂ => ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2))
      (volume.prod volume) := by
    have h1 : AEMeasurable (fun z : (Fin n → ℂ) × (Fin n → ℂ) =>
        ENNReal.ofReal (φ z.2)) (volume.prod volume) :=
      hwae.comp_snd
    have h2 : AEMeasurable (fun z : (Fin n → ℂ) × (Fin n → ℂ) =>
        ‖f (z.1 - z.2)‖ₑ ^ 2) (volume.prod volume) := by
      have hsub : AEMeasurable (fun z : (Fin n → ℂ) × (Fin n → ℂ) => f (z.1 - z.2))
          (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm.pow_const 2
    exact h1.mul h2
  rw [MeasureTheory.lintegral_lintegral_swap hjoint]
  have hinner : ∀ t : Fin n → ℂ,
      (∫⁻ x, ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2 ∂volume)
        = ENNReal.ofReal (φ t) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
    intro t
    rw [MeasureTheory.lintegral_const_mul'' _ (by
      have h : AEMeasurable (fun x : Fin n → ℂ => f (x - t)) volume :=
        hfm.comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume t).quasiMeasurePreserving
      exact (h.enorm.pow_const 2))]
    congr 1
    exact MeasureTheory.lintegral_sub_right_eq_self (fun z : Fin n → ℂ => ‖f z‖ₑ ^ 2) t
  rw [lintegral_congr hinner, MeasureTheory.lintegral_mul_const'' _ hwae]

/-- Convolution with a probability density does not increase the `L²` norm
(Young's inequality with `‖φ‖_{L¹} = 1`), for values in an arbitrary normed space. -/
theorem eLpNorm_convolution_le {n : ℕ} {φ : (Fin n → ℂ) → ℝ} {f : (Fin n → ℂ) → E}
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : MeasureTheory.integral MeasureTheory.volume φ = 1)
    (hφi : MeasureTheory.Integrable φ MeasureTheory.volume)
    (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.eLpNorm (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume) 2 MeasureTheory.volume ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.volume := by
  have hφm : AEMeasurable φ volume := hφi.aestronglyMeasurable.aemeasurable
  have hlin : ∫⁻ t, ENNReal.ofReal (φ t) ∂volume = 1 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφi
      (Filter.Eventually.of_forall hφ0), hφ1]
    simp
  have hA : ∀ x, ‖convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2 ∂volume :=
    fun x => enorm_convolution_lsmul_sq_le_lintegral hφ0 hφi hφ1 hf x
  have hB : (∫⁻ x, (∫⁻ t, ENNReal.ofReal (φ t) * ‖f (x - t)‖ₑ ^ 2 ∂volume) ∂volume)
      = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
    rw [lintegral_convolution_lsmul_eq hφm hf.aemeasurable, hlin, one_mul]
  have hmono : (∫⁻ x, ‖convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ 2 ∂volume)
      ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
    rw [← hB]
    exact lintegral_mono hA
  have hFas : AEStronglyMeasurable (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      volume :=
    hφi.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hFas,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
  simpa using hmono

end eLpNormIntegralSmulSub

/-- **Young's inequality for the convolution with a probability density, vector valued.**
If `ρ ≥ 0` is integrable with `∫ ρ = 1` and `g` is a.e. measurable, then the `L²` norm of
`x ↦ ∫ t, ρ t • g (x - t)` is at most the `L²` norm of `g`. -/
theorem eLpNorm_integral_smul_sub_le {n : ℕ} {ρ : (Fin n → ℂ) → ℝ}
    {g : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ)}
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (hρ1 : ∫ t, ρ t ∂MeasureTheory.volume = 1) (hg : AEMeasurable g MeasureTheory.volume) :
    MeasureTheory.eLpNorm (fun x => ∫ t, ρ t • g (x - t) ∂MeasureTheory.volume) 2 MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm g 2 MeasureTheory.volume := by
  have hg' : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume := hg.aestronglyMeasurable
  exact eLpNormIntegralSmulSub.eLpNorm_convolution_le hρ0 hρ1 hρi hg'

end Work.NN.Core
