import Mathlib
import Submission.Work.Analysis.IWMultiplier.Basic
import Submission.Port.Aesm

/-!
# Plancherel's identity for the Ionescu–Wainger Fourier multipliers on `ℓ²(ℤ)`

The Fourier transform `fourierZ : ℓ²(ℤ) ≃ₗᵢ[ℂ] L²(ℝ/ℤ)` (`Work.Analysis.IonescuWainger`) is an
isometry, and by definition the multiplier `T_m = multiplierOf m hm` acts on the Fourier side by
multiplication by the symbol `m`:

`fourierZ (T_m F) = hm.toLp m • fourierZ F`.

Consequently `T_m` is *exactly* the operator of multiplication by `m` on `L²(ℝ/ℤ)`, so its
`ℓ²`-norm (squared) is not merely bounded by, but equal to the weighted integral

`∫⁻ ξ, ‖m ξ‖ₑ ^ 2 * ‖(fourierZ F) ξ‖ₑ ^ 2 ∂ circleMeasure`

— Plancherel's identity with the symbol weight.  This is the form in which the `ℓ²` bound for
the Ionescu–Wainger projections is used (`‖T_m‖ = ‖m‖_∞` becomes the *identity* above).

The proof has three ingredients, isolated as the helper lemmas below:

* `eLpNorm_count_eq` — the `L^p`-seminorm on `ℤ` with respect to the counting measure is the
  `ℓᵖ` series: `eLpNorm f 2 count = ofReal ((∑' n, ‖f n‖ ^ 2) ^ (1/2))` for `f ∈ ℓ²`;
* `enorm_lp_count` — its `lp`-space form `eLpNorm (⇑f) 2 count = ‖f‖ₑ` for `f : L2Z`;
* `eLpNorm_two_sq` — raising the `L²`-seminorm to the second power removes the square root:
  `(eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ`.

The last step is the a.e. pointwise identity `‖m ξ • g ξ‖ₑ = ‖m ξ‖ₑ * ‖g ξ‖ₑ` for the
`Lp`-product `hm.toLp m • fourierZ F`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

/-- The `L²`-seminorm with respect to the counting measure on `ℤ` of an `ℓ²`-sequence is the
`ℓ²`-series: for `f : ℤ → ℂ` with `Memℓp f 2`,

`eLpNorm f 2 count = ENNReal.ofReal ((∑' n, ‖f n‖ ^ 2) ^ (1/2))`.

The integral `∫⁻ n, ‖f n‖ₑ ^ 2 ∂count` is the series `∑' n, ‖f n‖ₑ ^ 2` (`lintegral_count`),
and `ENNReal.ofReal` commutes with the (summable) series and with the square root. -/
lemma eLpNorm_count_eq (f : ℤ → ℂ) (hf : Memℓp f 2) :
    eLpNorm f 2 Measure.count
      = ENNReal.ofReal ((∑' n, ‖f n‖ ^ (2 : ℝ)) ^ ((1 / 2 : ℝ))) := by
  have hsum : Summable (fun n : ℤ => ‖f n‖ ^ (2 : ℝ)) :=
    (memℓp_gen_iff (p := 2) (by norm_num)).mp hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hlin : ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2 : ℝ) ∂Measure.count
      = ENNReal.ofReal (∑' n, ‖f n‖ ^ (2 : ℝ)) := by
    rw [lintegral_count, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact tsum_congr (fun n => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)])
  rw [hlin, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

/-- The `L²`-seminorm (with respect to the counting measure) of an element of `ℓ²(ℤ)` is its
`lp`-norm: `eLpNorm (⇑f) 2 count = ‖f‖ₑ`. -/
lemma enorm_lp_count (f : L2Z) :
    eLpNorm (⇑f) 2 Measure.count = ‖f‖ₑ := by
  rw [eLpNorm_count_eq (⇑f) (lp.memℓp f), ← ofReal_norm,
    lp.norm_eq_tsum_rpow (p := 2) (by norm_num), one_div]
  simp only [ENNReal.toReal_ofNat]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]

/-- Squaring the `L²`-seminorm removes the square root: for any function `f : α → ε`,

`(eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ`. -/
lemma eLpNorm_two_sq {α ε : Type*} {m : MeasurableSpace α} [TopologicalSpace ε] [ContinuousENorm ε]
    {μ : Measure α} (f : α → ε) (hf : AEStronglyMeasurable f μ := by pw_aesm) :
    (eLpNorm f 2 μ) ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  have h := eLpNorm_enorm_rpow (hf := hf) (μ := μ) (p := 1) f (show (0 : ℝ) < 2 by norm_num)
  rw [one_mul, ENNReal.ofReal_ofNat] at h
  have hfe : AEMeasurable (fun x => ‖f x‖ₑ) μ := hf.enorm
  rw [eLpNorm_one_eq_lintegral_enorm (hf := (hfe.pow_const (2 : ℝ)).aestronglyMeasurable)] at h
  simp only [enorm_eq_self] at h
  rw [show (eLpNorm f 2 μ) ^ (2 : ℕ) = (eLpNorm f 2 μ) ^ (2 : ℝ) from
      (ENNReal.rpow_natCast _ 2).symm, ← h]
  congr 1 with x
  exact ENNReal.rpow_natCast _ 2

/-- **Plancherel for the Fourier transform on `ℤ`**, in squared form: for `f : ℓ²(ℤ)` the
`ℓ²`-seminorm (with respect to the counting measure) of `f` equals the `L²`-seminorm of
`fourierZ f` on the frequency circle.  Both sides are expressed through the `enorm`, and
`enorm_lp_count` together with the `Lp`-form of `enorm` reduces this to the isometry property
`fourierZ.norm_map`. -/
lemma norm_fourierZ_sq (f : L2Z) :
    (eLpNorm (⇑f) 2 Measure.count) ^ (2 : ℕ)
      = (eLpNorm (⇑(fourierZ f)) 2 circleMeasure) ^ (2 : ℕ) := by
  rw [enorm_lp_count f, (Lp.enorm_def (fourierZ f)).symm]
  congr 1
  rw [← ofReal_norm, ← ofReal_norm, fourierZ.norm_map f]

theorem multiplierOfPlancherel (sym : Work.Analysis.IonescuWainger.Circle → ℂ)
    (hm : MeasureTheory.MemLp sym ⊤ Work.Analysis.IonescuWainger.circleMeasure)
    (F : Work.Analysis.IonescuWainger.L2Z) :
    (MeasureTheory.eLpNorm (⇑(Work.Analysis.IonescuWainger.multiplierOf sym hm F)) 2
        MeasureTheory.Measure.count) ^ (2 : ℕ)
      = ∫⁻ ξ, ‖sym ξ‖ₑ ^ (2 : ℕ) *
          ‖(Work.Analysis.IonescuWainger.fourierZ F) ξ‖ₑ ^ (2 : ℕ)
          ∂ Work.Analysis.IonescuWainger.circleMeasure := by
  rw [norm_fourierZ_sq (multiplierOf sym hm F), fourierZ_multiplierOf sym hm F,
    eLpNorm_two_sq _ (Lp.aestronglyMeasurable _)]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (hm.toLp sym) (fourierZ F),
    hm.coeFn_toLp] with ξ h1 h2
  rw [h1, Pi.smul_apply', smul_eq_mul, enorm_mul, mul_pow, h2]

end Work.KMTPlan.A6
