import Mathlib
import Submission.Work.GM.Energy.RLocal.Bump

/-!
# The Fourier identity behind GM Lemma 11.7

`R(v) = Σ_{t ∈ W} |v|^{it}`.  GM's proof of Lemma 11.7 evaluates this exponential sum with the
help of the flat-top bump `ψ` of `Bump.lean` (which is `1` on `[0,1]`, while `W ⊆ [0,T]`):
writing `𝓕ψ` for the Fourier transform of `ψ`,

  `R(v) = Σ_{t∈W} |v|^{it} ψ(t/T) = ∫ ξ, Σ_{t∈W} |v e^{2πξ/T}|^{it} 𝓕ψ(ξ) dξ
        = ∫ ξ, R(v e^{2πξ/T}) 𝓕ψ(ξ) dξ`.

This is `Rfun_eq_integral` below.
-/

namespace Work.GM.Energy.RLocal

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Submission.GM (Rfun)

/-- The complex exponential `e(x) = exp(2πi x)`, as the coercion of `Real.fourierChar`. -/
noncomputable def efun (x : ℝ) : ℂ := ((Real.fourierChar x : Circle) : ℂ)

lemma efun_apply (x : ℝ) : efun x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  rw [efun, Real.fourierChar_apply]

lemma efun_norm (x : ℝ) : ‖efun x‖ = 1 := by
  rw [efun]; exact Circle.norm_coe _

lemma efun_continuous : Continuous efun := by
  rw [show efun = fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) from
    funext efun_apply]
  fun_prop

lemma fourierChar_smul (a : ℝ) (y : ℂ) : Real.fourierChar a • y = efun a * y := by
  rw [Circle.smul_def, smul_eq_mul, efun]

/-- `PsiBump (t/T) = 1` when `t/T ∈ [0,1]`. -/
lemma PsiBump_eq_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : PsiBump x = 1 := by
  rw [PsiBump, psiBump_eq_one hx]; norm_num

/-- Fourier inversion for the bump, in terms of `efun`. -/
theorem PsiBump_fourier_inversion' (s : ℝ) :
    PsiBump s = ∫ ξ, efun (inner ℝ ξ s) * (𝓕 PsiBump) ξ := by
  rw [PsiBump_fourier_inversion s]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only []
  rw [fourierChar_smul]

/-- For `v > 0`, `Rfun W v` only involves `(v : ℂ) ^ (I t)`. -/
lemma Rfun_pos_eq_sum (W : Finset ℝ) {v : ℝ} (hv : 0 < v) :
    Rfun W v = ∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
  unfold Submission.GM.Rfun
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [abs_of_pos hv]

/-- `(r : ℂ) ^ (I t) = exp (I (t log r))` for `r > 0`. -/
lemma ofReal_cpow_pureImag (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ((r : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
      = Complex.exp (Complex.I * ((t * Real.log r : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by simpa using hr.ne'), ← Complex.ofReal_log hr.le]
  congr 1
  push_cast
  ring

/-- For `v > 0`, `Rfun W (v * e^a) = Σ_{t∈W} e^{it(log v + a)}`. -/
lemma Rfun_mul_exp_eq_sum (W : Finset ℝ) {v : ℝ} (hv : 0 < v) (a : ℝ) :
    Rfun W (v * Real.exp a)
      = ∑ t ∈ W, Complex.exp (Complex.I * ((t * (Real.log v + a) : ℝ) : ℂ)) := by
  unfold Submission.GM.Rfun
  refine Finset.sum_congr rfl fun t ht => ?_
  have hpos : (0 : ℝ) < v * Real.exp a := mul_pos hv (Real.exp_pos a)
  rw [abs_of_pos hpos, ofReal_cpow_pureImag (v * Real.exp a) hpos t,
    Real.log_mul hv.ne' (Real.exp_ne_zero a), Real.log_exp]

/-- The product of a `cpow` term with a Fourier character collapses into one exponential. -/
lemma cpow_mul_efun {v T ξ t : ℝ} (hv : 0 < v) :
    ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ)
      = Complex.exp (Complex.I * ((t * (Real.log v + 2 * Real.pi * ξ / T) : ℝ) : ℂ)) := by
  have hvne : (v : ℂ) ≠ 0 := by simpa using hv.ne'
  rw [Complex.cpow_def_of_ne_zero hvne, ← Complex.ofReal_log hv.le, efun_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- **The Fourier identity of GM Lemma 11.7.**  For `v > 0` and `W ⊆ [0,T]`,
`R(v)` is the average of `R` along the curve `v e^{2πξ/T}` against the Fourier transform of the
flat-top bump `ψ`. -/
theorem Rfun_eq_integral (T : ℝ) (hT : 0 < T) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) T) {v : ℝ} (hv : 0 < v) :
    Rfun W v = ∫ ξ, Rfun W (v * Real.exp (2 * Real.pi * ξ / T)) * (𝓕 PsiBump) ξ := by
  have hPsi : ∀ t ∈ W, PsiBump (t / T) = 1 := by
    intro t ht
    apply PsiBump_eq_one
    obtain ⟨h1, h2⟩ := hW t ht
    exact ⟨div_nonneg h1 hT.le, (div_le_one hT).mpr h2⟩
  have hinner : ∀ ξ t : ℝ, inner ℝ ξ (t / T) = t / T * ξ := by
    intro ξ t; simp
  have hbase : ∀ t ∈ W, Integrable (fun ξ : ℝ => efun (t / T * ξ) * (𝓕 PsiBump) ξ) := by
    intro t ht
    have hcont : Continuous fun ξ : ℝ => efun (t / T * ξ) :=
      efun_continuous.comp (continuous_const.mul continuous_id)
    have haesm : AEStronglyMeasurable (fun ξ : ℝ => efun (t / T * ξ) * (𝓕 PsiBump) ξ) :=
      (hcont.mul continuous_fourier_PsiBump).aestronglyMeasurable
    refine Integrable.mono' PsiBump_fourier_integrable.norm haesm ?_
    filter_upwards with ξ
    rw [norm_mul, efun_norm, one_mul]
  have hint : ∀ t ∈ W, Integrable (fun ξ : ℝ =>
      ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * (efun (t / T * ξ) * (𝓕 PsiBump) ξ)) := by
    intro t ht
    exact (hbase t ht).const_mul _
  have hA : (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))
      = ∫ ξ, (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ))
          * (𝓕 PsiBump) ξ := by
    have h1 : (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))
        = ∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * PsiBump (t / T) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hPsi t ht, mul_one]
    have h2 : (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * PsiBump (t / T))
        = ∑ t ∈ W, ∫ ξ, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
            * (efun (t / T * ξ) * (𝓕 PsiBump) ξ) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [PsiBump_fourier_inversion' (t / T), ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only []
      rw [hinner ξ t]
    have h3 : (∑ t ∈ W, ∫ ξ, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
            * (efun (t / T * ξ) * (𝓕 PsiBump) ξ))
        = ∫ ξ, ∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
            * (efun (t / T * ξ) * (𝓕 PsiBump) ξ) :=
      (MeasureTheory.integral_finset_sum W hint).symm
    have h4 : (∫ ξ, ∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
            * (efun (t / T * ξ) * (𝓕 PsiBump) ξ))
        = ∫ ξ, (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ))
            * (𝓕 PsiBump) ξ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
            * (efun (t / T * ξ) * (𝓕 PsiBump) ξ))
          = (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ))
            * (𝓕 PsiBump) ξ
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t ht => ?_
      ring
    exact h1.trans (h2.trans (h3.trans h4))
  have hB : (∫ ξ, (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ))
        * (𝓕 PsiBump) ξ)
      = ∫ ξ, Rfun W (v * Real.exp (2 * Real.pi * ξ / T)) * (𝓕 PsiBump) ξ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ)) * (𝓕 PsiBump) ξ
        = Rfun W (v * Real.exp (2 * Real.pi * ξ / T)) * (𝓕 PsiBump) ξ
    have h1 : (∑ t ∈ W, ((v : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * efun (t / T * ξ))
        = ∑ t ∈ W, Complex.exp (Complex.I * ((t * (Real.log v + 2 * Real.pi * ξ / T) : ℝ) : ℂ)) :=
      Finset.sum_congr rfl fun t ht => cpow_mul_efun (T := T) (v := v) (ξ := ξ) hv
    have h2 : Rfun W (v * Real.exp (2 * Real.pi * ξ / T))
        = ∑ t ∈ W, Complex.exp (Complex.I * ((t * (Real.log v + 2 * Real.pi * ξ / T) : ℝ) : ℂ)) :=
      Rfun_mul_exp_eq_sum W hv (2 * Real.pi * ξ / T)
    rw [h1, h2]
  exact (Rfun_pos_eq_sum W hv).trans (hA.trans hB)

end Work.GM.Energy.RLocal
