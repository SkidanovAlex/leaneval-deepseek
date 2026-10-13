import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.SinCompleteDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fourier coefficients of the odd extension: the sine-coefficient formula

For `F : ℝ → ℝ` and `L > 0`, the odd extension `sinOdd F` (see `SinCompleteDefs`) has
`n`-th Fourier coefficient on `[-L, L]` given by the sine coefficient of `F` on `[0, L]`:

`fourierCoeffOn (-L < L) (sinOdd F) n = -I / L * ∫_0^L sin (π n θ / L) F θ dθ`.

The proof splits the integral over `[-L, L]` at `0`, substitutes `x ↦ -x` on the left half
(using oddness of `sinOdd F`), and combines the two exponentials
`e^{-iπnx/L}` and `e^{iπnx/L}` into `-2i sin (π n x / L)`.
-/

open MeasureTheory Set
open scoped Interval

namespace Work.FTS.EllipticEst

/-- Pointwise difference of the `-n`-th Fourier monomials at `x` and `-x`, on the circle of
period `T`: the two exponentials combine into `-2i sin (2πnx/T)`. -/
lemma fourier_neg_sub_fourier (T : ℝ) (n : ℤ) (x : ℝ) :
    fourier (-n) ((x : ℝ) : AddCircle T) - fourier (-n) (((-x : ℝ) : AddCircle T))
      = -2 * Complex.I * (Real.sin (2 * Real.pi * n * x / T) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  set y : ℝ := 2 * Real.pi * n * x / T with hy
  have h1 : (2 * ↑Real.pi * Complex.I * ↑(-n) * ↑x / ↑T) = -((y : ℂ) * Complex.I) := by
    rw [hy]; push_cast; ring
  have h2 : (2 * ↑Real.pi * Complex.I * ↑(-n) * ↑(-x) / ↑T) = (y : ℂ) * Complex.I := by
    rw [hy]; push_cast; ring
  rw [h1, h2]
  rw [show -((y : ℂ) * Complex.I) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  simp only [Complex.ofReal_neg]
  ring

/-- The same identity for the period `2L`, with the sine written as `sin (π n x / L)`. -/
lemma fourier_neg_sub_fourier' {L : ℝ} (n : ℤ) (x : ℝ) :
    fourier (-n) ((x : ℝ) : AddCircle (2 * L)) - fourier (-n) (((-x : ℝ) : AddCircle (2 * L)))
      = -2 * Complex.I * (Real.sin (Real.pi * n * x / L) : ℂ) := by
  rw [fourier_neg_sub_fourier]
  rw [show 2 * Real.pi * n * x / (2 * L) = Real.pi * n * x / L by field_simp]

/-- The Fourier integral of the odd extension over `[-L, L]`, reduced to a sine integral over
`[0, L]`. -/
lemma integral_fourier_mul_sinOdd {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) L))) (n : ℤ) :
    ∫ x in (-L)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = (-2 * Complex.I)
          * ∫ θ in (0 : ℝ)..L, (Real.sin (Real.pi * n * θ / L) : ℂ) * (F θ : ℂ) := by
  have hInt : Integrable (sinOdd F) (volume.restrict (Ioc (-L) L)) := hmem.integrable (by norm_num)
  have hsub_L : volume.restrict (Ioc (-L) (0 : ℝ)) ≤ volume.restrict (Ioc (-L) L) :=
    Measure.restrict_mono (s := Ioc (-L) (0 : ℝ)) (s' := Ioc (-L) L)
      (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) le_rfl
  have hsub_R : volume.restrict (Ioc (0 : ℝ) L) ≤ volume.restrict (Ioc (-L) L) :=
    Measure.restrict_mono (s := Ioc (0 : ℝ) L) (s' := Ioc (-L) L)
      (fun x hx => ⟨by linarith [hx.1], hx.2⟩) le_rfl
  have hIntL : Integrable (sinOdd F) (volume.restrict (Ioc (0 : ℝ) L)) :=
    hInt.mono_measure hsub_R
  have hcont1 : Continuous (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L))) := by
    simp only [fourier_coe_apply]; fun_prop
  have hcont2 : Continuous (fun x : ℝ => fourier (-n) (((-x : ℝ)) : AddCircle (2 * L))) := by
    simp only [fourier_coe_apply]; fun_prop
  have hbd1 : ∀ (μ : Measure ℝ), ∀ᵐ x ∂μ,
      ‖fourier (-n) ((x : ℝ) : AddCircle (2 * L))‖ ≤ 1 :=
    fun μ => Filter.Eventually.of_forall (fun x => by rw [fourier_apply, Circle.norm_coe])
  have hbd2 : ∀ (μ : Measure ℝ), ∀ᵐ x ∂μ,
      ‖fourier (-n) (((-x : ℝ)) : AddCircle (2 * L))‖ ≤ 1 :=
    fun μ => Filter.Eventually.of_forall (fun x => by rw [fourier_apply, Circle.norm_coe])
  have hA : Integrable (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      (volume.restrict (Ioc (-L) L)) :=
    hInt.bdd_mul hcont1.aestronglyMeasurable (hbd1 _)
  have hAL : Integrable (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      (volume.restrict (Ioc (0 : ℝ) L)) :=
    hIntL.bdd_mul hcont1.aestronglyMeasurable (hbd1 _)
  have hArev : Integrable
      (fun x : ℝ => fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)))
      (volume.restrict (Ioc (0 : ℝ) L)) :=
    hIntL.neg.bdd_mul hcont2.aestronglyMeasurable (hbd2 _)
  have hIA1 : IntervalIntegrable
      (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x) volume (-L) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (-L : ℝ) ≤ 0)]
    exact hA.mono_measure hsub_L
  have hIA2 : IntervalIntegrable
      (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ L)]
    exact hAL
  have hIB : IntervalIntegrable
      (fun x : ℝ => fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)))
      volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ L)]
    exact hArev
  have s1 : ∫ x in (-L)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = (∫ x in (-L)..0, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
        + ∫ x in (0 : ℝ)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x :=
    (intervalIntegral.integral_add_adjacent_intervals hIA1 hIA2).symm
  have s2 : ∫ x in (-L)..(0 : ℝ), fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = ∫ x in (0 : ℝ)..L,
          fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * sinOdd F (-x) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      (a := 0) (b := L)).symm
  have s3 : ∫ x in (0 : ℝ)..L,
        fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * sinOdd F (-x)
      = ∫ x in (0 : ℝ)..L,
          fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [sinOdd_neg]
  have s4 : (∫ x in (0 : ℝ)..L, fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)))
        + ∫ x in (0 : ℝ)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = ∫ x in (0 : ℝ)..L,
          (fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x))
            + fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x) :=
    (intervalIntegral.integral_add hIB hIA2).symm
  have s5 : ∫ x in (0 : ℝ)..L,
        (fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x))
          + fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      = ∫ x in (0 : ℝ)..L,
          (-2 * Complex.I) * ((Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx0 : 0 < x := by
      rw [uIoc_of_le (by linarith : (0 : ℝ) ≤ L)] at hx
      exact hx.1
    have e1 : fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x))
          + fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
        = (fourier (-n) ((x : ℝ) : AddCircle (2 * L))
            - fourier (-n) (((-x : ℝ)) : AddCircle (2 * L))) * sinOdd F x := by
      ring
    rw [e1, fourier_neg_sub_fourier' n x, sinOdd_of_pos hx0]
    ring
  have s6 : ∫ x in (0 : ℝ)..L,
        (-2 * Complex.I) * ((Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ))
      = (-2 * Complex.I)
          * ∫ x in (0 : ℝ)..L, (Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ) :=
    intervalIntegral.integral_const_mul (-2 * Complex.I)
      (fun x : ℝ => (Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ))
  rw [s1, s2, s3, s4, s5, s6]

/-- The `n`-th Fourier coefficient on `[-L, L]` of the odd extension of `F` equals the
(complexified) sine coefficient of `F` on `[0, L]`, with factor `-I / L`. -/
theorem sinOdd_fourierCoeffOn {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MeasureTheory.MemLp (Work.FTS.EllipticEst.sinOdd F) 2
      (MeasureTheory.volume.restrict (Set.Ioc (-L) L)))
    (n : ℤ) :
    fourierCoeffOn (show (-L) < L by linarith) (Work.FTS.EllipticEst.sinOdd F) n
      = -Complex.I / L * ∫ θ in (0:ℝ)..L, (Real.sin (Real.pi * n * θ / L) : ℂ) * (F θ : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsmulC : ∀ z w : ℂ, z • w = z * w := fun z w => by rw [Algebra.smul_def]; simp
  rw [fourierCoeffOn_eq_integral]
  rw [show L - (-L) = 2 * L by ring]
  rw [Complex.real_smul]
  simp only [hsmulC]
  rw [integral_fourier_mul_sinOdd hL hmem n]
  have hcoef : ((1 / (2 * L) : ℝ) : ℂ) * (-2 * Complex.I) = -Complex.I / (L : ℂ) := by
    push_cast
    field_simp
  rw [← mul_assoc, hcoef]

end Work.FTS.EllipticEst
