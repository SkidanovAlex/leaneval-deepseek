import Mathlib
import Submission.Work.TMC7Core.Fourier.ldt_setup

/-!
# TMC7Core: auxiliary lemmas for the `L²` tail bound

Bridges between `fourierCoeffOn` on `(0,1]` and Fourier coefficients on the additive circle
`AddCircle 1`, plus the elementary translation identity for Fourier coefficients.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Fourier

/-- `AddCircle.liftIoc 1 0 f` agrees with `Function.Periodic.lift` for a `1`-periodic `f`. -/
theorem liftIoc_eq_lift (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    AddCircle.liftIoc (1 : ℝ) 0 f = hf.lift := by
  funext t
  obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ioc t
  rw [AddCircle.liftIoc_zero_coe_apply hx, Function.Periodic.lift_coe]

/-- A `1`-periodic `L²(0,1]` function gives an `L²` function on the circle. -/
theorem memLp_lift (f : ℝ → ℂ) (hf : Function.Periodic f 1)
    (hf2 : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp hf.lift 2 (AddCircle.haarAddCircle) := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have h2 : MemLp f 2 (volume.restrict (Ioc 0 (0 + 1))) := by simpa using hf2
  have h1 : MemLp (AddCircle.liftIoc (1 : ℝ) 0 f) 2 (AddCircle.haarAddCircle) :=
    (h2.memLp_liftIoc (t := 0)).haarAddCircle
  rwa [liftIoc_eq_lift f hf] at h1

/-- `fourierCoeffOn` on `(0,1]` as an integral against `e^{-2πimx}`. -/
theorem fourierCoeffOn_eq_integral_exp (f : ℝ → ℂ) (m : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f m
      = ∫ x in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)) * f x := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  beta_reduce
  rw [fourier_coe_apply, smul_eq_mul]
  congr 1
  push_cast
  ring_nf

/-- The Fourier coefficient on the circle of a `1`-periodic function, as an integral. -/
theorem fourierCoeff_lift_eq_integral_exp (f : ℝ → ℂ) (hf : Function.Periodic f 1) (m : ℤ) :
    fourierCoeff hf.lift m
      = ∫ x in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)) * f x := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [fourierCoeff_eq_intervalIntegral (f := hf.lift) (n := m) (a := 0)]
  simp only [zero_add, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  beta_reduce
  rw [Function.Periodic.lift_coe, fourier_coe_apply, smul_eq_mul]
  congr 1
  push_cast
  ring_nf

/-- The Fourier coefficient on the circle of `hf.lift` is `fourierCoeffOn` on `(0,1]`. -/
theorem fourierCoeff_lift_eq_fourierCoeffOn (f : ℝ → ℂ) (hf : Function.Periodic f 1) (m : ℤ) :
    fourierCoeff hf.lift m = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f m :=
  (fourierCoeff_lift_eq_integral_exp f hf m).trans (fourierCoeffOn_eq_integral_exp f m).symm

/-- Translation of a function on the circle multiplies its `m`-th Fourier coefficient by
`fourier m c`. -/
theorem fourierCoeff_translate (G : AddCircle (1 : ℝ) → ℂ) (c : ℝ) (m : ℤ) :
    fourierCoeff (fun t => G (t + (c : AddCircle (1 : ℝ)))) m
      = fourier m (c : AddCircle (1 : ℝ)) * fourierCoeff G m := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have harg : ∀ (n : ℤ) (x y : AddCircle (1 : ℝ)), fourier n (x + y) = fourier n x * fourier n y := by
    intro n x y
    rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
      Circle.coe_mul]
  have hc : fourier (-m) (-(c : AddCircle (1 : ℝ))) = fourier m (c : AddCircle (1 : ℝ)) := by
    simp only [fourier_apply, neg_zsmul, smul_neg, neg_neg]
  rw [fourierCoeff, fourierCoeff,
    ← MeasureTheory.integral_add_right_eq_self (fun t : AddCircle (1 : ℝ) =>
        fourier (-m) t • G (t + (c : AddCircle (1 : ℝ)))) (-(c : AddCircle (1 : ℝ)))]
  simp only [add_assoc, neg_add_cancel, add_zero]
  trans ∫ t, (fourier m (c : AddCircle (1 : ℝ))) • (fourier (-m) t • G t)
      ∂AddCircle.haarAddCircle
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [harg, hc, mul_comm, smul_smul]
  · rw [MeasureTheory.integral_smul, smul_eq_mul]

/-- `fourierCoeff` is additive under subtraction. -/
theorem fourierCoeff_sub (f g : AddCircle (1 : ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (hg : Integrable g AddCircle.haarAddCircle)
    (m : ℤ) :
    fourierCoeff (f - g) m = fourierCoeff f m - fourierCoeff g m := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  simp only [fourierCoeff, Pi.sub_apply]
  rw [← MeasureTheory.integral_sub]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [smul_sub]
  · exact hf.fourier_smul (-m)
  · exact hg.fourier_smul (-m)

end Work.TMC7Core.Fourier

end
