import Mathlib
import Submission.Work.ResMath.resamplingAux
import Submission.Work.ResMath.resamplingAssembly
import Submission.Work.ResMath.gaussianPoisson
import Submission.Work.ResMath.gaussSumm

/-!
# Assembly: the right-hand side `P_t F_t S` acting on `u`
-/

namespace Work.ResMath

open HvdH

/-- A Gaussian times a Fourier phase times a constant is summable. -/
lemma summable_gauss_cexp (s α : ℕ) (hs : 0 < s) (hα : 0 < α) (x : ℝ) (c : ℂ) :
    Summable (fun m : ℤ => (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ)) * c) := by
  have hg : Summable (fun m : ℤ =>
      Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2)) := by
    refine (gaussSumm (Real.pi * (α : ℝ) ^ 2 / (s : ℝ) ^ 2) (by positivity) 0).congr fun m => ?_
    congr 1
    ring
  refine Summable.of_norm_bounded
    (g := fun m : ℤ => Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) * ‖c‖)
    (hg.mul_right ‖c‖) ?_
  intro m
  rw [norm_mul, norm_mul, Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re, Complex.norm_exp]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((x : ℝ) : ℂ)
      = (((2 * Real.pi * (m : ℝ) * x : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero, mul_one]

/-- The resampling matrix `S` applied to a vector, after Poisson summation. -/
theorem resS_mulVec_expand (s t α : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α)
    (u : Fin s → ℂ) (l : Fin t) :
    (HvdH.resSmat s t α).mulVec u l =
      ∑' m : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) *
          FsZ s u m := by
  have hB : 0 < (s : ℝ) ^ 2 / (α : ℝ) ^ 2 := by positivity
  have hsne : ((s : ℂ)) ≠ 0 := by simp [hs.ne']
  have hsqrt : Real.sqrt ((s : ℝ) ^ 2 / (α : ℝ) ^ 2) = (s : ℝ) / (α : ℝ) := by
    rw [show (s : ℝ) ^ 2 / (α : ℝ) ^ 2 = ((s : ℝ) / (α : ℝ)) ^ 2 by rw [div_pow]]
    exact Real.sqrt_sq (by positivity)
  set A : Fin s → ℤ → ℂ := fun i m =>
    (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
        ((((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) : ℝ) : ℂ)) with hA
  have hper (i : Fin s) : HvdH.resSmat s t α l i = (1 / (s : ℂ)) * ∑' m : ℤ, A i m := by
    have hstep : HvdH.resSmat s t α l i =
        (1 / (α : ℂ)) * ∑' q : ℤ, (Real.exp (-Real.pi * ((s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
          (((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) - (q : ℝ)) ^ 2) : ℂ) := by
      rw [HvdH.resSmat, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_tsum]
      congr 1
      refine tsum_congr fun q => ?_
      congr 1
      congr 1
      ring_nf
    rw [hstep, gaussianPoisson ((s : ℝ) ^ 2 / (α : ℝ) ^ 2)
      ((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) hB, ← mul_assoc]
    have hcoef : (1 / (α : ℂ)) * ((Real.sqrt ((s : ℝ) ^ 2 / (α : ℝ) ^ 2) : ℂ))⁻¹ = 1 / (s : ℂ) := by
      have h1 : ((↑((s : ℝ) / (α : ℝ)) : ℂ))⁻¹ = Complex.ofReal (((s : ℝ) / (α : ℝ))⁻¹) :=
        (Complex.ofReal_inv ((s : ℝ) / (α : ℝ))).symm
      have hL : (1 / (α : ℂ)) = Complex.ofReal ((α : ℝ)⁻¹) := by
        rw [one_div, ← Complex.ofReal_natCast α, ← Complex.ofReal_inv]
      have hR : (1 / (s : ℂ)) = Complex.ofReal ((s : ℝ)⁻¹) := by
        rw [one_div, ← Complex.ofReal_natCast s, ← Complex.ofReal_inv]
      have hαR : ((α : ℝ)) ≠ 0 := by exact_mod_cast hα.ne'
      have hsR : ((s : ℝ)) ≠ 0 := by exact_mod_cast hs.ne'
      rw [hsqrt, h1, hL, hR, ← Complex.ofReal_mul, Complex.ofReal_inj, inv_div]
      field_simp
    rw [hcoef]
    have hsum : (∑' m : ℤ, (Real.exp (-Real.pi * (m : ℝ) ^ 2 / ((s : ℝ) ^ 2 / (α : ℝ) ^ 2)) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
          ((((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) : ℝ) : ℂ))) = ∑' m : ℤ, A i m := by
      refine tsum_congr fun m => ?_
      have hrr : -Real.pi * (m : ℝ) ^ 2 / ((s : ℝ) ^ 2 / (α : ℝ) ^ 2)
          = -Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2 := by
        field_simp
      rw [hrr]
    rw [hsum]
  rw [Matrix.mulVec_apply, dotProduct]
  simp only [Matrix.row_apply, hper]
  have hS : ∀ i : Fin s, Summable (fun m : ℤ => A i m * u i) :=
    fun i => summable_gauss_cexp s α hs hα ((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) (u i)
  rw [show (∑ i : Fin s, (1 / (s : ℂ)) * (∑' m : ℤ, A i m) * u i)
      = (1 / (s : ℂ)) * ∑ i : Fin s, (∑' m : ℤ, A i m) * u i from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
  rw [show (∑ i : Fin s, (∑' m : ℤ, A i m) * u i) = ∑ i : Fin s, ∑' m : ℤ, A i m * u i from by
        exact Finset.sum_congr rfl fun i _ => (tsum_mul_right).symm]
  rw [← Summable.tsum_finsetSum (s := Finset.univ) (f := fun i m => A i m * u i)
        (fun i _ => hS i)]
  have hkey (m : ℤ) : (∑ i : Fin s, A i m * u i)
      = (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) *
        ((s : ℂ) * FsZ s u m) := by
    have e1 : (∑ i : Fin s, A i m * u i)
        = (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
          ∑ i : Fin s, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
            ((((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) : ℝ) : ℂ)) * u i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hA]
      ring
    have e2 : (∑ i : Fin s, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
            ((((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) : ℝ) : ℂ)) * u i)
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) *
          ∑ i : Fin s, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
            ((i : ℂ) / (s : ℂ)))) * u i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
            ((((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) : ℝ) : ℂ))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((i : ℂ) / (s : ℂ)))) from by
        rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
              ((((l : ℝ) / (t : ℝ) - (i : ℝ) / (s : ℝ)) : ℝ) : ℂ)
            = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ)) +
              (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((i : ℂ) / (s : ℂ)))) from by
          push_cast; ring]
        rw [Complex.exp_add]]
      ring
    have e3 : (∑ i : Fin s, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
            ((i : ℂ) / (s : ℂ)))) * u i) = (s : ℂ) * FsZ s u m := by
      have h1 : ∀ i : Fin s, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((i : ℂ) / (s : ℂ))))
          = Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ)) := by
        intro i
        congr 1
        push_cast
        ring
      rw [FsZ]
      simp only [h1]
      rw [show (∑ i : Fin s, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ)) * u i)
          = ∑ i : Fin s, u i * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ)) from by
        exact Finset.sum_congr rfl fun i _ => by ring]
      rw [← mul_assoc]
      rw [one_div, mul_inv_cancel₀ hsne, one_mul]
    rw [e1, e2, e3]
    ring
  rw [tsum_congr hkey]
  rw [show (1 / (s : ℂ)) * (∑' m : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) *
          ((s : ℂ) * FsZ s u m))
      = ∑' m : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) *
          FsZ s u m from by
        rw [← tsum_mul_left]
        refine tsum_congr fun m => ?_
        exact inv_mul_scale (s : ℂ) hsne _ _]

end Work.ResMath
