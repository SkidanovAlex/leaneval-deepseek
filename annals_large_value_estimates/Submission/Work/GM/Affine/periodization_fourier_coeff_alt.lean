import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# The Fourier coefficient of the periodization (self-contained proof)

For `f : ℝ → ℝ` continuous and vanishing off `[-R,R]`, `m > 0`, an integer `K` with `mR ≤ K`
and `n : ℤ`:

`∫ x in (0)..1, efun (-(n x)) * (∑_{j < 2K+1} f ((x + (j-K))/m)) = m * Fhat f (n m)`,

i.e. the `n`-th Fourier coefficient of the periodization `x ↦ ∑_k f ((x+k)/m)` is `m * Fhat f (n m)`.

Proof: split the finite sum out of the integral, substitute `x = m y - (j-K)` in the `j`-th term
(which turns its integrand into the common `Ψ y = efun (-(n m y)) f y` because `efun` of an
integer is `1`), tile the intervals `[(j-K)/m, (j+1-K)/m]` with
`intervalIntegral.sum_integral_adjacent_intervals`, and use that `Ψ` vanishes off
`[a 0, a (2K+1)]` by the support hypothesis.

All auxiliary lemmas here are `private` so that this module cannot clash with other files
proving the same statement.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform
set_option autoImplicit false

namespace Work.GM.Affine
noncomputable section

private lemma efun_int (z : ℤ) : efun (z : ℝ) = 1 := by
  rw [efun]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((z:ℝ) : ℂ)) = (z:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

private lemma Fhat_eq_integral (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f ξ = ∫ y : ℝ, efun (-(ξ * y)) * ((f y : ℝ) : ℂ) := by
  rw [Fhat, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.inner_apply, smul_eq_mul, efun]
  congr 1
  push_cast
  ring_nf

private lemma continuous_efun : Continuous efun := by unfold efun; fun_prop

private lemma single_term {f : ℝ → ℝ} {m : ℝ} (hm : 0 < m) (n : ℤ) (z : ℝ) :
    ∫ x in (0:ℝ)..1, efun (-((n:ℝ)*x)) * ((f ((x+z)/m) : ℝ) : ℂ)
      = (m : ℂ) * ∫ y in z/m..(z+1)/m,
          efun (-((n:ℝ) * (m*y - z))) * ((f y : ℝ) : ℂ) := by
  set H : ℝ → ℂ := fun y => efun (-((n:ℝ) * (m*y - z))) * ((f y : ℝ) : ℂ) with hH
  have hid : (fun x : ℝ => efun (-((n:ℝ)*x)) * ((f ((x+z)/m) : ℝ) : ℂ))
      = fun x : ℝ => H (x/m + z/m) := by
    funext x
    simp only [hH]
    congr 1
    · congr 1
      field_simp
      ring
    · congr 1
      congr 1
      field_simp
  rw [hid, intervalIntegral.integral_comp_div_add H (by positivity : m ≠ 0) (z/m)]
  simp only [zero_div, zero_add, Complex.real_smul]
  have harg : (1:ℝ)/m + z/m = (z+1)/m := by field_simp; ring
  rw [harg]

theorem periodization_fourier_coeff_alt {f : ℝ → ℝ} (hf : Continuous f) {m R : ℝ} (hm : 0 < m)
    (hRf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R ≤ (K : ℝ)) (n : ℤ) :
    ∫ x in (0:ℝ)..1, efun (-((n : ℝ) * x)) * ((∑ j ∈ Finset.range (2 * K + 1),
        f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ)
      = (m : ℂ) * Fhat f ((n : ℝ) * m) := by
  set Ψ : ℝ → ℂ := fun y => efun (-(((n : ℝ) * m) * y)) * ((f y : ℝ) : ℂ) with hΨ
  set a : ℕ → ℝ := fun j => ((j : ℝ) - (K : ℝ)) / m with ha
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    exact (continuous_efun.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp hf)
  have hsplit : (∫ x in (0:ℝ)..1, efun (-((n : ℝ) * x)) * ((∑ j ∈ Finset.range (2 * K + 1),
        f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ))
      = ∑ j ∈ Finset.range (2 * K + 1), ∫ x in (0:ℝ)..1,
          efun (-((n : ℝ) * x)) * ((f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ) := by
    have hrw : (fun x : ℝ => efun (-((n : ℝ) * x)) * ((∑ j ∈ Finset.range (2 * K + 1),
        f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ))
        = fun x : ℝ => ∑ j ∈ Finset.range (2 * K + 1),
            efun (-((n : ℝ) * x)) * ((f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ) := by
      funext x
      rw [Complex.ofReal_sum, Finset.mul_sum]
    rw [hrw, intervalIntegral.integral_finsetSum]
    intro i hi
    exact Continuous.intervalIntegrable ((continuous_efun.comp (by fun_prop)).mul
      (Complex.continuous_ofReal.comp (hf.comp (by fun_prop)))) 0 1
  have hterm : ∀ j ∈ Finset.range (2 * K + 1),
      (∫ x in (0:ℝ)..1, efun (-((n : ℝ) * x)) * ((f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ))
        = (m : ℂ) * ∫ y in a j..a (j+1), Ψ y := by
    intro j hj
    have hgen := single_term (f := f) hm n (((j : ℤ) : ℝ) - ((K : ℤ) : ℝ))
    rw [hgen]
    congr 1
    have ezz : (↑(↑j : ℤ) : ℝ) - (↑(↑K : ℤ) : ℝ) = (j : ℝ) - (K : ℝ) := by push_cast; ring
    have e1 : ((j : ℝ) - (K : ℝ)) / m = a j := by rw [ha]
    have e2 : (((j : ℝ) - (K : ℝ)) + 1) / m = a (j+1) := by
      rw [ha]; simp only; push_cast; ring
    rw [ezz, e1, e2]
    refine intervalIntegral.integral_congr fun y hy => ?_
    simp only [hΨ]
    congr 1
    have : -((n : ℝ) * (m * y - ((j : ℝ) - (K : ℝ))))
        = -(((n : ℝ) * m) * y) + ((n * ((j : ℤ) - (K : ℤ)) : ℤ) : ℝ) := by
      push_cast; ring
    rw [this, efun_add, efun_int, mul_one]
  rw [hsplit, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [intervalIntegral.sum_integral_adjacent_intervals (f := Ψ) (a := a) (n := 2*K+1)
      (fun k hk => hΨc.intervalIntegrable _ _)]
  have ha0 : a 0 = -(K : ℝ)/m := by rw [ha]; simp
  have haN : a (2*K+1) = ((K:ℝ)+1)/m := by rw [ha]; simp only; push_cast; ring
  have hKK : R ≤ (K:ℝ)/m := by rw [le_div_iff₀ hm]; linarith
  have hle : a 0 ≤ a (2*K+1) := by
    rw [ha0, haN]
    apply div_le_div_of_nonneg_right _ hm.le
    linarith
  have hsupp : ∀ y ∉ Set.Icc (a 0) (a (2*K+1)), Ψ y = 0 := by
    intro y hy
    have hzero : f y = 0 := by
      apply hRf
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases lt_or_ge R 0 with hR | hR
      · exact lt_of_lt_of_le hR (abs_nonneg y)
      · rcases hy with h | h
        · have hy1 : y < -(K:ℝ)/m := by rw [← ha0]; exact h
          have h2 : -(K:ℝ)/m ≤ -R := by rw [neg_div]; exact neg_le_neg hKK
          have hy2 : y < -R := by linarith
          rw [abs_of_neg (by linarith)]; linarith
        · have hy1 : ((K:ℝ)+1)/m < y := by rw [← haN]; exact h
          have hy2 : R < y := by
            have h2 : R ≤ ((K:ℝ)+1)/m := by rw [le_div_iff₀ hm]; linarith
            linarith
          rw [abs_of_pos (by linarith)]; linarith
    rw [hΨ]
    simp only
    rw [hzero]
    simp
  have hfin : ∫ y in a 0..a (2*K+1), Ψ y = ∫ y, Ψ y := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  rw [hfin]
  simpa [hΨ] using (Fhat_eq_integral f ((n:ℝ)*m)).symm

end
end Work.GM.Affine
