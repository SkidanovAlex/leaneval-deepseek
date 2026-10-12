import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Submission.Work.BoseFixR.LatGreen.HeatK1Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.PoissonGauss1D`

One-dimensional Poisson/Jacobi summation for the Gaussian heat kernel: the periodisation
`Σ_{n∈ℤ} heatK1 t (x−n)` of `heatK1 t` is its Fourier series `Σ_{m∈ℤ} e^{−4π²t m²} cos(2π m x)`,
together with the exponential tail bound `|Σ_n heatK1 t (x−n) − 1| ≤ 2 Σ_{j≥0} e^{−4π²t (j+1)²}`.

The heart is the complex identity `↑(Σ_n heatK1 t (x−n)) = Σ_m θ_m` (`tsum_heatK1_complex`),
proved from Mathlib's Jacobi theta transformation `Complex.tsum_exp_neg_quadratic`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR.LatGreen

/-! ### The complex Jacobi/Poisson identity -/

/-- The one-dimensional heat kernel, cast to `ℂ`, is a complex Gaussian. -/
lemma ofReal_heatK1 {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ((heatK1 t y : ℝ) : ℂ)
      = (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          * Complex.exp (-((y : ℂ) ^ 2) / (4 * (t : ℂ))) := by
  have hq : (0 : ℝ) < 4 * Real.pi * t := by positivity
  unfold heatK1
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hq.le, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The same, with the argument written as `x − n` for `n : ℤ`. -/
lemma ofReal_heatK1_sub {t x : ℝ} (ht : 0 < t) (n : ℤ) :
    ((heatK1 t (x - n) : ℝ) : ℂ)
      = (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          * Complex.exp (-(((x : ℂ) - (n : ℂ)) ^ 2) / (4 * (t : ℂ))) := by
  have h := ofReal_heatK1 ht (x - (n : ℝ))
  rw [show ((x - (n : ℝ) : ℝ) : ℂ) = ((x : ℂ) - (n : ℂ)) by push_cast; ring] at h
  exact h

/-- The exponent identity comparing the Jacobi theta exponent with the heat-kernel exponent. -/
lemma theta_exponent_eq {t x : ℝ} (ht : 0 < t) (n : ℤ) :
    -(Real.pi : ℂ) * (((1 / (4 * Real.pi * t) : ℝ)) : ℂ) * (n : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * (((x / (4 * Real.pi * t) : ℝ)) : ℂ) * (n : ℂ)
      = -((n : ℂ) ^ 2) / (4 * (t : ℂ)) + (x : ℂ) * (n : ℂ) / (2 * (t : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  ring

/-- Splitting the exponent of the heat kernel into the `x`-part and the `n`-part. -/
lemma exp_split_eq {t x : ℝ} (ht : 0 < t) (n : ℤ) :
    Complex.exp (-(((x : ℂ) - (n : ℂ)) ^ 2) / (4 * (t : ℂ)))
      = Complex.exp (-((x : ℂ) ^ 2) / (4 * (t : ℂ)))
          * Complex.exp (-((n : ℂ) ^ 2) / (4 * (t : ℂ))
              + (x : ℂ) * (n : ℂ) / (2 * (t : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp
  ring

/-- Jacobi's theta transformation, applied to the `n`-sum of the heat kernel. -/
lemma tsum_exp_theta {t x : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, Complex.exp (-((n : ℂ) ^ 2) / (4 * (t : ℂ))
        + (x : ℂ) * (n : ℂ) / (2 * (t : ℂ))))
      = 1 / ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))
          * ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / (((1 / (4 * Real.pi * t) : ℝ)) : ℂ)
              * ((n : ℂ) + Complex.I * (((x / (4 * Real.pi * t) : ℝ)) : ℂ)) ^ 2) := by
  have hA : 0 < ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  have h := Complex.tsum_exp_neg_quadratic (a := (((1 / (4 * Real.pi * t) : ℝ)) : ℂ))
      (b := (((x / (4 * Real.pi * t) : ℝ)) : ℂ)) hA
  rw [show (∑' n : ℤ, Complex.exp (-((n : ℂ) ^ 2) / (4 * (t : ℂ))
          + (x : ℂ) * (n : ℂ) / (2 * (t : ℂ))))
        = ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (((1 / (4 * Real.pi * t) : ℝ)) : ℂ)
            * (n : ℂ) ^ 2
            + 2 * (Real.pi : ℂ) * (((x / (4 * Real.pi * t) : ℝ)) : ℂ) * (n : ℂ)) from
      tsum_congr (fun n => by rw [theta_exponent_eq ht n])]
  rw [h]

/-- The exponent of the theta-transformed summand, split into the `x`-factor, the Fourier
coefficient and the phase. -/
lemma theta_rhs_exponent_eq {t x : ℝ} (ht : 0 < t) (n : ℤ) :
    -(Real.pi : ℂ) / (((1 / (4 * Real.pi * t) : ℝ)) : ℂ)
        * ((n : ℂ) + Complex.I * (((x / (4 * Real.pi * t) : ℝ)) : ℂ)) ^ 2
      = ((x : ℂ) ^ 2) / (4 * (t : ℂ))
          + ((-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2 : ℝ) : ℂ)
          + (-(2 * Real.pi * Complex.I * ((n : ℝ) * x))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

/-- Termwise identification of the theta sum with the Fourier series of the heat kernel. -/
lemma theta_sum_eq {t x : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / (((1 / (4 * Real.pi * t) : ℝ)) : ℂ)
        * ((n : ℂ) + Complex.I * (((x / (4 * Real.pi * t) : ℝ)) : ℂ)) ^ 2))
      = Complex.exp (((x : ℂ) ^ 2) / (4 * (t : ℂ)))
          * (∑' n : ℤ, thetaTerm1 t x n) := by
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [theta_rhs_exponent_eq ht n]
  unfold thetaTerm1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, add_assoc]

/-- The prefactor of the theta transformation cancels the prefactor of the heat kernel. -/
lemma prefactor_mul_eq_one {t : ℝ} (ht : 0 < t) :
    (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * (1 / ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))) = 1 := by
  have hq : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have h12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hkey : ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))
      = (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← h12,
      ← Complex.ofReal_cpow (show (0 : ℝ) ≤ 1 / (4 * Real.pi * t) by positivity) (1 / 2 : ℝ)]
    congr 1
    rw [show (1 / (4 * Real.pi * t) : ℝ) = (4 * Real.pi * t) ^ (-1 : ℝ) by
      rw [Real.rpow_neg_one, inv_eq_one_div]]
    rw [← Real.rpow_mul hq.le (-1 : ℝ) (1 / 2 : ℝ)]
    norm_num
  rw [hkey]
  have hne : (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero, ne_eq]
    exact ne_of_gt (Real.rpow_pos_of_pos hq _)
  field_simp

/-- **The complex Poisson/Jacobi summation identity** for the one-dimensional heat kernel. -/
lemma tsum_heatK1_complex {t x : ℝ} (ht : 0 < t) :
    (((∑' n : ℤ, heatK1 t (x - n)) : ℝ) : ℂ) = ∑' n : ℤ, thetaTerm1 t x n := by
  have h1 : (((∑' n : ℤ, heatK1 t (x - n)) : ℝ) : ℂ)
      = (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          * (∑' n : ℤ, Complex.exp (-(((x : ℂ) - (n : ℂ)) ^ 2) / (4 * (t : ℂ)))) := by
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr (fun n => ofReal_heatK1_sub ht n)
  have h2 : (∑' n : ℤ, Complex.exp (-(((x : ℂ) - (n : ℂ)) ^ 2) / (4 * (t : ℂ))))
      = Complex.exp (-((x : ℂ) ^ 2) / (4 * (t : ℂ)))
          * (∑' n : ℤ, Complex.exp (-((n : ℂ) ^ 2) / (4 * (t : ℂ))
              + (x : ℂ) * (n : ℂ) / (2 * (t : ℂ)))) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => exp_split_eq ht n)
  have h3 : (∑' n : ℤ, Complex.exp (-((n : ℂ) ^ 2) / (4 * (t : ℂ))
          + (x : ℂ) * (n : ℂ) / (2 * (t : ℂ))))
        = 1 / ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))
          * ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / (((1 / (4 * Real.pi * t) : ℝ)) : ℂ)
              * ((n : ℂ) + Complex.I * (((x / (4 * Real.pi * t) : ℝ)) : ℂ)) ^ 2) :=
    tsum_exp_theta ht
  have h4 : (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / (((1 / (4 * Real.pi * t) : ℝ)) : ℂ)
          * ((n : ℂ) + Complex.I * (((x / (4 * Real.pi * t) : ℝ)) : ℂ)) ^ 2))
        = Complex.exp (((x : ℂ) ^ 2) / (4 * (t : ℂ)))
          * (∑' n : ℤ, thetaTerm1 t x n) :=
    theta_sum_eq ht
  have hc : (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      * (1 / ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))) = 1 :=
    prefactor_mul_eq_one ht
  have he : Complex.exp (-((x : ℂ) ^ 2) / (4 * (t : ℂ)))
      * Complex.exp (((x : ℂ) ^ 2) / (4 * (t : ℂ))) = 1 := by
    rw [show -((x : ℂ) ^ 2) / (4 * (t : ℂ)) = -(((x : ℂ) ^ 2) / (4 * (t : ℂ))) by
      rw [neg_div]]
    rw [Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _)]
  rw [h1, h2, h3, h4]
  rw [show (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * (Complex.exp (-((x : ℂ) ^ 2) / (4 * (t : ℂ)))
          * (1 / ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))
            * (Complex.exp (((x : ℂ) ^ 2) / (4 * (t : ℂ)))
              * (∑' n : ℤ, thetaTerm1 t x n))))
      = ((((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          * (1 / ((((1 / (4 * Real.pi * t) : ℝ)) : ℂ) ^ (1 / 2 : ℂ))))
          * (Complex.exp (-((x : ℂ) ^ 2) / (4 * (t : ℂ)))
              * Complex.exp (((x : ℂ) ^ 2) / (4 * (t : ℂ))))
          * (∑' n : ℤ, thetaTerm1 t x n) from by ring,
    hc, he]
  simp

/-! ### The real Fourier series -/

/-- The real part of a Fourier term of the heat kernel. -/
lemma thetaTerm1_re {t x : ℝ} (m : ℤ) :
    (thetaTerm1 t x m).re
      = Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2)
          * Real.cos (2 * Real.pi * (m : ℝ) * x) := by
  unfold thetaTerm1
  rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.exp_re]
  have hre : (-(2 * Real.pi * Complex.I * ((m : ℝ) * x))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re]
  have him : (-(2 * Real.pi * Complex.I * ((m : ℝ) * x))).im
      = -(2 * Real.pi * (m : ℝ) * x) := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre, him, Real.exp_zero, one_mul, zero_mul, sub_zero, Real.cos_neg]

/-- The periodised heat kernel is its Fourier series (the first part of `PoissonGauss1D`). -/
lemma heatCosForm {t x : ℝ} (ht : 0 < t) :
    (∑' m : ℤ, heatK1 t (x - m))
      = ∑' m : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2)
          * Real.cos (2 * Real.pi * (m : ℝ) * x) := by
  have hsum : Summable fun m : ℤ => thetaTerm1 t x m := (summable_thetaTerm1 ht x).of_norm
  have hre : (∑' m : ℤ, thetaTerm1 t x m).re = ∑' m : ℤ, (thetaTerm1 t x m).re := by
    simpa using (Complex.reCLM.map_tsum hsum)
  have hc := tsum_heatK1_complex (x := x) ht
  calc (∑' m : ℤ, heatK1 t (x - m))
      = (((∑' m : ℤ, heatK1 t (x - m)) : ℝ) : ℂ).re := (Complex.ofReal_re _).symm
    _ = (∑' m : ℤ, thetaTerm1 t x m).re := by rw [hc]
    _ = ∑' m : ℤ, (thetaTerm1 t x m).re := hre
    _ = ∑' m : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2)
          * Real.cos (2 * Real.pi * (m : ℝ) * x) := tsum_congr (fun m => thetaTerm1_re m)

/-- The exponential tail bound for the periodised heat kernel (the second part of
`PoissonGauss1D`). -/
theorem abs_periodSum_sub_one_le {t x : ℝ} (ht : 0 < t)
    (hcos : (∑' m : ℤ, heatK1 t (x - m))
        = ∑' m : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2)
            * Real.cos (2 * Real.pi * (m : ℝ) * x)) :
    |(∑' m : ℤ, heatK1 t (x - m)) - 1|
      ≤ 2 * ∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2) := by
  have hpos : (0 : ℝ) < 4 * Real.pi ^ 2 * t := by positivity
  set a : ℤ → ℝ := fun m => Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2) with ha
  set G : ℤ → ℝ := fun m => a m * Real.cos (2 * Real.pi * (m : ℝ) * x) with hG
  have ha_nn : ∀ m : ℤ, 0 ≤ a m := fun m => by rw [ha]; positivity
  have hsa : Summable a := by
    rw [ha]
    exact summable_exp_neg_mul_sq_int hpos
  have hG0 : G 0 = 1 := by simp [hG, ha]
  have hs1 : Summable fun n : ℕ => a (↑n + 1) :=
    hsa.comp_injective fun m n h => Int.ofNat.inj (add_right_cancel h)
  have hs2 : Summable fun n : ℕ => a (-(↑n + 1)) :=
    hsa.comp_injective fun m n h => Int.ofNat.inj (add_right_cancel (neg_injective h))
  have hbd1 : ∀ n : ℕ, ‖G (↑n + 1)‖ ≤ a (↑n + 1) := by
    intro n
    simp only [hG]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha_nn _)]
    calc a (↑n + 1) * |Real.cos (2 * Real.pi * ((↑n + 1 : ℤ) : ℝ) * x)|
        ≤ a (↑n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (ha_nn _)
      _ = a (↑n + 1) := mul_one _
  have hbd2 : ∀ n : ℕ, ‖G (-(↑n + 1))‖ ≤ a (-(↑n + 1)) := by
    intro n
    simp only [hG]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha_nn _)]
    calc a (-(↑n + 1)) * |Real.cos (2 * Real.pi * ((-(↑n + 1) : ℤ) : ℝ) * x)|
        ≤ a (-(↑n + 1)) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (ha_nn _)
      _ = a (-(↑n + 1)) := mul_one _
  have hG1 : Summable fun n : ℕ => G (↑n + 1) := Summable.of_norm_bounded hs1 hbd1
  have hG2 : Summable fun n : ℕ => G (-(↑n + 1)) := Summable.of_norm_bounded hs2 hbd2
  have hsplit : (∑' n : ℤ, G n)
      = (∑' n : ℕ, G (↑n + 1)) + G 0 + (∑' n : ℕ, G (-(↑n + 1))) :=
    tsum_of_add_one_of_neg_add_one hG1 hG2
  have hcosG : (∑' m : ℤ, heatK1 t (x - m)) = ∑' m : ℤ, G m := by
    rw [hcos]
  have hS : (∑' m : ℤ, heatK1 t (x - m))
      = (∑' n : ℕ, G (↑n + 1)) + 1 + (∑' n : ℕ, G (-(↑n + 1))) := by
    rw [hcosG, hsplit, hG0]
  rw [hS]
  have hsub : (∑' n : ℕ, G (↑n + 1)) + 1 + (∑' n : ℕ, G (-(↑n + 1))) - 1
      = (∑' n : ℕ, G (↑n + 1)) + (∑' n : ℕ, G (-(↑n + 1))) := by ring
  rw [hsub]
  calc |(∑' n : ℕ, G (↑n + 1)) + (∑' n : ℕ, G (-(↑n + 1)))|
      ≤ |(∑' n : ℕ, G (↑n + 1))| + |(∑' n : ℕ, G (-(↑n + 1)))| := abs_add_le _ _
    _ ≤ (∑' n : ℕ, a (↑n + 1)) + (∑' n : ℕ, a (-(↑n + 1))) := by
        refine add_le_add ?_ ?_
        · simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hs1.hasSum hbd1
        · simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hs2.hasSum hbd2
    _ = (∑' n : ℕ, a (↑n + 1)) + (∑' n : ℕ, a (↑n + 1)) := by
        congr 1
        exact tsum_congr fun n => by
          simp only [ha]
          congr 1
          push_cast
          ring
    _ = 2 * (∑' n : ℕ, a (↑n + 1)) := by ring
    _ = 2 * ∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2) := by
        congr 1
        exact tsum_congr fun j => by
          simp only [ha]
          congr 1
          push_cast
          ring

theorem PoissonGauss1D {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∑' m : ℤ, Work.BoseFixR.LatGreen.heatK1 t (x - m))
        = ∑' m : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2)
            * Real.cos (2 * Real.pi * (m : ℝ) * x)
      ∧ |(∑' m : ℤ, Work.BoseFixR.LatGreen.heatK1 t (x - m)) - 1|
          ≤ 2 * ∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2) := by
  exact ⟨heatCosForm ht, abs_periodSum_sub_one_le ht (heatCosForm ht)⟩

end Work.BoseFixR.LatGreen
