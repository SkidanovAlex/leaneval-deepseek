import Mathlib
import Submission.Work.KMTAreas.A4.fejerKern_trig

/-!
# The Fejér-window convolution identity

For the dense-multiples engine one needs the exact value of the windowed convolution of the
classical Fejér kernel `Work.KMTAreas.A4.fejerKern N x = (N+1) * fejerWin N x` with the
indicator of the symmetric interval `[-a,a]`:

`∫ y in (-a)..a, fejerKern N (x - y) dy = 2a + 2 ∑_{n=1}^N (1 - n/(N+1)) (sin (2πna)/(πn)) cos (2πnx)`.

The computation proceeds in three steps.

* `fejerKern_trig` expands the kernel into the tent-coefficient cosine sum
  `fejerKern N z = ∑_{|n| ≤ N} (1 - |n|/(N+1)) cos (2πn z)`.
* `integral_cos_int_mul` computes the integral of a single cosine over the symmetric interval.
* `sum_Icc_neg_neg_eq` pairs the frequencies `n` and `-n`, and `sum_pairing` puts the two
  pieces together.
-/

namespace Work.KMTAreas.A4

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The integral of a cosine of a linear function over a symmetric interval. -/
theorem integral_cos_int_mul (m : ℤ) (a x : ℝ) :
    ∫ y in (-a)..a, Real.cos (2 * Real.pi * (m : ℝ) * (x - y))
      = if m = 0 then 2 * a
        else Real.sin (2 * Real.pi * (m : ℝ) * a) / (Real.pi * (m : ℝ))
          * Real.cos (2 * Real.pi * (m : ℝ) * x) := by
  by_cases hm : m = 0
  · rw [if_pos hm, hm]
    simp
    ring
  · rw [if_neg hm]
    have hmR : (m : ℝ) ≠ 0 := by intro h; exact hm (by exact_mod_cast h)
    have hc : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmR
    have harg : ∀ y : ℝ, Real.cos (2 * Real.pi * (m : ℝ) * (x - y))
        = Real.cos (2 * Real.pi * (m : ℝ) * x - 2 * Real.pi * (m : ℝ) * y) := by
      intro y; congr 1; ring
    simp_rw [harg]
    rw [intervalIntegral.integral_comp_mul_left
      (fun u => Real.cos (2 * Real.pi * (m : ℝ) * x - u)) hc]
    rw [intervalIntegral.integral_comp_sub_left Real.cos (2 * Real.pi * (m : ℝ) * x)]
    rw [integral_cos]
    rw [show 2 * Real.pi * (m : ℝ) * x - 2 * Real.pi * (m : ℝ) * (-a)
          = 2 * Real.pi * (m : ℝ) * x + 2 * Real.pi * (m : ℝ) * a from by ring]
    rw [Real.sin_add, Real.sin_sub]
    simp only [smul_eq_mul]
    field_simp
    ring

/-- Pairing the symmetric sum over `[-N, N]` with the sum over `[1, N]`: for an even function `c`
the sum over `ℤ ∩ [-N,N]` is the `n = 0` term plus twice the sum over `1 ≤ n ≤ N`. -/
theorem sum_Icc_neg_neg_eq (c : ℤ → ℝ) (hc : ∀ n, c (-n) = c n) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n = c 0 + 2 * ∑ n ∈ Finset.Icc 1 N, c (n : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-(((N + 1 : ℕ)) : ℤ)) (((N + 1 : ℕ)) : ℤ)
        = insert (-(((N + 1 : ℕ)) : ℤ))
            (insert (((N + 1 : ℕ)) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h1 : (-(((N + 1 : ℕ)) : ℤ))
        ∉ insert (((N + 1 : ℕ)) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h2 : (((N + 1 : ℕ)) : ℤ) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, ih,
        Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega)]
    rw [hc]
    ring

/-- The `ℤ`-sum of the Fejér convolution summands reduces to the `ℕ`-sum appearing in
`fejerKern_conv`. -/
theorem sum_pairing (N : ℕ) (a x : ℝ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - |(n : ℝ)| / ((N : ℝ) + 1)) *
          (if n = 0 then 2 * a
           else Real.sin (2 * Real.pi * (n : ℝ) * a) / (Real.pi * (n : ℝ))
                * Real.cos (2 * Real.pi * (n : ℝ) * x))
      = 2 * a + 2 * ∑ n ∈ Finset.Icc 1 N,
          (1 - (n : ℝ) / ((N : ℝ) + 1))
            * (Real.sin (2 * Real.pi * (n : ℝ) * a) / (Real.pi * (n : ℝ)))
            * Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  set c : ℤ → ℝ := fun m =>
      (1 - |(m : ℝ)| / ((N : ℝ) + 1)) *
        (if m = 0 then 2 * a
         else Real.sin (2 * Real.pi * (m : ℝ) * a) / (Real.pi * (m : ℝ))
              * Real.cos (2 * Real.pi * (m : ℝ) * x)) with hcdef
  have hc0 : c 0 = 2 * a := by
    rw [hcdef]
    simp
  have hcn : ∀ n : ℤ, c (-n) = c n := by
    intro n
    rw [hcdef]
    simp only [Int.cast_neg, abs_neg]
    by_cases hn : n = 0
    · rw [hn]; simp
    · have hn' : (-n : ℤ) ≠ 0 := neg_ne_zero.mpr hn
      rw [if_neg hn', if_neg hn]
      have hsin : Real.sin (2 * Real.pi * (-(n : ℝ)) * a) / (Real.pi * (-(n : ℝ)))
          = Real.sin (2 * Real.pi * (n : ℝ) * a) / (Real.pi * (n : ℝ)) := by
        rw [show (2 : ℝ) * Real.pi * (-(n : ℝ)) * a = -(2 * Real.pi * (n : ℝ) * a)
              from by ring,
            show Real.pi * (-(n : ℝ)) = -(Real.pi * (n : ℝ)) from by ring,
            Real.sin_neg, neg_div_neg_eq]
      have hcos : Real.cos (2 * Real.pi * (-(n : ℝ)) * x)
          = Real.cos (2 * Real.pi * (n : ℝ) * x) := by
        rw [show (2 : ℝ) * Real.pi * (-(n : ℝ)) * x = -(2 * Real.pi * (n : ℝ) * x)
              from by ring,
            Real.cos_neg]
      rw [hsin, hcos]
  have hsum : ∑ n ∈ Finset.Icc 1 N, c (n : ℤ)
      = ∑ n ∈ Finset.Icc 1 N,
          (1 - (n : ℝ) / ((N : ℝ) + 1))
            * (Real.sin (2 * Real.pi * (n : ℝ) * a) / (Real.pi * (n : ℝ)))
            * Real.cos (2 * Real.pi * (n : ℝ) * x) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnz : ((n : ℤ)) ≠ 0 := by
      intro h
      have : n = 0 := by exact_mod_cast h
      omega
    rw [hcdef]
    simp only []
    rw [if_neg hnz]
    have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
    rw [hcast, abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  rw [sum_Icc_neg_neg_eq c hcn N, hc0, hsum]

theorem fejerKern_conv (N : ℕ) (a x : ℝ) : ∫ y in (-a)..a, fejerKern N (x - y) = 2*a + 2 * ∑ n ∈ Finset.Icc 1 N, (1 - (n:ℝ)/((N:ℝ)+1)) * (Real.sin (2*Real.pi*(n:ℝ)*a)/(Real.pi*(n:ℝ))) * Real.cos (2*Real.pi*(n:ℝ)*x) := by
  have htrig : ∀ y : ℝ, fejerKern N (x - y) = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (1 - |(n : ℝ)| / ((N : ℝ) + 1)) * Real.cos (2 * Real.pi * (n : ℝ) * (x - y)) := by
    intro y
    exact fejerKern_trig N (x - y)
  have hint : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      IntervalIntegrable (fun y : ℝ =>
        (1 - |(n : ℝ)| / ((N : ℝ) + 1)) * Real.cos (2 * Real.pi * (n : ℝ) * (x - y)))
        volume (-a) a := by
    intro n hn
    exact (continuous_const.mul (Real.continuous_cos.comp
      (by fun_prop : Continuous fun y : ℝ => 2 * Real.pi * (n : ℝ) * (x - y)))).intervalIntegrable (-a) a
  have hlin : ∫ y in (-a)..a, (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - |(n : ℝ)| / ((N : ℝ) + 1)) * Real.cos (2 * Real.pi * (n : ℝ) * (x - y)))
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∫ y in (-a)..a,
            (1 - |(n : ℝ)| / ((N : ℝ) + 1)) * Real.cos (2 * Real.pi * (n : ℝ) * (x - y)) :=
    intervalIntegral.integral_finsetSum
      (E := ℝ) (a := -a) (b := a) (μ := volume) (ι := ℤ)
      (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
      (f := fun n y => (1 - |(n : ℝ)| / ((N : ℝ) + 1)) * Real.cos (2 * Real.pi * (n : ℝ) * (x - y)))
      hint
  simp_rw [htrig]
  rw [hlin]
  simp_rw [intervalIntegral.integral_const_mul, integral_cos_int_mul]
  exact sum_pairing N a x

end

end Work.KMTAreas.A4
