

import Mathlib
import Submission.Commons.Analysis.Complex.intervalIntegral_re_comm
import Submission.Work.Analysis.Complex.cpow_nat_eq_exp
import Submission.Work.Analysis.Integral.norm_intervalIntegral_exp_I_mul_le
import Submission.Work.Analysis.Real.log_diff_ge_div
import Submission.Work.Analysis.Complex.dirichletPoly_normsq_expansion

/-!
# `Work.ZeroDensity.Zeta.dirichletPoly_meanValue_integral_corrected` — Montgomery's mean value
theorem for Dirichlet polynomials (integral form), **correctly parenthesised**.

The statement requested as `Work.ZeroDensity.Zeta.dirichletPoly_meanValue_integral` was

```
|∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
  - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2| ≤ C * ((N : ℝ) * Real.log ((N : ℝ) + 2)) * ∑ ...
```

Lean's `∫ t in a..b, _` notation absorbs everything to the right into the *integrand*, so that
text elaborates to `|∫_0^T (‖z(t)‖² − T·Σ)| ≤ …`, which is FALSE (see the module docstring of
`Submission/Work/ZeroDensity/Zeta/dirichletPoly_meanValue_integral.lean`).  Adding the missing
parentheses around the integral gives the intended — and true — Montgomery mean value theorem
`|(∫_0^T ‖z(t)‖² dt) − T·Σ| ≤ C·N·log(N+2)·Σ`, which is what is proved here (with `C = 20`).

Everything is reduced to the exact identity
`∫_0^T ‖z‖² = T·Σ + re (Σ_{m≠n} a_m conj(a_n) ∫_0^T exp(i t log(m/n)))`
and to the bound `|∫_0^T exp(i t θ)| ≤ 2/|θ| ≤ 2N/|m−n|`.
-/

open scoped BigOperators
open Complex

namespace Work.ZeroDensity.Zeta

noncomputable section

/-- `mvTheta m n = log m - log n`, the frequency attached to the pair `(m, n)`. -/
private def mvTheta (m n : ℕ) : ℝ := Real.log (m : ℝ) - Real.log (n : ℝ)

/-- The complex double sum whose real part is `‖∑ a n · n^{it}‖²`. -/
private def mvPhi (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    (a m * (starRingEnd ℂ) (a n)) * Complex.exp (Complex.I * ((t * mvTheta m n : ℝ) : ℂ))

/-- The oscillatory integral `∫₀ᵀ exp(i θ t) dt` for `θ = mvTheta m n`. -/
private def mvK (T : ℝ) (m n : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * ((t * mvTheta m n : ℝ) : ℂ))

private lemma mvPhi_continuous (a : ℕ → ℂ) (N : ℕ) : Continuous (mvPhi a N) := by
  unfold mvPhi
  fun_prop

/-- **Pointwise expansion** of the squared norm as a double sum. -/
private lemma mvPhi_expansion (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
      = (mvPhi a N t).re := by
  rw [Work.Analysis.Complex.dirichletPoly_normsq_expansion a N t]
  simp only [mvPhi, mvTheta]

/-- `mvK T m m = T`. -/
private lemma mvK_self (T : ℝ) (m : ℕ) : mvK T m m = (T : ℂ) := by
  rw [mvK, mvTheta]
  have h : (fun t : ℝ => Complex.exp (Complex.I * ((t * (Real.log (m : ℝ) - Real.log (m : ℝ)) : ℝ) : ℂ)))
      = fun _ : ℝ => (1 : ℂ) := by
    funext t; rw [sub_self, mul_zero]; norm_num
  rw [h, intervalIntegral.integral_const]; simp

/-- Norm bound for the oscillatory integral. -/
private lemma mvK_norm_le (T : ℝ) (m n : ℕ) (h : mvTheta m n ≠ 0) :
    ‖mvK T m n‖ ≤ 2 / |mvTheta m n| := by
  rw [mvK]
  have hfun : (fun t : ℝ => Complex.exp (Complex.I * ((t * mvTheta m n : ℝ) : ℂ)))
      = fun t : ℝ => Complex.exp (Complex.I * ((mvTheta m n * t : ℝ) : ℂ)) := by
    funext t; simp only [mul_comm t (mvTheta m n)]
  rw [hfun]
  exact Work.Analysis.Integral.norm_intervalIntegral_exp_I_mul_le T (mvTheta m n) h

/-- **The integral of the double sum** is the double sum of the integrals. -/
private lemma mvPhi_integral (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, mvPhi a N t)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (a m * (starRingEnd ℂ) (a n)) * mvK T m n := by
  simp only [mvPhi, mvK, mvTheta]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro n hn
      rw [intervalIntegral.integral_const_mul]
    · intro n hn
      exact (by fun_prop : Continuous fun t : ℝ => (a m * (starRingEnd ℂ) (a n)) *
        Complex.exp (Complex.I * ((t * (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ))).intervalIntegrable _ _
  · intro m hm
    exact (by fun_prop : Continuous fun t : ℝ => ∑ n ∈ Finset.Icc 1 N,
      (a m * (starRingEnd ℂ) (a n)) *
        Complex.exp (Complex.I * ((t * (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ))).intervalIntegrable _ _

/-- Split the double sum into its diagonal and off-diagonal parts. -/
private lemma mvPhi_split (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (a m * (starRingEnd ℂ) (a n)) * mvK T m n)
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (a m * (starRingEnd ℂ) (a n)) * mvK T m n)
        + ∑ m ∈ Finset.Icc 1 N, (a m * (starRingEnd ℂ) (a m)) * mvK T m m := by
  have h1 : ∀ m ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc 1 N, (a m * (starRingEnd ℂ) (a n)) * mvK T m n)
        = (∑ n ∈ (Finset.Icc 1 N).erase m, (a m * (starRingEnd ℂ) (a n)) * mvK T m n)
          + (a m * (starRingEnd ℂ) (a m)) * mvK T m m := by
    intro m hm
    exact (Finset.sum_erase_add _ _ hm).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]

/-- The diagonal part evaluates to `T · ∑ ‖a n‖²`. -/
private lemma mvPhi_diag (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, (a m * (starRingEnd ℂ) (a m)) * mvK T m m)
      = ↑(T * ∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) := by
  simp only [mvK_self]
  have hstep : ∀ m, (a m * (starRingEnd ℂ) (a m)) * (T : ℂ) = ↑(T * ‖a m‖ ^ 2) := by
    intro m
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp only [hstep]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The real part of the integral of the double sum, split into diagonal and off-diagonal. -/
private lemma main_integral (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, mvPhi a N t).re
      = T * (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2)
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (a m * (starRingEnd ℂ) (a n)) * mvK T m n).re := by
  rw [mvPhi_integral, mvPhi_split, Complex.add_re, mvPhi_diag]
  simp only [Complex.ofReal_re]
  ring

/-- **The exact mean value identity** for the Dirichlet polynomial integral. -/
private lemma integral_identity (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
      = T * (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2)
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (a m * (starRingEnd ℂ) (a n)) * mvK T m n).re := by
  rw [← main_integral]
  rw [show (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
      = ∫ t in (0 : ℝ)..T, (mvPhi a N t).re from
    intervalIntegral.integral_congr (fun t _ => mvPhi_expansion a N t)]
  exact Commons.Analysis.Complex.intervalIntegral_re_comm (mvPhi a N) 0 T (mvPhi_continuous a N)

/-- `mvTheta m n ≠ 0` when `m ≠ n` are positive. -/
private lemma mvTheta_ne_zero {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    mvTheta m n ≠ 0 := by
  rw [mvTheta, sub_ne_zero]
  intro hc
  exact h (by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have := Real.log_injOn_pos hm0 hn0 hc
    exact_mod_cast this)

/-- Norm bound `‖mvK T m n‖ ≤ 2N/|m-n|` for `m ≠ n` in `[1, N]`. -/
private lemma mvK_norm_le' (T : ℝ) (m n N : ℕ) (hm : m ∈ Finset.Icc 1 N)
    (hn : n ∈ Finset.Icc 1 N) (hmn : m ≠ n) :
    ‖mvK T m n‖ ≤ 2 * (N : ℝ) / |(m : ℝ) - (n : ℝ)| := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hθ : mvTheta m n ≠ 0 := mvTheta_ne_zero hm1 hn1 hmn
  have hθpos : 0 < |mvTheta m n| := abs_pos.mpr hθ
  have hdpos : 0 < |(m : ℝ) - (n : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hD : |(m : ℝ) - (n : ℝ)| ≤ (N : ℝ) * |mvTheta m n| :=
    Work.Analysis.Real.log_diff_ge_div m n N hm hn
  refine (mvK_norm_le T m n hθ).trans ?_
  rw [div_le_div_iff₀ hθpos hdpos]
  calc (2 : ℝ) * |(m : ℝ) - (n : ℝ)| ≤ 2 * ((N : ℝ) * |mvTheta m n|) :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
    _ = (2 * (N : ℝ)) * |mvTheta m n| := by ring


/-- The harmonic sum bound `∑_{k ≤ K} 1/k ≤ 1 + log K`. -/
private lemma harm_sum_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ((k : ℝ))⁻¹) ≤ 1 + Real.log (K : ℝ) := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  simpa using h

/-- Row-sum bound for the `1/|m-n|` kernel: for `n ∈ [1,N]` the whole off-diagonal row
`∑_{m ≠ n} 1/|m-n|` is at most `2 (1 + log N)`. -/
private lemma row_sum_bound (n N : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    (∑ m ∈ (Finset.Icc 1 N).erase n, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|)
      ≤ 2 * (1 + Real.log (N : ℝ)) := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hunion : (Finset.Icc 1 N).erase n
      = (Finset.Icc 1 N).filter (fun m => m < n)
          ∪ (Finset.Icc 1 N).filter (fun m => n < m) := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint ((Finset.Icc 1 N).filter (fun m => m < n))
      ((Finset.Icc 1 N).filter (fun m => n < m)) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_filter] at hm1 hm2
    omega
  rw [hunion, Finset.sum_union hdisj]
  have hA : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => m < n),
        (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤ 1 + Real.log (N : ℝ) := by
    have hset : (Finset.Icc 1 N).filter (fun m => m < n) = Finset.Icc 1 (n - 1) := by
      ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hset]
    have hbij : (∑ m ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / |(m : ℝ) - (n : ℝ)|)
        = ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / (k : ℝ) := by
      refine Finset.sum_bij (fun m _ => n - m) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        simp only [Finset.mem_Icc]; omega
      · intro m1 hm1 m2 hm2 heq
        obtain ⟨hm11, hm12⟩ := Finset.mem_Icc.mp hm1
        obtain ⟨hm21, hm22⟩ := Finset.mem_Icc.mp hm2
        omega
      · intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        exact ⟨n - k, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hle : m ≤ n := by omega
        have hle' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
        rw [abs_of_nonpos (by linarith), Nat.cast_sub hle]
        ring
    rw [hbij]
    calc (∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / (k : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
          · intro k hk _; positivity
      _ = ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ := by simp [one_div]
      _ ≤ 1 + Real.log (N : ℝ) := harm_sum_le N
  have hB : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => n < m),
        (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤ 1 + Real.log (N : ℝ) := by
    have hset : (Finset.Icc 1 N).filter (fun m => n < m) = Finset.Icc (n + 1) N := by
      ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hset]
    have hbij : (∑ m ∈ Finset.Icc (n + 1) N, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|)
        = ∑ k ∈ Finset.Icc 1 (N - n), (1 : ℝ) / (k : ℝ) := by
      refine Finset.sum_bij (fun m _ => m - n) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        simp only [Finset.mem_Icc]; omega
      · intro m1 hm1 m2 hm2 heq
        obtain ⟨hm11, hm12⟩ := Finset.mem_Icc.mp hm1
        obtain ⟨hm21, hm22⟩ := Finset.mem_Icc.mp hm2
        omega
      · intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        exact ⟨n + k, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hle : n ≤ m := by omega
        have hle' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
        rw [abs_of_nonneg (by linarith), Nat.cast_sub hle]
    rw [hbij]
    calc (∑ k ∈ Finset.Icc 1 (N - n), (1 : ℝ) / (k : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
          · intro k hk _; positivity
      _ = ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ := by simp [one_div]
      _ ≤ 1 + Real.log (N : ℝ) := harm_sum_le N
  linarith

/-- The `1/|m-n|` quadratic-form (Schur) bound. -/
private lemma harmonic_convolution_le' (a : ℕ → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|)
      ≤ 2 * (1 + Real.log (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hstep1 : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)| := by
    apply Finset.sum_congr rfl
    intro m hm
    have hz : (fun n : ℕ => ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|) m = 0 := by simp
    exact Finset.sum_erase (Finset.Icc 1 N)
      (f := fun n => ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|) (a := m) hz
  have hstep2 : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|)
      ≤ (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|))
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a n‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have h1 : ‖a m‖ * ‖a n‖ ≤ (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)]
    have hD : 0 ≤ |(m : ℝ) - (n : ℝ)| := abs_nonneg _
    calc ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|
        ≤ ((‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2) / |(m : ℝ) - (n : ℝ)| :=
          div_le_div_of_nonneg_right h1 hD
      _ = ‖a m‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|)
            + ‖a n‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|) := by ring
  have hA : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|))
      = ∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2 * (∑ n ∈ Finset.Icc 1 N,
          1 / (2 * |(m : ℝ) - (n : ℝ)|)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hBswap : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a n‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|))
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          ‖a n‖ ^ 2 / (2 * |(n : ℝ) - (m : ℝ)|) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [abs_sub_comm]
  have hB : (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          ‖a n‖ ^ 2 / (2 * |(n : ℝ) - (m : ℝ)|))
      = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (∑ m ∈ Finset.Icc 1 N,
          1 / (2 * |(n : ℝ) - (m : ℝ)|)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hInner : ∀ m ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc 1 N, 1 / (2 * |(m : ℝ) - (n : ℝ)|)) ≤ 1 + Real.log (N : ℝ) := by
    intro m hm
    have hz : (fun n : ℕ => 1 / (2 * |(m : ℝ) - (n : ℝ)|)) m = 0 := by simp
    have h1 : (∑ n ∈ Finset.Icc 1 N, 1 / (2 * |(m : ℝ) - (n : ℝ)|))
        = (1 / 2) * (∑ n ∈ (Finset.Icc 1 N).erase m, 1 / |(n : ℝ) - (m : ℝ)|) := by
      rw [← Finset.sum_erase (Finset.Icc 1 N)
        (f := fun n => 1 / (2 * |(m : ℝ) - (n : ℝ)|)) (a := m) hz]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [abs_sub_comm]
      ring
    rw [h1]
    have := row_sum_bound m N hm
    linarith
  calc (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)|)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)| := hstep1
    _ ≤ (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|))
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a n‖ ^ 2 / (2 * |(m : ℝ) - (n : ℝ)|)) := hstep2
    _ = (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2 * (∑ n ∈ Finset.Icc 1 N,
          1 / (2 * |(m : ℝ) - (n : ℝ)|)))
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (∑ m ∈ Finset.Icc 1 N,
          1 / (2 * |(n : ℝ) - (m : ℝ)|))) := by rw [hA, hBswap, hB]
    _ ≤ (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2 * (1 + Real.log (N : ℝ)))
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (1 + Real.log (N : ℝ))) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro m hm
          exact mul_le_mul_of_nonneg_left (hInner m hm) (by positivity)
        · apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_left (hInner n hn) (by positivity)
    _ = 2 * (1 + Real.log (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
        rw [← Finset.sum_mul]
        ring

/-- **Off-diagonal bound** by the harmonic convolution. -/
private lemma offdiag_bound (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        (a m * (starRingEnd ℂ) (a n)) * mvK T m n‖
      ≤ 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
  have hnorm : ∀ m n, ‖(a m * (starRingEnd ℂ) (a n)) * mvK T m n‖
      = ‖a m‖ * ‖a n‖ * ‖mvK T m n‖ := by
    intro m n; rw [norm_mul, norm_mul, Complex.norm_conj]
  calc ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          (a m * (starRingEnd ℂ) (a n)) * mvK T m n‖
      ≤ ∑ m ∈ Finset.Icc 1 N, ‖∑ n ∈ (Finset.Icc 1 N).erase m,
          (a m * (starRingEnd ℂ) (a n)) * mvK T m n‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          ‖(a m * (starRingEnd ℂ) (a n)) * mvK T m n‖ := by
        apply Finset.sum_le_sum; intro m hm
        exact norm_sum_le _ _
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          ‖a m‖ * ‖a n‖ * ‖mvK T m n‖ := by
        apply Finset.sum_congr rfl; intro m hm
        apply Finset.sum_congr rfl; intro n hn
        rw [hnorm]
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          ‖a m‖ * ‖a n‖ * (2 * (N : ℝ) / |(m : ℝ) - (n : ℝ)|) := by
        apply Finset.sum_le_sum; intro m hm
        apply Finset.sum_le_sum; intro n hn
        have hmn : m ≠ n := (Finset.mem_erase.mp hn).1.symm
        have hn' : n ∈ Finset.Icc 1 N := (Finset.mem_erase.mp hn).2
        exact mul_le_mul_of_nonneg_left (mvK_norm_le' T m n N hm hn' hmn) (by positivity)
    _ = 2 * (N : ℝ) * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          ‖a m‖ * ‖a n‖ / |(m : ℝ) - (n : ℝ)| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n hn
        ring
    _ ≤ 2 * (N : ℝ) * (2 * (1 + Real.log (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (harmonic_convolution_le' a N)
          (by positivity)
    _ = 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by ring

/-- The numerical inequality `4·N·(1 + log N) ≤ 20·N·log(N+2)`. -/
private lemma log_factor (N : ℕ) :
    4 * (N : ℝ) * (1 + Real.log (N : ℝ))
      ≤ 20 * ((N : ℝ) * Real.log ((N : ℝ) + 2)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [Real.log_zero]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hL : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      have h3N : (3 : ℝ) ≤ (N : ℝ) + 2 := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      linarith
    have h2 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log hNpos (by linarith)
    nlinarith [hL, h2, hNpos, Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 2 by linarith)]

theorem dirichletPoly_meanValue_integral_corrected :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ), 0 < T →
      |(∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
        - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2|
        ≤ C * ((N : ℝ) * Real.log ((N : ℝ) + 2)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  refine ⟨20, by norm_num, ?_⟩
  intro a N T _hT
  have hkey := integral_identity a N T
  have hb := offdiag_bound a N T
  have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hEq : (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
      - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (a m * (starRingEnd ℂ) (a n)) * mvK T m n).re := by
    rw [hkey]; ring
  rw [hEq]
  calc |(∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (a m * (starRingEnd ℂ) (a n)) * mvK T m n).re|
      ≤ ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (a m * (starRingEnd ℂ) (a n)) * mvK T m n‖ := Complex.abs_re_le_norm _
    _ ≤ 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := hb
    _ ≤ 20 * ((N : ℝ) * Real.log ((N : ℝ) + 2)) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (log_factor N) hS

end

end Work.ZeroDensity.Zeta
