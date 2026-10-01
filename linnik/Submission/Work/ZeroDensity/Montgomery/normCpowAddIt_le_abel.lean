import Mathlib
import Submission.Work.ZeroDensity.Montgomery.sumIcc_byParts

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators

/-- Telescoping identity for `Icc 1 (N-1)`: `∑_{n=1}^{N-1}(w n - w (n+1)) = w 1 - w N`. -/
lemma sum_Icc_sub_eq (w : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 (N - 1), (w n - w (n + 1)) = w 1 - w N := by
  have hIcc : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have h2 : ∑ k ∈ Finset.range (N - 1), (w (1 + k) - w (1 + k + 1))
      = w (1 + 0) - w (1 + (N - 1)) :=
    Finset.sum_range_sub' (fun k => w (1 + k)) (N - 1)
  rw [h2]
  simp only [Nat.add_zero]
  rw [show 1 + (N - 1) = N by omega]

/-- Weighted Cauchy–Schwarz: for nonnegative weights `c` on a finite set `s` and any real `b`,
`(∑ c i · b i)^2 ≤ (∑ c i) · (∑ c i · b i^2)`. -/
lemma sum_mul_sq_le' (s : Finset ℕ) (c b : ℕ → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i * b i) ^ 2 ≤ (∑ i ∈ s, c i) * (∑ i ∈ s, c i * b i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (c i))
      (fun i => Real.sqrt (c i) * b i)
  have e1 : ∑ i ∈ s, Real.sqrt (c i) * (Real.sqrt (c i) * b i) = ∑ i ∈ s, c i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hc i hi)]
  have e2 : ∑ i ∈ s, Real.sqrt (c i) ^ 2 = ∑ i ∈ s, c i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.sq_sqrt (hc i hi)]
  have e3 : ∑ i ∈ s, (Real.sqrt (c i) * b i) ^ 2 = ∑ i ∈ s, c i * b i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hc i hi)]
  rw [e1, e2, e3] at h
  exact h

/-- **General Abel (summation-by-parts) norm-square bound.**  For a complex sequence `a` and a real
weight sequence `w` with `0 ≤ w n ≤ 1` for `n ≥ 1` and `w` nonincreasing on `n ≥ 1`,
`‖∑_{n≤N} a n · w n‖² ≤ 2‖X N‖² + 2 ∑_{n≤N-1} (w n - w (n+1))·‖X n‖²`, `X n = ∑_{k≤n} a k`. -/
theorem abel_norm_sq_bound (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (hw_nonneg : ∀ n, 1 ≤ n → 0 ≤ w n)
    (hw_le_one : ∀ n, 1 ≤ n → w n ≤ 1)
    (hw_anti : ∀ n, 1 ≤ n → w (n + 1) ≤ w n) :
    ‖∑ n ∈ Finset.Icc 1 N, a n * (w n : ℂ)‖ ^ 2
      ≤ 2 * ‖∑ k ∈ Finset.Icc 1 N, a k‖ ^ 2
        + 2 * ∑ n ∈ Finset.Icc 1 (N - 1), (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖ ^ 2 := by
  have hbp := sumIcc_byParts N a (fun n => (w n : ℂ))
  have hbp' : ∑ n ∈ Finset.Icc 1 N, a n * (w n : ℂ)
      = (w N : ℂ) * (∑ k ∈ Finset.Icc 1 N, a k)
        + ∑ n ∈ Finset.Icc 1 (N - 1),
            ((w n - w (n + 1) : ℝ) : ℂ) * (∑ k ∈ Finset.Icc 1 n, a k) := by
    rw [hbp]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Complex.ofReal_sub]
  have hS : ‖∑ n ∈ Finset.Icc 1 N, a n * (w n : ℂ)‖
      ≤ ‖∑ k ∈ Finset.Icc 1 N, a k‖
        + ∑ n ∈ Finset.Icc 1 (N - 1), (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖ := by
    rw [hbp']
    refine (norm_add_le _ _).trans ?_
    apply add_le_add
    · rw [norm_mul,
          show ‖((w N : ℝ) : ℂ)‖ = |w N| from RCLike.norm_ofReal (w N),
          abs_of_nonneg (hw_nonneg N hN)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw_le_one N hN)
    · refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro n hn
      have h1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hcn : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw_anti n h1n)
      rw [norm_mul,
          show ‖((w n - w (n + 1) : ℝ) : ℂ)‖ = |w n - w (n + 1)| from RCLike.norm_ofReal _,
          abs_of_nonneg hcn]
  have hsq : ‖∑ n ∈ Finset.Icc 1 N, a n * (w n : ℂ)‖ ^ 2
      ≤ (‖∑ k ∈ Finset.Icc 1 N, a k‖
          + ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hS 2
  have hsplit : (‖∑ k ∈ Finset.Icc 1 N, a k‖
          + ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2
      ≤ 2 * ‖∑ k ∈ Finset.Icc 1 N, a k‖ ^ 2
        + 2 * (∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2 := by
    nlinarith [sq_nonneg (‖∑ k ∈ Finset.Icc 1 N, a k‖
          - ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖)]
  have hcs : (∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 (N - 1), (w n - w (n + 1)))
        * (∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖ ^ 2) :=
    sum_mul_sq_le' _ _ _ (fun n hn => sub_nonneg.mpr (hw_anti n (Finset.mem_Icc.mp hn).1))
  have hsum : (∑ n ∈ Finset.Icc 1 (N - 1), (w n - w (n + 1))) ≤ 1 := by
    rw [sum_Icc_sub_eq w N hN]
    have h1 : w 1 ≤ 1 := hw_le_one 1 le_rfl
    have h2 : 0 ≤ w N := hw_nonneg N hN
    linarith
  have hS2nn : 0 ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖ ^ 2 :=
    Finset.sum_nonneg (fun n hn =>
      mul_nonneg (sub_nonneg.mpr (hw_anti n (Finset.mem_Icc.mp hn).1)) (sq_nonneg _))
  have hA2 : (∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖ ^ 2 :=
    hcs.trans (mul_le_of_le_one_left hS2nn hsum)
  calc ‖∑ n ∈ Finset.Icc 1 N, a n * (w n : ℂ)‖ ^ 2
      ≤ (‖∑ k ∈ Finset.Icc 1 N, a k‖
          + ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2 := hsq
    _ ≤ 2 * ‖∑ k ∈ Finset.Icc 1 N, a k‖ ^ 2
        + 2 * (∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖) ^ 2 := hsplit
    _ ≤ 2 * ‖∑ k ∈ Finset.Icc 1 N, a k‖ ^ 2
        + 2 * ∑ n ∈ Finset.Icc 1 (N - 1),
              (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, a k‖ ^ 2 := by linarith [hA2]

/-- Splitting the powers of a positive integer `n ≥ 1` in a complex product:
`v·n^{-σ₀}·n^{-it}·n^{-(σ-σ₀)} = v·n^{-(σ+it)}`. -/
theorem cpow_factor_neg_sigma_add_it (n : ℕ) (hn : 1 ≤ n) (v : ℂ) (σ₀ σ t : ℝ) :
    (v * ((((n : ℝ) ^ (-σ₀)) : ℝ) : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I))
        * ((((n : ℝ) ^ (-(σ - σ₀))) : ℝ) : ℂ)
      = v * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hrpow : (n : ℝ) ^ (-σ₀) * (n : ℝ) ^ (-(σ - σ₀)) = (n : ℝ) ^ (-σ) := by
    rw [← Real.rpow_add hpos (-σ₀) (-(σ - σ₀))]
    congr 1
    ring
  have hof : ((((n : ℝ) ^ (-σ₀)) : ℝ) : ℂ) * ((((n : ℝ) ^ (-(σ - σ₀))) : ℝ) : ℂ)
      = (n : ℂ) ^ (-(σ : ℂ)) := by
    rw [← Complex.ofReal_mul, hrpow, Complex.ofReal_cpow (le_of_lt hpos) (-σ),
        Complex.ofReal_natCast, Complex.ofReal_neg]
  calc (v * ((((n : ℝ) ^ (-σ₀)) : ℝ) : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I))
          * ((((n : ℝ) ^ (-(σ - σ₀))) : ℝ) : ℂ)
      = v * (((((n : ℝ) ^ (-σ₀)) : ℝ) : ℂ) * ((((n : ℝ) ^ (-(σ - σ₀))) : ℝ) : ℂ))
            * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by ring
    _ = v * (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by rw [hof]
    _ = v * ((n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I))) := by ring
    _ = v * (n : ℂ) ^ (-(σ : ℂ) + -((t : ℂ) * Complex.I)) := by
          rw [Complex.cpow_add (-(σ : ℂ)) (-((t : ℂ) * Complex.I)) hnc]
    _ = v * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
          rw [show -(σ : ℂ) + -((t : ℂ) * Complex.I)
                = -((σ : ℂ) + (t : ℂ) * Complex.I) by ring]

/-- **Pointwise Abel (summation-by-parts) bound for a truncated Dirichlet polynomial in a
vertical strip.**  For coefficients `v : ℕ → ℂ`, real `σ₀ ≤ σ` and `t`, and `N ≥ 1`, put
`X n = ∑_{k ≤ n} v k · k^{-σ₀} · k^{-it}` (the partial sums of the `σ₀`-weighted polynomial).
Then, writing `β = σ - σ₀ ≥ 0`,
`‖∑_{n≤N} v n · n^{-(σ+it)}‖² ≤ 2‖X N‖² + 2 ∑_{n≤N-1} (n^{-β} - (n+1)^{-β}) ‖X n‖²`.
Proof: `n^{-(σ+it)} = n^{-σ₀} · n^{-β} · n^{-it}`; summation by parts
(`∑ x n w n = w N X N + ∑ (w n - w (n+1)) X n`, cf. `sumIcc_byParts`) with the decreasing real
weights `w n = n^{-β} ≤ 1`; then `‖·‖ ≤ ‖X N‖ + ∑ (w n - w (n+1))‖X n‖` and
Cauchy–Schwarz with `∑_{n<N} (w n - w (n+1)) = 1 - N^{-β} ≤ 1`. -/
theorem normCpowAddIt_le_abel (N : ℕ) (hN : 1 ≤ N) (v : ℕ → ℂ) {σ₀ σ t : ℝ} (hσ : σ₀ ≤ σ) :
    ‖∑ n ∈ Finset.Icc 1 N, v n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2
      ≤ 2 * ‖∑ n ∈ Finset.Icc 1 N,
            (v n * ((((n : ℝ) ^ (-σ₀)) : ℝ) : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
        + 2 * ∑ n ∈ Finset.Icc 1 (N - 1),
            ((n : ℝ) ^ (-(σ - σ₀)) - (((n + 1 : ℕ)) : ℝ) ^ (-(σ - σ₀)))
              * ‖∑ k ∈ Finset.Icc 1 n,
                  (v k * ((((k : ℝ) ^ (-σ₀)) : ℝ) : ℂ)) * (k : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2 := by
  let a : ℕ → ℂ := fun n =>
    (v n * ((((n : ℝ) ^ (-σ₀)) : ℝ) : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I))
  let w : ℕ → ℝ := fun n => (n : ℝ) ^ (-(σ - σ₀))
  have habel := abel_norm_sq_bound N hN a w
      (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (fun n hn => by
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        calc w n = (n : ℝ) ^ (-(σ - σ₀)) := rfl
          _ ≤ (n : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ = 1 := Real.rpow_zero _)
      (fun n hn => by
        have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ n)
        show w (n + 1) ≤ w n
        exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith))
  have hLHS : (∑ n ∈ Finset.Icc 1 N, a n * (w n : ℂ))
      = ∑ n ∈ Finset.Icc 1 N, v n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact cpow_factor_neg_sigma_add_it n (Finset.mem_Icc.mp hn).1 (v n) σ₀ σ t
  rw [hLHS] at habel
  exact habel

end Work.ZeroDensity.Montgomery
