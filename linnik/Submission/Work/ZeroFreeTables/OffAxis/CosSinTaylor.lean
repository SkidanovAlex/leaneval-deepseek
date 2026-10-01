import Mathlib

namespace Work.ZeroFreeTables.OffAxis

open Finset

/-- Helper: a sum over `range (2*n)` can be decomposed into even and odd indices. -/
lemma sum_pair (f : ℕ → ℝ) : ∀ n, ∑ k ∈ Finset.range (2*n), f k
    = ∑ j ∈ Finset.range n, (f (2*j) + f (2*j+1))
  | 0 => by simp
  | n+1 => by
    rw [show 2*(n+1) = 2*n+2 from rfl]
    rw [show 2*n+2 = (2*n+1)+1 from rfl, Finset.sum_range_succ]
    rw [show 2*n+1 = (2*n)+1 from rfl, Finset.sum_range_succ]
    rw [sum_pair f n]
    rw [Finset.sum_range_succ]
    ring

/-- Helper: if all odd-indexed terms vanish, a sum over `range (2*n)` is a sum over the even
indices. -/
lemma sum_odd_zero (f : ℕ → ℝ) (hf : ∀ j, f (2*j+1) = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n), f k = ∑ j ∈ Finset.range n, f (2*j) := by
  rw [sum_pair f n]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hf j, add_zero]

/-- Helper: if all even-indexed terms vanish, a sum over `range (2*n+1)` is a sum over the odd
indices. -/
lemma sum_even_zero (f : ℕ → ℝ) (hf : ∀ j, f (2*j) = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n+1), f k = ∑ j ∈ Finset.range n, f (2*j+1) := by
  rw [show 2*n+1 = (2*n)+1 from rfl, Finset.sum_range_succ]
  rw [hf n, add_zero, sum_pair f n]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hf j, zero_add]

/-- The derivatives within `Icc 0 x` at `0` agree with the ordinary derivatives. -/
lemma iteratedDerivWithin_cos (x : ℝ) (hx : 0 < x) (k : ℕ) :
    iteratedDerivWithin k Real.cos (Set.Icc 0 x) 0 = iteratedDeriv k Real.cos 0 :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx) (Real.contDiff_cos.contDiffAt)
    (Set.left_mem_Icc.mpr hx.le)

lemma iteratedDerivWithin_sin (x : ℝ) (hx : 0 < x) (k : ℕ) :
    iteratedDerivWithin k Real.sin (Set.Icc 0 x) 0 = iteratedDeriv k Real.sin 0 :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx) (Real.contDiff_sin.contDiffAt)
    (Set.left_mem_Icc.mpr hx.le)

/-- Values of the higher derivatives of `cos` and `sin` at `0`. -/
lemma iteratedDeriv_cos_even (j : ℕ) : iteratedDeriv (2*j) Real.cos 0 = (-1)^j := by
  rw [Real.iteratedDeriv_even_cos]; simp

lemma iteratedDeriv_cos_odd (j : ℕ) : iteratedDeriv (2*j+1) Real.cos 0 = 0 := by
  rw [Real.iteratedDeriv_odd_cos]; simp

lemma iteratedDeriv_sin_even (j : ℕ) : iteratedDeriv (2*j) Real.sin 0 = 0 := by
  rw [Real.iteratedDeriv_even_sin]; simp

lemma iteratedDeriv_sin_odd (j : ℕ) : iteratedDeriv (2*j+1) Real.sin 0 = (-1)^j := by
  rw [Real.iteratedDeriv_odd_sin]; simp

/-- The Taylor polynomial of `cos` of degree `2*n+1` at `0` equals the truncated power series. -/
lemma taylorWithinEval_cos (x : ℝ) (hx : 0 < x) (n : ℕ) :
    taylorWithinEval Real.cos (2*n+1) (Set.Icc 0 x) 0 x
      = ∑ k ∈ Finset.range (n+1), (-1)^k * x^(2*k) / (Nat.factorial (2*k) : ℝ) := by
  rw [taylor_within_apply]
  rw [show 2*n+1+1 = 2*(n+1) from rfl]
  rw [sum_odd_zero (fun k => ((↑k.factorial)⁻¹ * (x - 0) ^ k) •
      iteratedDerivWithin k Real.cos (Set.Icc 0 x) 0) ?_ (n+1)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [iteratedDerivWithin_cos x hx, iteratedDeriv_cos_even j]
    simp only [sub_zero, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm ((-1:ℝ)^j)]
    ring
  · intro j
    rw [iteratedDerivWithin_cos x hx, iteratedDeriv_cos_odd j]
    simp

/-- The Taylor polynomial of `sin` of degree `2*n` at `0` equals the truncated power series. -/
lemma taylorWithinEval_sin (x : ℝ) (hx : 0 < x) (n : ℕ) :
    taylorWithinEval Real.sin (2*n) (Set.Icc 0 x) 0 x
      = ∑ k ∈ Finset.range n, (-1)^k * x^(2*k+1) / (Nat.factorial (2*k+1) : ℝ) := by
  rw [taylor_within_apply]
  rw [sum_even_zero (fun k => ((↑k.factorial)⁻¹ * (x - 0) ^ k) •
      iteratedDerivWithin k Real.sin (Set.Icc 0 x) 0) ?_ n]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [iteratedDerivWithin_sin x hx, iteratedDeriv_sin_odd j]
    simp only [sub_zero, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm ((-1:ℝ)^j)]
    ring
  · intro j
    rw [iteratedDerivWithin_sin x hx, iteratedDeriv_sin_even j]
    simp

/-- Taylor remainder estimate for `sin` with the "next term" bound. -/
lemma sin_taylor_bound (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.sin x - ∑ k ∈ Finset.range n,
        (-1 : ℝ)^k * x^(2*k+1) / (Nat.factorial (2*k+1) : ℝ)|
      ≤ x^(2*n+1) / (Nat.factorial (2*n+1) : ℝ) := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.sin) (x := x) (x₀ := 0)
      (n := 2*n) (ne_of_lt hx) (Real.contDiff_sin.contDiffOn) with ⟨x', hx', heq⟩
  rw [Set.uIcc_of_le hx.le] at heq
  rw [taylorWithinEval_sin x hx n] at heq
  rw [heq]
  have hb : |iteratedDeriv (2*n+1) Real.sin x'| ≤ 1 := by
    rw [Real.iteratedDeriv_odd_sin]
    simp only [Pi.mul_apply, abs_mul]
    simp [Real.abs_cos_le_one]
  have hfac : (0:ℝ) < (Nat.factorial (2*n+1) : ℝ) := by positivity
  rw [abs_div, abs_mul, sub_zero, abs_of_nonneg (pow_nonneg hx.le (2*n+1)), abs_of_pos hfac]
  calc |iteratedDeriv (2*n+1) Real.sin x'| * x^(2*n+1) / (↑(2*n+1).factorial)
      ≤ 1 * x^(2*n+1) / (↑(2*n+1).factorial) := by gcongr
    _ = x^(2*n+1) / (↑(2*n+1).factorial) := by ring

/-- Taylor remainder estimate for `cos` with the "next term" bound. -/
lemma cos_taylor_bound (x : ℝ) (hx : 0 < x) (m : ℕ) :
    |Real.cos x - ∑ k ∈ Finset.range (m+1),
        (-1 : ℝ)^k * x^(2*k) / (Nat.factorial (2*k) : ℝ)|
      ≤ x^(2*(m+1)) / (Nat.factorial (2*(m+1)) : ℝ) := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.cos) (x := x) (x₀ := 0)
      (n := 2*m+1) (ne_of_lt hx) (Real.contDiff_cos.contDiffOn) with ⟨x', hx', heq⟩
  rw [Set.uIcc_of_le hx.le] at heq
  rw [taylorWithinEval_cos x hx m] at heq
  rw [heq]
  have hb : |iteratedDeriv (2*m+1+1) Real.cos x'| ≤ 1 := by
    rw [show 2*m+1+1 = 2*(m+1) from rfl, Real.iteratedDeriv_even_cos]
    simp only [Pi.mul_apply, abs_mul]
    simp [Real.abs_cos_le_one]
  have hfac : (0:ℝ) < (Nat.factorial (2*m+1+1) : ℝ) := by positivity
  rw [abs_div, abs_mul, sub_zero, abs_of_nonneg (pow_nonneg hx.le (2*m+1+1)), abs_of_pos hfac]
  calc |iteratedDeriv (2*m+1+1) Real.cos x'| * x^(2*m+1+1) / (↑(2*m+1+1).factorial)
      ≤ 1 * x^(2*m+1+1) / (↑(2*m+1+1).factorial) := by gcongr
    _ = x^(2*(m+1)) / (↑(2*(m+1)).factorial) := by rw [one_mul]; rfl

theorem CosSinTaylor (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    |Real.cos x - ∑ k ∈ Finset.range n, (-1 : ℝ)^k * x^(2*k) / (Nat.factorial (2*k) : ℝ)|
        ≤ x^(2*n) / (Nat.factorial (2*n) : ℝ)
      ∧ |Real.sin x - ∑ k ∈ Finset.range n, (-1 : ℝ)^k * x^(2*k+1) / (Nat.factorial (2*k+1) : ℝ)|
        ≤ x^(2*n+1) / (Nat.factorial (2*n+1) : ℝ) := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0]
    refine ⟨?_, ?_⟩
    · rcases n with _ | m
      · simp
      · rw [Finset.sum_range_succ']
        have hzero : ∀ k : ℕ, (-1 : ℝ)^(k+1) * (0:ℝ)^(2*(k+1)) /
            (Nat.factorial (2*(k+1)) : ℝ) = 0 := by
          intro k; rw [zero_pow (by positivity : 2*(k+1) ≠ 0), mul_zero, zero_div]
        simp only [hzero, Finset.sum_const_zero, zero_add]
        simp
    · simp
  · refine ⟨?_, sin_taylor_bound x hxpos n⟩
    rcases n with _ | m
    · simpa using Real.abs_cos_le_one x
    · exact cos_taylor_bound x hxpos m

end Work.ZeroFreeTables.OffAxis
