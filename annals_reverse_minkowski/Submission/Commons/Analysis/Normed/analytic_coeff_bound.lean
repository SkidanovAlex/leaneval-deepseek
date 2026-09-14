import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Normed.Module.HahnBanach
import Submission.Commons.Analysis.Polynomial.bernstein_deriv_sqrt_le

/-!
# A quantitative bound on the first Taylor coefficient

We prove `Commons.Analysis.Normed.analytic_coeff_bound`: if `x : ℕ → B` is a sequence in a real
Banach space with `‖x k‖ ≤ C` for all `k`, and the power series `∑ k, ρ^k • x k` is bounded by `1`
on the real interval `[-1/2, 1/2]`, then `‖x 1‖ ≤ 4 (1 + log C / log 2)`.

The proof is the classical "truncate + Bernstein" argument:

* truncating the series at degree `n` leaves the polynomial `∑_{k ≤ n} ρ^k • x k`, which is bounded
  by `1 + C·(1/2)^n` on `[-1/2, 1/2]`;
* Bernstein's inequality for polynomials bounded by `M` on `[-1, 1]`,
  `|p'(0)| ≤ n·M`, applied (after rescaling and using Hahn–Banach to pass to scalars) gives
  `‖x 1‖ ≤ 2n(1 + C·(1/2)^n)`;
* choosing `n ≈ log₂ C` yields the claim.

The two reusable ingredients are exposed below as `trunc_norm_le` (the truncation bound) and
`poly_coeff_bound` (a Banach-valued form of Bernstein's inequality at the origin).
-/

open Polynomial Finset

namespace Commons.Analysis.Normed

section PolynomialAux

/-- Evaluation of a sum of monomials `∑ k ∈ s, C (c k) * X^k`. -/
lemma eval_sum_C_mul_X_pow (c : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    (∑ k ∈ s, Polynomial.C (c k) * Polynomial.X ^ k).eval t = ∑ k ∈ s, c k * t ^ k := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Polynomial.eval_mul]

/-- The coefficient of a sum of monomials `∑ k ∈ s, C (c k) * X^k`. -/
lemma coeff_sum_C_mul_X_pow (c : ℕ → ℝ) (s : Finset ℕ) (m : ℕ) :
    (∑ k ∈ s, Polynomial.C (c k) * Polynomial.X ^ k).coeff m
      = ∑ k ∈ s, (if m = k then c k else 0) := by
  rw [← Polynomial.lcoeff_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]

/-- The coefficient of `X ^ 1` of `∑ k ∈ range (n+1), C (c k) * X^k` is `c 1`, for `1 ≤ n`. -/
lemma coeff_one_sum_C_mul_X_pow (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k).coeff 1 = c 1 := by
  rw [coeff_sum_C_mul_X_pow]
  apply Finset.sum_eq_single 1
  · intro k _ hk1
    rw [if_neg (by omega : ¬ (1 = k))]
  · intro h
    exact absurd (by rw [Finset.mem_range]; omega : 1 ∈ Finset.range (n + 1)) h

/-- The degree of `∑ k ∈ range (n+1), C (c k) * X^k` is at most `n`. -/
lemma natDegree_sum_C_mul_X_pow_le (c : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_sum_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  rw [if_neg (by omega : ¬ (m = k))]

/-- **Bernstein's inequality for Banach-valued polynomials, at the origin.**
If a polynomial `∑_{k ≤ n} ρ^k • y k` is bounded by `M` on `[-1/2, 1/2]`, then its "linear"
coefficient satisfies `‖y 1‖ ≤ 2 n M`. -/
lemma poly_coeff_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (y : ℕ → B) (n : ℕ) (hn : 1 ≤ n) (M : ℝ) (hM : 0 < M)
    (h : ∀ ρ : ℝ, |ρ| ≤ 1 / 2 → ‖∑ k ∈ Finset.range (n + 1), ρ ^ k • y k‖ ≤ M) :
    ‖y 1‖ ≤ 2 * n * M := by
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (y 1)
  set p : Polynomial ℝ :=
    ∑ k ∈ Finset.range (n + 1), Polynomial.C (g (y k) / (M * 2 ^ k)) * Polynomial.X ^ k with hp
  have h_gsmul : ∀ (t : ℝ) (k : ℕ), g ((t/2) ^ k • y k) = (t/2) ^ k * g (y k) := by
    intro t k
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  have h_gsum : ∀ t : ℝ,
      g (∑ k ∈ Finset.range (n + 1), (t/2) ^ k • y k)
        = ∑ k ∈ Finset.range (n + 1), g (y k) * (t/2) ^ k := by
    intro t
    rw [map_sum g (fun k => (t/2) ^ k • y k) (Finset.range (n+1))]
    exact Finset.sum_congr rfl fun k _ => by rw [h_gsmul t k]; ring
  have h_eval : ∀ t : ℝ, |t| ≤ 1 → |∑ k ∈ Finset.range (n + 1), g (y k) * (t/2) ^ k| ≤ M := by
    intro t ht
    have hρ : |t/2| ≤ 1/2 := by
      rw [abs_div, show |(2:ℝ)| = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith [abs_nonneg t]
    have hop := ContinuousLinearMap.le_opNorm g (∑ k ∈ Finset.range (n + 1), (t/2) ^ k • y k)
    have hM' := h (t/2) hρ
    have key : |∑ k ∈ Finset.range (n + 1), g (y k) * (t/2) ^ k|
        = ‖g (∑ k ∈ Finset.range (n + 1), (t/2) ^ k • y k)‖ := by
      rw [Real.norm_eq_abs, h_gsum t]
    calc |∑ k ∈ Finset.range (n + 1), g (y k) * (t/2) ^ k|
        = ‖g (∑ k ∈ Finset.range (n + 1), (t/2) ^ k • y k)‖ := key
      _ ≤ ‖g‖ * ‖∑ k ∈ Finset.range (n + 1), (t/2) ^ k • y k‖ := hop
      _ ≤ 1 * M := mul_le_mul hg1 hM' (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have hp_bound : ∀ t ∈ Set.Icc (-1:ℝ) 1, |p.eval t| ≤ 1 := by
    intro t ht
    have ht1 : |t| ≤ 1 := by rw [abs_le]; exact ⟨ht.1, ht.2⟩
    have hE := h_eval t ht1
    have h_eq : p.eval t = (∑ k ∈ Finset.range (n + 1), g (y k) * (t/2) ^ k) / M := by
      rw [hp, eval_sum_C_mul_X_pow, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [div_pow]; field_simp
    rw [h_eq, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    linarith [hE]
  have hp_deg : p.degree ≤ (n : WithBot ℕ) := by
    rw [← Polynomial.natDegree_le_iff_degree_le, hp]
    exact natDegree_sum_C_mul_X_pow_le (fun k => g (y k) / (M * 2 ^ k)) n
  have hbern : |p.derivative.eval 0| ≤ (n : ℝ) := by
    have := Commons.Analysis.Polynomial.bernstein_deriv_sqrt_le n p hp_deg hp_bound 0
      (by constructor <;> norm_num)
    simpa using this
  have hpderiv : p.derivative.eval 0 = g (y 1) / (M * 2) := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    norm_num
    rw [hp, coeff_one_sum_C_mul_X_pow (fun k => g (y k) / (M * 2 ^ k)) hn]
    norm_num
  have hnorm : g (y 1) = ‖y 1‖ := by simpa using hgx
  have hpderiv_nonneg : 0 ≤ p.derivative.eval 0 := by rw [hpderiv, hnorm]; positivity
  calc ‖y 1‖ = g (y 1) := hnorm.symm
    _ = (M * 2) * (g (y 1) / (M * 2)) := by field_simp
    _ = (M * 2) * p.derivative.eval 0 := by rw [hpderiv]
    _ = (M * 2) * |p.derivative.eval 0| := by rw [abs_of_nonneg hpderiv_nonneg]
    _ ≤ (M * 2) * n := by apply mul_le_mul_of_nonneg_left hbern; positivity
    _ = 2 * n * M := by ring

end PolynomialAux

section Taylor

/-- Tail bound for a bounded sequence: the shifted series is dominated by a geometric series. -/
lemma tsum_shift_norm_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (y : ℕ → B) {C : ℝ} (_hC0 : 0 ≤ C) (hc : ∀ k, ‖y k‖ ≤ C)
    {ρ : ℝ} (hρ : |ρ| ≤ 1/2) (m : ℕ) :
    ‖∑' i : ℕ, ρ ^ (i + m) • y (i + m)‖ ≤ 2 * C * (1/2) ^ m := by
  have hgeo : Summable (fun i : ℕ => (1/2:ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgs : Summable (fun i : ℕ => (C * (1/2) ^ m) * (1/2) ^ i) := Summable.mul_left _ hgeo
  have hg : Summable (fun i : ℕ => C * (1/2) ^ (i + m)) := by
    refine hgs.congr (fun i => ?_)
    rw [pow_add]; ring
  have hle : ∀ i : ℕ, ‖ρ ^ (i + m) • y (i + m)‖ ≤ C * (1/2) ^ (i + m) := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    have h1 : |ρ| ^ (i + m) ≤ (1/2) ^ (i + m) := pow_le_pow_left₀ (abs_nonneg ρ) hρ _
    have h2 : ‖y (i + m)‖ ≤ C := hc _
    calc |ρ| ^ (i + m) * ‖y (i + m)‖ ≤ (1/2) ^ (i + m) * C :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * (1/2) ^ (i + m) := by ring
  have hnormS : Summable (fun i : ℕ => ‖ρ ^ (i + m) • y (i + m)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hle hg
  calc ‖∑' i : ℕ, ρ ^ (i + m) • y (i + m)‖ ≤ ∑' i : ℕ, ‖ρ ^ (i + m) • y (i + m)‖ :=
        norm_tsum_le_tsum_norm hnormS
    _ ≤ ∑' i : ℕ, C * (1/2) ^ (i + m) := Summable.tsum_le_tsum hle hnormS hg
    _ = 2 * C * (1/2) ^ m := by
        have h1 : (fun i : ℕ => C * (1/2) ^ (i + m)) = (fun i : ℕ => (C * (1/2) ^ m) * (1/2) ^ i) := by
          funext i; rw [pow_add]; ring
        rw [h1, Summable.tsum_mul_left (C * (1/2) ^ m) hgeo,
            tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
        ring

/-- Truncation bound: the partial sum `∑_{k ≤ n} ρ^k • y k` is bounded by `1 + C (1/2)^n`. -/
lemma trunc_norm_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (y : ℕ → B) {C : ℝ} (hC0 : 0 ≤ C) (hc : ∀ k, ‖y k‖ ≤ C)
    (hsup : ∀ ρ : ℝ, |ρ| ≤ 1/2 → ‖∑' k : ℕ, ρ ^ k • y k‖ ≤ 1)
    (n : ℕ) {ρ : ℝ} (hρ : |ρ| ≤ 1/2) :
    ‖∑ i ∈ Finset.range (n + 1), ρ ^ i • y i‖ ≤ 1 + C * (1/2) ^ n := by
  have hgeo : Summable (fun i : ℕ => (1/2:ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg : Summable (fun i : ℕ => C * (1/2) ^ i) := Summable.mul_left _ hgeo
  have hle : ∀ i : ℕ, ‖ρ ^ i • y i‖ ≤ C * (1/2) ^ i := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    have h1 : |ρ| ^ i ≤ (1/2) ^ i := pow_le_pow_left₀ (abs_nonneg ρ) hρ _
    have h2 : ‖y i‖ ≤ C := hc _
    calc |ρ| ^ i * ‖y i‖ ≤ (1/2) ^ i * C := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * (1/2) ^ i := by ring
  have hfS : Summable (fun i : ℕ => ρ ^ i • y i) := Summable.of_norm_bounded hg hle
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun i : ℕ => ρ ^ i • y i) (n + 1) hfS
  have htsum_eq : (∑ i ∈ Finset.range (n + 1), ρ ^ i • y i)
      = (∑' i : ℕ, ρ ^ i • y i) - (∑' i : ℕ, ρ ^ (i + (n+1)) • y (i + (n+1))) := by
    rw [eq_sub_iff_add_eq]; exact hsplit
  rw [htsum_eq]
  calc ‖(∑' i : ℕ, ρ ^ i • y i) - (∑' i : ℕ, ρ ^ (i + (n+1)) • y (i + (n+1)))‖
      ≤ ‖∑' i : ℕ, ρ ^ i • y i‖ + ‖∑' i : ℕ, ρ ^ (i + (n+1)) • y (i + (n+1))‖ := norm_sub_le _ _
    _ ≤ 1 + 2 * C * (1/2) ^ (n + 1) :=
        add_le_add (hsup ρ hρ) (tsum_shift_norm_le y hC0 hc hρ (n + 1))
    _ = 1 + C * (1/2) ^ n := by rw [pow_succ]; ring

end Taylor

/-- **Main lemma.** If `x : ℕ → B` takes values of norm at most `C` and the power series
`∑ k, ρ^k • x k` is bounded by `1` for all real `|ρ| ≤ 1/2`, then
`‖x 1‖ ≤ 4 (1 + log C / log 2)`. -/
theorem analytic_coeff_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] (x : ℕ → B) (C : ℝ) (hC : 1 ≤ C)
    (hc : ∀ k : ℕ, ‖x k‖ ≤ C)
    (hsup : ∀ ρ : ℝ, |ρ| ≤ 1/2 → ‖∑' k : ℕ, ρ ^ k • x k‖ ≤ 1) :
    ‖x 1‖ ≤ 4 * (1 + Real.log C / Real.log 2) := by
  have hC0 : 0 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y : ℝ := Real.log C / Real.log 2 with hy
  have hy0 : 0 ≤ y := by
    rw [hy]; exact div_nonneg (Real.log_nonneg hC) (le_of_lt hlog2pos)
  -- Choose the truncation degree.
  obtain ⟨n, hn1, hnub, hnC⟩ :
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ 1 + y ∧ C ≤ (2 : ℝ) ^ n := by
    refine ⟨max 1 ⌈y⌉₊, le_max_left _ _, ?_, ?_⟩
    · have h1 : ((max 1 ⌈y⌉₊ : ℕ) : ℝ) = max (1:ℝ) ((⌈y⌉₊ : ℕ) : ℝ) := by push_cast; rfl
      rw [h1]
      refine max_le (by linarith) ?_
      have := Nat.ceil_lt_add_one hy0
      have : ((⌈y⌉₊ : ℕ) : ℝ) < y + 1 := by exact_mod_cast this
      linarith
    · have hyle : y ≤ ((max 1 ⌈y⌉₊ : ℕ) : ℝ) := by
        have h1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
        have h2 : ((⌈y⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈y⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast (le_max_right 1 ⌈y⌉₊)
        linarith
      have hlogC : Real.log C ≤ ((max 1 ⌈y⌉₊ : ℕ) : ℝ) * Real.log 2 := by
        have hmul := mul_le_mul_of_nonneg_right hyle (le_of_lt hlog2pos)
        have hyeq : y * Real.log 2 = Real.log C := by rw [hy]; field_simp
        rwa [hyeq] at hmul
      have h2n : Real.log ((2:ℝ) ^ (max 1 ⌈y⌉₊)) =
          ((max 1 ⌈y⌉₊ : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 _
      rw [← h2n] at hlogC
      exact (Real.log_le_log_iff hCpos (by positivity)).mp hlogC
  -- The truncation bound with `M = 1 + C (1/2)^n ≤ 2`.
  have htrunc : ∀ ρ : ℝ, |ρ| ≤ 1/2 →
      ‖∑ k ∈ Finset.range (n + 1), ρ ^ k • x k‖ ≤ 1 + C * (1/2) ^ n :=
    fun ρ hρ => trunc_norm_le x hC0 hc hsup n hρ
  have hMpos : 0 < 1 + C * (1/2) ^ n := by positivity
  have hmain := poly_coeff_bound x n hn1 _ hMpos htrunc
  have hCle : C * (1/2) ^ n ≤ 1 := by
    calc C * (1/2) ^ n ≤ (2:ℝ)^n * (1/2)^n :=
          mul_le_mul_of_nonneg_right hnC (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  calc ‖x 1‖ ≤ 2 * n * (1 + C * (1/2) ^ n) := hmain
    _ ≤ 2 * n * 2 := by
        apply mul_le_mul_of_nonneg_left (by linarith) ; positivity
    _ = 4 * n := by ring
    _ ≤ 4 * (1 + y) := by
        apply mul_le_mul_of_nonneg_left hnub; norm_num
    _ = 4 * (1 + Real.log C / Real.log 2) := by rw [hy]

end Commons.Analysis.Normed