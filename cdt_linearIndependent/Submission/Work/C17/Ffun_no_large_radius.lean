/-
# `Ffun_no_large_radius`

Given the sharp lower bound `|F a b n| ≥ c / ((n+1)^5 · xs a b ^ n)` on the coefficients of the
overconvergent Hadamard product `F = E_a ⋆ A_b`, the power series `Σ F a b n · z^n` cannot converge
at any `z = ρ` with `ρ > xs a b`: the terms `F a b n · ρ^n` are of size at least

  `c · (ρ / xs a b)^n / (n+1)^5`,

which is bounded away from `0` (indeed tends to `∞`), so the series diverges.
-/
import Mathlib
import Submission.Work.C17.logP_defs

namespace Work.C17

open Filter
open scoped Topology

/-- For `a, b ≥ 3` the Taylor radius `xs a b = (a+√(a²−1))·(b−√(b²−1))` of the unlikely series is
strictly positive. -/
lemma xs_pos_of_ge_three (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) : 0 < xs a b := by
  unfold xs
  apply mul_pos
  · exact add_pos_of_pos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
  · apply sub_pos.2
    rw [Real.sqrt_lt' (by linarith : (0:ℝ) < b)]
    nlinarith

/-- For `q > 1` and `c > 0`, `n ↦ c · q^n / (n+1)^k` tends to `+∞`. -/
lemma tendsto_const_mul_pow_div_atTop (c q : ℝ) (hc : 0 < c) (hq : 1 < q) (k : ℕ) :
    Tendsto (fun n : ℕ => c * q ^ n / ((n : ℝ) + 1) ^ k) atTop atTop := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hb0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k / q ^ n) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt k hq).comp (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k / q ^ (n+1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
    have h2 : Tendsto (fun n : ℕ => q * (((n : ℝ) + 1) ^ k / q ^ (n+1))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := q)).mul h1
    refine h2.congr' (Eventually.of_forall fun n => ?_)
    rw [pow_succ]
    field_simp
  have hbgt : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k / q ^ n) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hb0, Eventually.of_forall fun n => ?_⟩
    show (0:ℝ) < ((n : ℝ) + 1) ^ k / q ^ n
    positivity
  have hinv := hbgt.inv_tendsto_nhdsGT_zero
  have hinv' : Tendsto (fun n : ℕ => q ^ n / ((n : ℝ) + 1) ^ k) atTop atTop := by
    refine hinv.congr' (Eventually.of_forall fun n => ?_)
    show (((n : ℝ) + 1) ^ k / q ^ n)⁻¹ = q ^ n / ((n : ℝ) + 1) ^ k
    rw [inv_div]
  have h3 := hinv'.const_mul_atTop hc
  refine h3.congr' (Eventually.of_forall fun n => ?_)
  show c * (q ^ n / ((n : ℝ) + 1) ^ k) = c * q ^ n / ((n : ℝ) + 1) ^ k
  rw [mul_div_assoc]

theorem Ffun_no_large_radius (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (c : ℝ) (hc : 0 < c)
    (hlo : ∀ n : ℕ, c / (((n : ℝ) + 1) ^ 5 * (xs a b) ^ n) ≤ |Ffun a b n|)
    {ρ : ℝ} (hρ : xs a b < ρ) :
    ¬ Summable fun n : ℕ => Ffun a b n * ρ ^ n := by
  intro hsum
  have hxs : 0 < xs (a:ℝ) (b:ℝ) :=
    xs_pos_of_ge_three (a:ℝ) (b:ℝ) (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hρ0 : 0 < ρ := lt_trans hxs hρ
  have hq : 1 < ρ / xs a b := (one_lt_div hxs).2 hρ
  -- if the series converged, its terms would tend to `0` in absolute value
  have habs : Tendsto (fun n : ℕ => |Ffun a b n * ρ ^ n|) atTop (𝓝 0) := by
    simpa using hsum.tendsto_atTop_zero.abs
  -- but they are bounded below by a quantity that tends to `∞`
  have hg := tendsto_const_mul_pow_div_atTop c (ρ / xs a b) hc hq 5
  have hge_aux : ∀ n : ℕ, c * (ρ / xs a b) ^ n / ((n : ℝ) + 1) ^ 5
      ≤ |Ffun a b n * ρ ^ n| := by
    intro n
    have h1 := hlo n
    have hρn : (0:ℝ) ≤ ρ ^ n := by positivity
    calc c * (ρ / xs a b) ^ n / ((n : ℝ) + 1) ^ 5
        = c / (((n : ℝ) + 1) ^ 5 * (xs a b) ^ n) * ρ ^ n := by
          rw [div_pow]
          field_simp
      _ ≤ |Ffun a b n| * ρ ^ n := mul_le_mul_of_nonneg_right h1 hρn
      _ = |Ffun a b n * ρ ^ n| := by rw [abs_mul, abs_of_nonneg hρn]
  have hge1 : ∀ᶠ n : ℕ in atTop, (1:ℝ) ≤ |Ffun a b n * ρ ^ n| :=
    ((tendsto_atTop.1 hg) 1).mono fun n hn => le_trans hn (hge_aux n)
  have hlt1 : ∀ᶠ n : ℕ in atTop, |Ffun a b n * ρ ^ n| < 1 := by
    have := (Metric.tendsto_nhds.mp habs) 1 zero_lt_one
    simpa [Real.dist_eq] using this
  obtain ⟨n, hn⟩ := (hge1.and hlt1).exists
  exact absurd hn.2 (not_lt.mpr hn.1)

end Work.C17
