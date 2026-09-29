import Mathlib
import Submission.Work.CLift.analytic

/-!
# Area CLift — `U₀` and `U₁` are analytic, with derivatives `U₁` and `U₂`

This file proves `Work.CLift.hasDerivAt_U`: on the disc `‖x‖ < 1/2` the analytic function
`U₀ = Σ_k c_k x^k` (defined from the power series `P` of Theorem C) has derivative `U₁`, and
`U₁` has derivative `U₂`.

The proof is via the general term-by-term differentiation result for series of functions
`Mathlib.Analysis.Calculus.SmoothSeries.hasDerivAt_tsum_of_isPreconnected`, applied to
`g n z = c n * z ^ n` on a ball of radius `r` with `‖x‖ < r < 2/3`.  The only input is the
coefficient growth bound `‖c k‖ ≤ C * (3/2)^k` furnished by `coef_bound`.
-/

namespace Work.CLift

open Work.CLift Submission.CDTPlan
open scoped BigOperators

/-- Reindexing a summable series with vanishing zeroth term:
`∑' n, f n = ∑' n, f (n+1)` when `f 0 = 0`. -/
lemma tsum_succ_of_zero {f : ℕ → ℂ} (hf : Summable f) (h0 : f 0 = 0) :
    (∑' n, f n) = ∑' n, f (n + 1) := by
  rw [Summable.tsum_eq_zero_add hf, h0, zero_add]

/-- Term-by-term differentiation of a power series `∑' k, c k * z ^ k` whose coefficients grow
at most like `C * (k+1)^d * (3/2)^k`.  The derivative is `∑' k, (k+1) * c (k+1) * z ^ k`. -/
lemma hasDerivAt_tsum_pow (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hbound : ∀ k, ‖c k‖ ≤ C * ((k : ℝ) + 1) ^ d * (3 / 2) ^ k)
    {x : ℂ} (hx : ‖x‖ < 2 / 3) :
    HasDerivAt (fun z => ∑' k : ℕ, c k * z ^ k)
      (∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * x ^ k) x := by
  -- `((n:ℝ)+1)^d ≤ 2^d * (n:ℝ)^d` for `n ≥ 1`
  have hkey : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) + 1) ^ d ≤ (2:ℝ)^d * (n:ℝ)^d := by
    intro n hn1
    have h2n : (n:ℝ) + 1 ≤ 2 * (n:ℝ) := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith
    calc ((n : ℝ) + 1) ^ d ≤ (2 * (n:ℝ)) ^ d := pow_le_pow_left₀ (by positivity) h2n d
      _ = (2:ℝ)^d * (n:ℝ)^d := by rw [mul_pow]
  -- the radius of the disc of convergence we use
  let r : ℝ := (‖x‖ + 2 / 3) / 2
  have hxr : ‖x‖ < r := by
    show ‖x‖ < (‖x‖ + 2 / 3) / 2
    linarith [norm_nonneg x]
  have hr23 : r < 2 / 3 := by
    show (‖x‖ + 2 / 3) / 2 < 2 / 3
    linarith [norm_nonneg x]
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  let q : ℝ := (3 / 2) * r
  have hq0 : 0 ≤ q := by
    show 0 ≤ (3/2) * r
    positivity
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    show (3/2) * r < 1
    linarith
  -- the summable majorant for the derivative series
  have huQ : Summable (fun n : ℕ => (n : ℝ) ^ (d + 1) * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (d + 1) hq1
  have hu : Summable (fun n : ℕ => C * r⁻¹ * (2:ℝ) ^ d * (n : ℝ) ^ (d + 1) * q ^ n) := by
    refine (huQ.mul_left (C * r⁻¹ * (2:ℝ)^d)).congr (fun n => ?_)
    ring
  -- the key algebraic identity expressing the majorant
  have hpow : ∀ n : ℕ, 1 ≤ n →
      C * ((2:ℝ)^d * (n:ℝ)^d) * (3/2)^n * ((n:ℝ) * r^(n-1))
        = C * r⁻¹ * (2:ℝ)^d * (n:ℝ)^(d+1) * q^n := by
    intro n hn1
    have hrn : r ^ n = r ^ (n - 1) * r := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [pow_succ]
    have hqn : q ^ n = (3 / 2) ^ n * (r ^ (n - 1) * r) := by
      rw [show q = (3/2)*r from rfl, mul_pow, hrn]
    rw [hqn, pow_succ]
    field_simp
  -- uniform bound on the derivatives on the disc of radius `r`
  have hbound' : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      ‖c n * ((n : ℂ) * y ^ (n - 1))‖ ≤ C * r⁻¹ * (2:ℝ)^d * (n : ℝ) ^ (d + 1) * q ^ n := by
    intro n y hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [zero_pow (Nat.succ_ne_zero d)]
    · have hn1 : 1 ≤ n := hn
      have hyn : ‖y‖ ^ (n - 1) ≤ r ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg y) hy.le (n - 1)
      calc ‖c n * ((n : ℂ) * y ^ (n - 1))‖
          = ‖c n‖ * ((n:ℝ) * ‖y‖^(n-1)) := by
            rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
        _ ≤ (C * ((n:ℝ)+1)^d * (3/2)^n) * ((n:ℝ) * r^(n-1)) :=
            mul_le_mul (hbound n) (mul_le_mul_of_nonneg_left hyn (by positivity))
              (by positivity) (by positivity)
        _ ≤ (C * ((2:ℝ)^d * (n:ℝ)^d) * (3/2)^n) * ((n:ℝ) * r^(n-1)) := by
            gcongr
            exact hkey n hn1
        _ = C * r⁻¹ * (2:ℝ)^d * (n:ℝ)^(d+1) * q ^ n := hpow n hn1
  -- term-by-term differentiation on the disc
  have hderiv : HasDerivAt (fun z : ℂ => ∑' k : ℕ, c k * z ^ k)
      (∑' k : ℕ, c k * ((k : ℂ) * x ^ (k - 1))) x := by
    refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0:ℂ) r) (y₀ := 0)
      (u := fun n : ℕ => C * r⁻¹ * (2:ℝ) ^ d * (n : ℝ) ^ (d + 1) * q ^ n)
      hu Metric.isOpen_ball (convex_ball (0:ℂ) r).isPreconnected ?_ hbound' ?_ ?_ ?_
    · intro n y hy
      exact (hasDerivAt_pow n y).const_mul (c n)
    · simpa using hr0
    · refine summable_of_ne_finset_zero (s := {0}) ?_
      intro n hn
      simp only [Finset.mem_singleton] at hn
      rw [zero_pow hn, mul_zero]
    · simpa using hxr
  -- summability of the derivative series at `x`, needed for the reindexing
  have hf : Summable fun n : ℕ => c n * ((n : ℂ) * x ^ (n - 1)) := by
    refine Summable.of_norm_bounded hu (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [zero_pow (Nat.succ_ne_zero d)]
    · have hn1 : 1 ≤ n := hn
      have hxn : ‖x‖ ^ (n - 1) ≤ r ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg x) hxr.le (n - 1)
      calc ‖c n * ((n : ℂ) * x ^ (n - 1))‖
          = ‖c n‖ * ((n:ℝ) * ‖x‖^(n-1)) := by
            rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
        _ ≤ (C * ((n:ℝ)+1)^d * (3/2)^n) * ((n:ℝ) * r^(n-1)) :=
            mul_le_mul (hbound n) (mul_le_mul_of_nonneg_left hxn (by positivity))
              (by positivity) (by positivity)
        _ ≤ (C * ((2:ℝ)^d * (n:ℝ)^d) * (3/2)^n) * ((n:ℝ) * r^(n-1)) := by
            gcongr
            exact hkey n hn1
        _ = C * r⁻¹ * (2:ℝ)^d * (n:ℝ)^(d+1) * q^n := hpow n hn1
  -- reindex the derivative series
  have h2 : (∑' k : ℕ, c k * ((k : ℂ) * x ^ (k - 1))) =
      ∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * x ^ k := by
    rw [tsum_succ_of_zero hf (by simp)]
    apply tsum_congr
    intro n
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  simpa only [h2] using hderiv

theorem hasDerivAt_U (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    HasDerivAt (U0 m n ra rb rab r0) (U1 m n ra rb rab r0 x) x ∧
      HasDerivAt (U1 m n ra rb rab r0) (U2 m n ra rb rab r0 x) x := by
  obtain ⟨C, hC0, hC⟩ := coef_bound m n ra rb rab r0 hR hAdm hRel
  have hx23 : ‖x‖ < 2 / 3 := by linarith
  refine ⟨?_, ?_⟩
  · exact hasDerivAt_tsum_pow (coef m n ra rb rab r0) C hC0 0
      (fun k => by simpa using hC k) hx23
  · set c' : ℕ → ℂ := fun k => ((k : ℂ) + 1) * coef m n ra rb rab r0 (k + 1) with hc'
    have hb : ∀ k : ℕ, ‖c' k‖ ≤ C * (3 / 2) * ((k : ℝ) + 1) ^ 1 * (3 / 2) ^ k := by
      intro k
      rw [hc', norm_mul, norm_add_one]
      calc ((k:ℝ)+1) * ‖coef m n ra rb rab r0 (k+1)‖
          ≤ ((k:ℝ)+1) * (C * (3/2)^(k+1)) :=
            mul_le_mul_of_nonneg_left (hC (k+1)) (by positivity)
        _ = C * (3/2) * ((k:ℝ)+1)^1 * (3/2)^k := by ring
    have h := hasDerivAt_tsum_pow c' (C * (3/2)) (by positivity) 1 hb hx23
    have hfun : (fun z : ℂ => ∑' k : ℕ, c' k * z ^ k) = U1 m n ra rb rab r0 := by
      funext z
      rw [U1]
    have hder : (∑' k : ℕ, ((k : ℂ) + 1) * c' (k + 1) * x ^ k) = U2 m n ra rb rab r0 x := by
      rw [U2]
      apply tsum_congr
      intro k
      simp only [hc']
      have hk : k + 1 + 1 = k + 2 := by omega
      rw [hk]
      push_cast
      ring
    rw [hfun, hder] at h
    exact h

end Work.CLift
