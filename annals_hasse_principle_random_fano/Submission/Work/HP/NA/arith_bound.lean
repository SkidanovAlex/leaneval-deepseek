import Mathlib
import Submission.Work.HP.NA.arith_term_bound

namespace Work.HP.NA

/-- Geometric domination: the summand `p^(2e + (r-e)(n+1))` decays by a factor
`p^(n-1) ≥ 2` at each step in `e`, so the sum over `e ∈ [1,r]` is at most twice
its first term. -/
private theorem arith_bound_geom (p r n : ℕ) (hp : p.Prime) (hn : 2 ≤ n) (hr : 1 ≤ r) :
    (∑ e ∈ Finset.Ico 1 (r + 1), (p : ℝ) ^ (2 * e + (r - e) * (n + 1)))
      ≤ 2 * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hn1 : 1 ≤ n - 1 := by omega
  have hPn : (2 : ℝ) ≤ (p : ℝ) ^ (n - 1) := by
    calc (2:ℝ) ≤ (p:ℝ) := hP2
      _ = (p:ℝ)^1 := by rw [pow_one]
      _ ≤ (p:ℝ)^(n-1) := pow_le_pow_right₀ hP1 hn1
  -- ratio of two consecutive summands is at most `1/2`
  have step : ∀ e, e + 1 ≤ r →
      (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1))
        ≤ (1 / 2) * (p : ℝ) ^ (2 * e + (r - e) * (n + 1)) := by
    intro e he
    have hidx : (r - e) * (n + 1) = (r - (e + 1)) * (n + 1) + (n + 1) := by
      have h1 : r - (e + 1) + 1 = r - e := by omega
      rw [← h1, add_mul, one_mul]
    have hexp : 2 * e + (r - e) * (n + 1)
        = (2 * (e + 1) + (r - (e + 1)) * (n + 1)) + (n - 1) := by
      rw [hidx]
      set A := (r - (e + 1)) * (n + 1)
      have hn1' : n - 1 + 1 = n := by omega
      omega
    have hpow : (p : ℝ) ^ (2 * e + (r - e) * (n + 1))
        = (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1)) * (p : ℝ) ^ (n - 1) := by
      rw [hexp, pow_add]
    rw [hpow]
    have hnonneg : (0 : ℝ) ≤ (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1)) :=
      pow_nonneg (by positivity) _
    have h2 : 2 * (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1))
        ≤ (p : ℝ) ^ (n - 1) * (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1)) :=
      mul_le_mul_of_nonneg_right hPn hnonneg
    calc (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1))
        = (1/2) * (2 * (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1))) := by ring
      _ ≤ (1/2) * ((p : ℝ) ^ (n - 1) * (p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1))) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (1/2) * ((p : ℝ) ^ (2 * (e + 1) + (r - (e + 1)) * (n + 1)) * (p : ℝ) ^ (n - 1)) := by ring
  -- pointwise geometric bound
  have key : ∀ i, i + 1 ≤ r →
      (p : ℝ) ^ (2 * (i + 1) + (r - (i + 1)) * (n + 1))
        ≤ (1 / 2) ^ i * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hle
      have hle' : i + 1 ≤ r := by omega
      have hih := ih hle'
      have hst := step (i + 1) hle
      calc (p : ℝ) ^ (2 * (i + 1 + 1) + (r - (i + 1 + 1)) * (n + 1))
          ≤ (1 / 2) * (p : ℝ) ^ (2 * (i + 1) + (r - (i + 1)) * (n + 1)) := hst
        _ ≤ (1 / 2) * ((1 / 2) ^ i * (p : ℝ) ^ (2 + (r - 1) * (n + 1))) :=
            mul_le_mul_of_nonneg_left hih (by norm_num)
        _ = (1 / 2) ^ (i + 1) * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
            rw [pow_succ]; ring
  rw [Finset.sum_Ico_eq_sum_range, show (r + 1) - 1 = r by omega]
  have hbound : ∀ k ∈ Finset.range r,
      (p : ℝ) ^ (2 * (1 + k) + (r - (1 + k)) * (n + 1))
        ≤ (1 / 2) ^ k * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
    intro k hk
    have hkr : k + 1 ≤ r := by
      simp only [Finset.mem_range] at hk; omega
    rw [show (1 + k) = (k + 1) by omega]
    exact key k hkr
  calc ∑ k ∈ Finset.range r, (p : ℝ) ^ (2 * (1 + k) + (r - (1 + k)) * (n + 1))
      ≤ ∑ k ∈ Finset.range r, (1 / 2) ^ k * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) :=
        Finset.sum_le_sum hbound
    _ = (∑ k ∈ Finset.range r, (1 / 2) ^ k) * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
        apply mul_le_mul_of_nonneg_right (sum_geometric_two_le r)
        positivity

/-- The right-hand side rewrites to `4 * p^(2 + (r-1)(n+1))`, so the factor `2`
from the geometric estimate is harmless. -/
private theorem arith_bound_rhs (p r n : ℕ) (hp : p.Prime) (hn : 2 ≤ n) (hr : 1 ≤ r) :
    2 * (p : ℝ) ^ (2 + (r - 1) * (n + 1))
      ≤ (p : ℝ) ^ (r * (n + 1)) * (4 / (p : ℝ) ^ (n - 1)) := by
  have hidx : r * (n + 1) = (2 + (r - 1) * (n + 1)) + (n - 1) := by
    have h1 : r = (r - 1) + 1 := by omega
    have h2 : n + 1 = 2 + (n - 1) := by omega
    conv_lhs => rw [h1]
    rw [add_mul, one_mul]
    omega
  have hmain : (p : ℝ) ^ (r * (n + 1)) * (4 / (p : ℝ) ^ (n - 1))
      = 4 * (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by
    rw [hidx, pow_add]
    have hne : (p : ℝ) ^ (n - 1) ≠ 0 := by
      apply pow_ne_zero
      exact_mod_cast (ne_of_gt hp.pos)
    field_simp
  rw [hmain]
  have hnn : (0:ℝ) ≤ (p : ℝ) ^ (2 + (r - 1) * (n + 1)) := by positivity
  linarith

theorem arith_bound (p r n : ℕ) (hp : p.Prime) (hn : 2 ≤ n) (hr : 1 ≤ r) :
    (∑ e ∈ Finset.Ico 1 (r + 1),
        ((p ^ e - p ^ (e - 1) : ℕ) : ℝ) * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ))
      ≤ (p : ℝ) ^ (r * (n + 1)) * (4 / (p : ℝ) ^ (n - 1)) := by
  have h1 := Finset.sum_le_sum (fun e he => arith_term_bound p r n e hp hn he)
  have h2 := arith_bound_geom p r n hp hn hr
  have h3 := arith_bound_rhs p r n hp hn hr
  exact le_trans h1 (le_trans h2 h3)

end Work.HP.NA
