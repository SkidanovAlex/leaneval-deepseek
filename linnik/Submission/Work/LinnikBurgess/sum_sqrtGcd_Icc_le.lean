import Mathlib
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos

namespace Work.LinnikBurgess

open Finset

/-- **Auxiliary bound.** For `g ≥ 1`, `√g ≤ g` (as reals). -/
private lemma sqrt_le_self_of_one_le {g : ℝ} (hg : 1 ≤ g) : Real.sqrt g ≤ g := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [sq_nonneg (g - 1), hg]

/-- The sum of `√(gcd m t)` over `t ∈ [1, N]` is at most `N · τ(m)`: pointwise `√(gcd m t) ≤ gcd m t`
(since `gcd m t ≥ 1`), and `∑_{t ∈ [1,N]} gcd m t ≤ N · τ(m)` by the elliptic-counting bound
`Commons.NumberTheory.Divisors.sum_gcd_le_of_pos`. -/
theorem sum_sqrtGcd_Icc_le (m N : ℕ) (hm : 0 < m) : (∑ t ∈ Finset.Icc 1 N, Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ)) ≤ (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
  have hpt : ∀ t ∈ Finset.Icc 1 N,
      Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ) ≤ (((Nat.gcd m t : ℕ)) : ℝ) := by
    intro t _
    have hpos : 0 < Nat.gcd m t := Nat.gcd_pos_of_pos_left t hm
    have hg1 : (1 : ℝ) ≤ (((Nat.gcd m t : ℕ)) : ℝ) := by
      have : 1 ≤ Nat.gcd m t := by omega
      exact_mod_cast this
    exact sqrt_le_self_of_one_le hg1
  have hnat : ∑ t ∈ Finset.Icc 1 N, Nat.gcd m t ≤ N * m.divisors.card := by
    calc ∑ t ∈ Finset.Icc 1 N, Nat.gcd m t
        = ∑ t ∈ Finset.Icc 1 N, Nat.gcd t m :=
          Finset.sum_congr rfl (fun t _ => Nat.gcd_comm m t)
      _ ≤ N * m.divisors.card := Commons.NumberTheory.Divisors.sum_gcd_le_of_pos N m hm
  calc ∑ t ∈ Finset.Icc 1 N, Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ)
      ≤ ∑ t ∈ Finset.Icc 1 N, (((Nat.gcd m t : ℕ)) : ℝ) := Finset.sum_le_sum hpt
    _ = ((∑ t ∈ Finset.Icc 1 N, Nat.gcd m t : ℕ) : ℝ) :=
        (Nat.cast_sum (Finset.Icc 1 N) (fun t => Nat.gcd m t)).symm
    _ ≤ ((N * m.divisors.card : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by push_cast; ring

end Work.LinnikBurgess
