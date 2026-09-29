import Mathlib

/-!
# The sharp polynomial bound `‖w ^ n - q₀ ^ n‖ ≤ (c + ρ) ^ n - c ^ n`

If `‖q₀‖ = c` and `‖w - q₀‖ ≤ ρ` (with `ρ ≥ 0`), then the powers of `w` and `q₀`
differ by at most the *exact* increment of the function `t ↦ t ^ n` between `c`
and `c + ρ`.  Equivalently, the bound obtained from the telescoping factorisation

  `w ^ n - q₀ ^ n = (w - q₀) * ∑ i < n, w ^ i * q₀ ^ (n - 1 - i)`

is sharp: each term of the geometric sum is controlled by `(c + ρ) ^ i * c ^ (n - 1 - i)`,
and the resulting sum satisfies the polynomial identity

  `(∑ i < n, (c + ρ) ^ i * c ^ (n - 1 - i)) * ρ = (c + ρ) ^ n - c ^ n`.

This is the estimate used in the Calegari–Dimitrov–Tang linear independence argument.
-/

namespace Work.CNum

theorem norm_pow_sub_pow_le_sharp {w q₀ : ℂ} {c ρ : ℝ} (hρ : 0 ≤ ρ) (hq0 : ‖q₀‖ = c)
    (hwq : ‖w - q₀‖ ≤ ρ) (n : ℕ) :
    ‖w ^ n - q₀ ^ n‖ ≤ (c + ρ) ^ n - c ^ n := by
  have hc : 0 ≤ c := by rw [← hq0]; exact norm_nonneg q₀
  -- `w` lies in the disc of radius `c + ρ` about the origin.
  have hw : ‖w‖ ≤ c + ρ := by
    calc ‖w‖ ≤ ‖w - q₀‖ + ‖q₀‖ := by simpa using norm_add_le (w - q₀) q₀
      _ ≤ ρ + c := add_le_add hwq (le_of_eq hq0)
      _ = c + ρ := by ring
  -- Telescoping (geometric-sum) factorisation of the difference of powers.
  have hid : (∑ i ∈ Finset.range n, w ^ i * q₀ ^ (n - 1 - i)) * (w - q₀) = w ^ n - q₀ ^ n :=
    (Commute.all w q₀).geom_sum₂_mul n
  -- Termwise bound on the geometric sum, using the two radii `c + ρ` and `c`.
  have hS : ‖∑ i ∈ Finset.range n, w ^ i * q₀ ^ (n - 1 - i)‖
      ≤ ∑ i ∈ Finset.range n, (c + ρ) ^ i * c ^ (n - 1 - i) := by
    calc ‖∑ i ∈ Finset.range n, w ^ i * q₀ ^ (n - 1 - i)‖
        ≤ ∑ i ∈ Finset.range n, ‖w ^ i * q₀ ^ (n - 1 - i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range n, ‖w‖ ^ i * ‖q₀‖ ^ (n - 1 - i) := by simp [norm_pow]
      _ ≤ ∑ i ∈ Finset.range n, (c + ρ) ^ i * c ^ (n - 1 - i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg w) hw i) ?_ ?_ ?_
          · rw [hq0]
          · positivity
          · positivity
  -- The real geometric identity: the sum times `ρ` is the exact increment.
  have hgeo : (∑ i ∈ Finset.range n, (c + ρ) ^ i * c ^ (n - 1 - i)) * ρ
      = (c + ρ) ^ n - c ^ n := by
    have h := (Commute.all (c + ρ) c).geom_sum₂_mul n
    rwa [show (c + ρ) - c = ρ by ring] at h
  calc ‖w ^ n - q₀ ^ n‖
      = ‖(∑ i ∈ Finset.range n, w ^ i * q₀ ^ (n - 1 - i)) * (w - q₀)‖ := by rw [hid]
    _ = ‖∑ i ∈ Finset.range n, w ^ i * q₀ ^ (n - 1 - i)‖ * ‖w - q₀‖ := norm_mul _ _
    _ ≤ (∑ i ∈ Finset.range n, (c + ρ) ^ i * c ^ (n - 1 - i)) * ρ :=
        mul_le_mul hS hwq (norm_nonneg _) (Finset.sum_nonneg fun i _ => by positivity)
    _ = (c + ρ) ^ n - c ^ n := hgeo

end Work.CNum
