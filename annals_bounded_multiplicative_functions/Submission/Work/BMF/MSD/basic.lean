import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for `mean_scales_down`

The Turán–Kubilius "mean scales down" bound is proved by an elementary additive large
sieve: after a discrete Fourier expansion the problem becomes a second-moment bound for
exponential sums at the frequencies `a/p`, and the additive large sieve is proved by the
Schur test applied to the `δ`-separated frequencies.

This file provides the two notions used by the pieces of that proof:
* `circDist θ`, the distance from `θ` to the nearest integer;
* `kern N θ`, the standard majorant for `‖∑_{n ∈ I} eC (n θ)‖` when `I` has `N` elements,
  namely `min N (1/(2 ‖θ‖))` (with the value `N` at `θ ∈ ℤ`, where `‖θ‖ = 0`).
-/

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF

/-- Distance from `θ` to the nearest integer. -/
noncomputable def circDist (θ : ℝ) : ℝ := |θ - ((⌊θ + 1 / 2⌋ : ℤ) : ℝ)|

/-- Majorant for `‖∑_{n ∈ I} eC (n θ)‖` when `I ⊆ ℕ` has `N` elements: `N` if `θ ∈ ℤ`, and
`min N (1 / (2 * circDist θ))` otherwise. -/
noncomputable def kern (N : ℕ) (θ : ℝ) : ℝ :=
  if circDist θ = 0 then (N : ℝ) else min (N : ℝ) (1 / (2 * circDist θ))

theorem circDist_nonneg (θ : ℝ) : 0 ≤ circDist θ := abs_nonneg _

theorem circDist_le_half (θ : ℝ) : circDist θ ≤ 1 / 2 := by
  rw [circDist]
  have h2 : ((⌊θ + 1 / 2⌋ : ℤ) : ℝ) ≤ θ + 1 / 2 := by
    have := Int.floor_le (θ + 1 / 2); linarith
  have h1 : θ - 1 / 2 < ((⌊θ + 1 / 2⌋ : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (θ + 1 / 2); linarith
  rw [abs_le]; constructor <;> linarith

theorem circDist_zero_iff (θ : ℝ) : circDist θ = 0 ↔ ∃ n : ℤ, θ = n := by
  rw [circDist, abs_eq_zero, sub_eq_zero]
  constructor
  · intro h; exact ⟨⌊θ + 1 / 2⌋, h⟩
  · rintro ⟨n, rfl⟩
    rw [show ((n:ℤ):ℝ) + 1 / 2 = (n:ℝ) + 1 / 2 by push_cast; ring]
    have : ⌊(n:ℝ) + 1 / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    rw [this]

theorem kern_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ kern N θ := by
  rw [kern]; split
  · exact Nat.cast_nonneg N
  · apply le_min (Nat.cast_nonneg N)
    apply div_nonneg (by norm_num)
    linarith [circDist_nonneg θ]

theorem kern_eq_min {N : ℕ} {θ : ℝ} (h : circDist θ ≠ 0) :
    kern N θ = min (N : ℝ) (1 / (2 * circDist θ)) := by
  rw [kern]; rw [if_neg h]

end Work.BMF.MSD
