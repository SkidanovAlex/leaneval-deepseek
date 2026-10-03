import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The `ℓ¹` mass of a finitely supported bounded function

`supportIn_tsum_le`: if `g : ℤ → ℂ` is supported in `[-N₀, N₀]` (`Work.Peluse.SupportIn g N₀`) and
bounded by one, then its `ℓ¹` mass is at most the size `2 N₀ + 1` of the support interval.  The
`tsum` is a finite sum: `‖g‖` vanishes off `Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

theorem supportIn_tsum_le {N₀ : ℕ} {g : ℤ → ℂ} (h : Work.Peluse.SupportIn g N₀)
    (hb : ∀ x : ℤ, ‖g x‖ ≤ 1) :
    (∑' x : ℤ, ‖g x‖) ≤ ((2 * N₀ + 1 : ℕ) : ℝ) := by
  -- the support interval `[-N₀, N₀]`, written as a `ℤ`-interval
  have hmem : ∀ x : ℤ, x.natAbs ≤ N₀ → x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) := by
    intro x hx
    rw [Finset.mem_Icc]
    have habs : |x| ≤ (N₀ : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hx
    exact abs_le.mp habs
  have hsupp : ∀ x : ℤ, x ∉ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) → ‖g x‖ = 0 := by
    intro x hx
    have hxabs : N₀ < x.natAbs := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hx (hmem x hcon)
    rw [h x hxabs, norm_zero]
  rw [tsum_eq_sum hsupp]
  calc ∑ x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖g x‖
      ≤ ∑ x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), (1 : ℝ) := Finset.sum_le_sum fun x _ => hb x
    _ = ((Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)).card : ℝ) := by simp
    _ = ((2 * N₀ + 1 : ℕ) : ℝ) := by
        congr 1
        rw [Int.card_Icc]
        have h2 : (N₀ : ℤ) + 1 - (-(N₀ : ℤ)) = ((2 * N₀ + 1 : ℕ) : ℤ) := by
          push_cast; ring
        rw [h2, Int.toNat_natCast]

end

end Work.Peluse.Ulower
