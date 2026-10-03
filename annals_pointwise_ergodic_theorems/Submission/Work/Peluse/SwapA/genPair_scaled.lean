import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs

namespace Work.Peluse.SwapA

/-- `genPair` is monotone in the scale: a generic pair at scale `H` with parameter `η` is generic at
scale `c·H` with parameter `η/c` (`c ≥ 1`, so the gcd condition only weakens). -/
theorem genPair_scaled {H : ℕ} {η : ℝ} {q₁ q₂ : ℤ} (c : ℕ) (hc : 1 ≤ c)
    (h : Work.Peluse.LadderP.Swap.genPair H η q₁ q₂) :
    Work.Peluse.LadderP.Swap.genPair (c * H) (η / c) q₁ q₂ := by
  unfold Work.Peluse.LadderP.Swap.genPair at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  -- `c ≥ 1` is positive as a real, so the two size conditions transport unchanged:
  -- `(η/c)·(c·H) = η·H`.
  have hcpos : (0:ℝ) < (c:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have key : (η / (c:ℝ)) * ((c * H : ℕ) : ℝ) = η * (H:ℝ) := by
    push_cast
    field_simp
  -- `η ≥ 0`, since `η < 0` would force `gcd q₁ q₂ ≤ 1/η < 0`.
  have hge : (0:ℝ) ≤ ((Int.gcd q₁ q₂ : ℕ) : ℝ) := by positivity
  have heta : 0 ≤ η := by
    have h0 : 0 ≤ 1/η := le_trans hge h3
    rwa [one_div_nonneg] at h0
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; exact h1
  · rw [key]; exact h2
  · rcases eq_or_lt_of_le heta with h0 | hpos
    · -- `η = 0` forces `q₁ = q₂ = 0`: the gcd bound is `0 ≤ 0` on both sides.
      subst h0
      have hgcd : Int.gcd q₁ q₂ = 0 := by
        have hle : ((Int.gcd q₁ q₂ : ℕ) : ℝ) ≤ 0 := by simpa using h3
        exact_mod_cast (le_antisymm (by exact_mod_cast hle) (Nat.zero_le _))
      rw [hgcd]; norm_num
    · -- `η > 0`: `1/η ≤ c/η = 1/(η/c)` because `c ≥ 1`.
      have h1c : (1:ℝ) ≤ c := by exact_mod_cast hc
      have keyc : (1:ℝ)/η ≤ 1/(η/c) := by
        rw [one_div_div, div_le_div_iff_of_pos_right hpos]
        exact h1c
      exact le_trans h3 keyc

end Work.Peluse.SwapA
