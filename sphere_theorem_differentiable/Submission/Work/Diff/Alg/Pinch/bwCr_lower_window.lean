import Mathlib
import Submission.Work.Diff.Alg.Pinch.RoomAux.RFAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform positive lower bound for `bwCρ` on a window `[ε, 1/2]`

`Work.Diff.Alg.Pinch.RFAux.bwCρ n b` is the coefficient of `|Ric₀|² · |v|²` in the
Böhm–Wilking one-step estimate; `RFAux.bwCρ_pos` shows it is *positive* for `0 < b ≤ 1/2`.
For the pinching-set existence arguments one needs more: a bound that is **uniform** on the
window `ε ≤ b ≤ 1/2` (the shifted-cone/room arguments scale the pinching parameter `b`, and
the resulting invariant set must be controlled by a single constant).

`bwCρ n ·` is a rational function which is continuous and strictly positive on the compact
interval `[ε, 1/2]`, so it attains its minimum there and that minimum is positive.  The
statement of this file is exactly that: `∃ c > 0, ∀ b ∈ [ε,1/2], c ≤ bwCρ n b`.
-/

namespace Work.Diff.Alg.Pinch

open Set

/-- The Böhm–Wilking coefficient `bwCρ n ·` admits a strictly positive lower bound on every
window `[ε, 1/2]`, `0 < ε ≤ 1/2`. -/
theorem bwCr_lower_window (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ b : ℝ, ε ≤ b → b ≤ 1 / 2 → c ≤ Work.Diff.Alg.Pinch.RFAux.bwCρ n b := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- The denominator `n * bwR n b * bwq0 n b ^ 2` does not vanish on the window.
  have hne : ∀ b ∈ Icc ε (1 / 2),
      (n : ℝ) * Work.Diff.Alg.Pinch.RFAux.bwR n b * (Work.Diff.Alg.Pinch.RFAux.bwq0 n b) ^ 2 ≠ 0 := by
    intro b hb
    have hb0 : (0 : ℝ) ≤ b := le_trans hε.le hb.1
    have hR : 0 < Work.Diff.Alg.Pinch.RFAux.bwR n b := by
      unfold Work.Diff.Alg.Pinch.RFAux.bwR
      nlinarith [sq_nonneg b, mul_nonneg (sub_nonneg.mpr hn2) hb0]
    have hq : 0 < Work.Diff.Alg.Pinch.RFAux.bwq0 n b := by
      unfold Work.Diff.Alg.Pinch.RFAux.bwq0
      nlinarith [sq_nonneg b, mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg b)]
    exact ne_of_gt (mul_pos (mul_pos hn0 hR) (pow_pos hq 2))
  -- ... hence `bwCρ n ·` is continuous on the window.
  have hcont : ContinuousOn (fun b : ℝ => Work.Diff.Alg.Pinch.RFAux.bwCρ n b) (Icc ε (1 / 2)) := by
    unfold Work.Diff.Alg.Pinch.RFAux.bwCρ
    refine ContinuousOn.div ?_ ?_ hne
    · fun_prop
    · unfold Work.Diff.Alg.Pinch.RFAux.bwR Work.Diff.Alg.Pinch.RFAux.bwq0
      fun_prop
  -- The window is compact and nonempty, so the minimum is attained, and it is positive.
  obtain ⟨b₀, hb₀, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc ε (1/2)) ⟨ε, le_rfl, hε2⟩ hcont
  exact ⟨Work.Diff.Alg.Pinch.RFAux.bwCρ n b₀,
    Work.Diff.Alg.Pinch.RFAux.bwCρ_pos n hn (by linarith [hb₀.1, hε]) hb₀.2,
    fun b hb1 hb2 => hmin ⟨hb1, hb2⟩⟩

end Work.Diff.Alg.Pinch
