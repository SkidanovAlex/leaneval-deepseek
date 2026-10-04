import Mathlib
import Submission.Work.Diff.Alg.Pinch.chat_shift_inclusion
import Submission.Work.Diff.Alg.Pinch.Chat_shift_inclusion_any
import Submission.Work.Diff.Alg.Pinch.Chat_window_shift
import Submission.Work.Diff.Alg.Pinch.Chat_large_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The global (uniform) shift inclusion for the Brendle–Schoen cones `Ĉ(s)`

The pointwise shift inclusion `Chat_shift_inclusion_any` says that for *each* `s > 0` and each level
`N > 0` there is `δ(s) > 0` with

`R + Iso n ∈ Ĉ(s)`, `scalAlg R ≤ N` ⟹ `R + 2 • Iso n ∈ Ĉ(s + δ(s))`.

For the pinching-set machinery (Böhm–Wilking Thm. 4.1 / Brendle–Schoen Prop. 16–17) one needs the
same statement with a **single** `δ`, uniform in `s` ranging over `[ε, ∞)`, and with an arbitrary
positive multiple `c • Iso n` of the round sphere:

`∀ ε > 0, ∀ N > 0, ∃ δ > 0, ∀ s ≥ ε, ∀ c > 0, ∀ R,`
`  R + c • Iso n ∈ Ĉ(s) → scalAlg R ≤ N · c → R + 2c • Iso n ∈ Ĉ(s + δ)`.

That is this file's theorem.  The uniformity is extracted as follows.

* The dependence on `c` is pure scaling: `Ĉ(s)` is a cone, so dividing by `c > 0` reduces to `c = 1`
  with level `N`, and multiplying back gives the general case.
* For `s ≥ 1/2` one is in the second branch `Ĉ(s) = ℓ_{s,1/2}(D(s))` where the Böhm–Wilking
  parameter `b = 1/2` is **fixed**; the shift identity
  `linv_{s+δ,1/2}(X + Iso n) = S + γ₂ • Iso n` then has no `Ric₀ ∧ id`-term, and the single room
  inequality that remains is satisfied for one uniform `δ` depending only on `n` and `N`
  (`Work.Diff.Alg.Pinch.Chat_large_shift`).
* For `ε ≤ s ≤ 1/2` one is on a *compact* window of the first branch; here the parameters
  `(anyAA n s, anyBB s, anyPP n s)` (`Work.Diff.Alg.Pinch.ChatAny`) move by `O(δ)`, `scalAlg S` is
  bounded by `N + n(n-1)`, and the defect `1 - anyPP n (s+δ)` is bounded below on the window, so the
  two `ChSRoom` inequalities hold for one uniform `δ` (`Work.Diff.Alg.Pinch.Chat_window_shift`).

Both cases conclude with the Böhm–Wilking inverse identity `linv_ell_add_smul_Iso` plus the core
`Dpic_shift_core`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

theorem Chat_inclusion_global (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℝ, 0 < N → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, ε ≤ s →
      ∀ c : ℝ, 0 < c → ∀ R : Submission.Diff.Alg.Curv4 n,
        R + c • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s →
        Submission.Diff.Alg.scalAlg R ≤ N * c →
        R + (2 * c) • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n (s + δ) := by
  intro ε hε N hN
  -- the uniform shifts on the two windows
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Chat_window_shift n hn ε N hε hN
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Chat_large_shift n hn N hN
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro s hs c hc R hX hscal
  -- reduce to `c = 1` by scaling with `c⁻¹` (the family `Ĉ(s)` is a cone)
  set R₀ : Curv4 n := c⁻¹ • R with hR₀
  have hc0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hX₀ : R₀ + Iso n ∈ Chat n s := by
    have h : c⁻¹ • (R + c • Iso n) = R₀ + Iso n := by
      rw [smul_add, smul_smul, ← hR₀, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    rw [← h]
    exact chat_smul_mem_of_nonneg hc0 hX
  have hsc₀ : scalAlg R₀ ≤ N := by
    rw [hR₀, scalAlg_smul]
    have h : c⁻¹ * scalAlg R ≤ c⁻¹ * (N * c) := mul_le_mul_of_nonneg_left hscal hc0
    have h2 : c⁻¹ * (N * c) = N := by
      rw [← mul_assoc, mul_comm c⁻¹ N, mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), mul_one]
    linarith
  have hres : R₀ + (2 : ℝ) • Iso n ∈ Chat n (s + min δ₁ δ₂) := by
    by_cases hs2 : s ≤ 1 / 2
    · exact hδ₁ (min δ₁ δ₂) (lt_min hδ₁pos hδ₂pos) (min_le_left _ _) s hs hs2 R₀ hX₀ hsc₀
    · exact hδ₂ (min δ₁ δ₂) (lt_min hδ₁pos hδ₂pos) (min_le_right _ _) s
        (le_of_lt (not_le.mp hs2)) R₀ hX₀ hsc₀
  -- multiply back by `c`
  have hconv : c • (R₀ + (2 : ℝ) • Iso n) = R + (2 * c) • Iso n := by
    rw [hR₀, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul,
      show c * 2 = 2 * c from by ring]
  rw [← hconv]
  exact chat_smul_mem_of_nonneg hc.le hres

end Work.Diff.Alg.Pinch
