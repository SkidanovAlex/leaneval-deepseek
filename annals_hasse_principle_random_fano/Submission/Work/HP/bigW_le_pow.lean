import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.log_bigW_le
import Submission.Work.HP.tendsto_wOf_atTop
import Submission.Work.HP.pi_mul_log_eventually_le
import Submission.Work.HP.loglog_div_eventually_le

/-!
# `W(w(A)) ≤ A^ε` for every `ε > 0`, eventually in `A`

We are asked to show: for every `ε > 0` there is `B₀` with

  `W (wOf B) ≤ B ^ ε`  for all `B ≥ B₀`,

where `wOf B = log B / log log B` and `W(w) = ∏_{p ≤ w} p^{⌈log w / log p⌉ + 1}`.

The point is that `log W(w) = O(w) = O(log B / log log B)`, which is `o(log B)`.
Concretely, from `log_bigW_le`,

  `log W(w) ≤ π(⌊w⌋) log ⌈w⌉ + 2 (log 4) w`,

and `π(⌊w⌋) log ⌈w⌉ ≪ w` (`pi_mul_log_eventually_le`), so there is `C > 0`
with `log W(w) ≤ C w` for all large `w`.  Substituting `w = wOf B` (which tends
to `∞`) and using `C log B / log log B ≤ ε log B` for large `B`
(`loglog_div_eventually_le`), we get `log W(wOf B) ≤ ε log B = log (B^ε)`.
Exponentiating (`Real.log_le_log_iff`) gives the claim.
-/

set_option autoImplicit false

open Filter

namespace Work.HP

/-- `W(w) ≥ 1`, so `log W(w)` is the logarithm of a positive number. -/
lemma one_le_bigW (w : ℝ) : 1 ≤ bigW w := by
  rw [bigW]
  refine Finset.one_le_prod₀ fun p hp => ?_
  exact Nat.one_le_pow _ p (Nat.Prime.pos (Finset.mem_filter.mp hp).2)

/-- **Key asymptotic input.**  There is `C > 0` with
`log W(wOf B) ≤ C · log B / log log B` for all large `B`. -/
lemma log_bigW_wOf_eventually :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B in atTop,
      Real.log ((bigW (wOf B) : ℕ) : ℝ) ≤ C * Real.log B / Real.log (Real.log B) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := pi_mul_log_eventually_le
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨C₁ + 2 * Real.log 4, by linarith, ?_⟩
  have hpull : ∀ᶠ B in atTop,
      (Nat.primeCounting ⌊wOf B⌋₊ : ℝ) * Real.log ⌈wOf B⌉₊ ≤ C₁ * wOf B :=
    tendsto_wOf_atTop.eventually hC₁
  have hge : ∀ᶠ B in atTop, (2 : ℝ) ≤ wOf B := tendsto_wOf_atTop.eventually_ge_atTop 2
  filter_upwards [hpull, hge] with B hB hgeB
  have h := log_bigW_le (wOf B) hgeB
  have h' : Real.log ((bigW (wOf B) : ℕ) : ℝ) ≤
      (C₁ + 2 * Real.log 4) * Real.log B / Real.log (Real.log B) := by
    calc Real.log ((bigW (wOf B) : ℕ) : ℝ)
        ≤ (Nat.primeCounting ⌊wOf B⌋₊ : ℝ) * Real.log ⌈wOf B⌉₊ + 2 * Real.log 4 * wOf B := h
      _ ≤ (C₁ + 2 * Real.log 4) * wOf B := by linarith
      _ = (C₁ + 2 * Real.log 4) * Real.log B / Real.log (Real.log B) := by
            rw [wOf, mul_div_assoc]
  exact h'

theorem bigW_le_pow (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → (bigW (wOf B) : ℝ) ≤ B ^ ε := by
  obtain ⟨C, hCpos, hC⟩ := log_bigW_wOf_eventually
  have hεC : ∀ᶠ B in atTop, C * Real.log B / Real.log (Real.log B) ≤ ε * Real.log B :=
    loglog_div_eventually_le C ε hε
  have hmain : ∀ᶠ B in atTop,
      Real.log ((bigW (wOf B) : ℕ) : ℝ) ≤ ε * Real.log B ∧ 0 < B := by
    filter_upwards [hC, hεC, eventually_gt_atTop (0 : ℝ)] with B h1 h2 h3
    exact ⟨h1.trans h2, h3⟩
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hmain
  refine ⟨B₀, fun B hB => ?_⟩
  obtain ⟨hlog, hBpos⟩ := hB₀ B hB
  have hWpos : (0 : ℝ) < ((bigW (wOf B) : ℕ) : ℝ) := by
    have h1 : (0 : ℕ) < bigW (wOf B) := lt_of_lt_of_le Nat.zero_lt_one (one_le_bigW (wOf B))
    exact_mod_cast h1
  have hBε : (0 : ℝ) < B ^ ε := Real.rpow_pos_of_pos hBpos ε
  rw [← Real.log_le_log_iff hWpos hBε, Real.log_rpow hBpos ε]
  exact hlog

end Work.HP
