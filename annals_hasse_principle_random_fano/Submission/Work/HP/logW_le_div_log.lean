import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.Sig2.log_pow_le_rpow

/-!
# `log B · W(w(B)) ≤ B / log B` for all large `B`

We are asked to show that eventually

  `log B · W(w(B)) ≤ B / log B`,   where `w(B) = log B / log log B`.

Since `W(w(B))` grows slower than any fixed power of `B`, it suffices to use the
crude bound `W(w(B)) ≤ B^{1/2}` (`bigW_le_pow` with `ε = 1/2`).  Then

  `log B · W(w(B)) ≤ log B · B^{1/2}`,

and `log B · B^{1/2} ≤ B / log B` is equivalent (multiply by `log B > 0`) to

  `(log B)^2 ≤ B^{1/2}`,

which holds for all large `B` because powers of `log` are dominated by every
positive power of `B` (`Sig2.log_pow_le_rpow` with `m = 2`, `ε = 1/2`).
-/

set_option autoImplicit false

namespace Work.HP

theorem logW_le_div_log : ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
    Real.log B * (bigW (wOf B) : ℝ) ≤ B / Real.log B := by
  obtain ⟨B₁, hB₁⟩ := bigW_le_pow (1 / 2) (by norm_num)
  obtain ⟨A₀, -, hA₀⟩ := Sig2.log_pow_le_rpow 2 (1 / 2) (by norm_num)
  refine ⟨max (max B₁ A₀) 4, by positivity, fun B hB => ?_⟩
  have hBB₁ : B₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBA₀ : A₀ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hB4 : (4 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hBpos : 0 < B := by linarith
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by linarith)
  -- `W(w(B)) ≤ B^{1/2}`.
  have hW : (bigW (wOf B) : ℝ) ≤ B ^ (1 / 2 : ℝ) := hB₁ B hBB₁
  -- `(log B)^2 ≤ B^{1/2}`.
  have hlogsq : (Real.log B) ^ 2 ≤ B ^ (1 / 2 : ℝ) := by
    have h := hA₀ B hBA₀
    nlinarith [hlogB_nonneg, h]
  have hBhalf_pos : 0 < B ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hBpos _
  have hBeq : B ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) = B := by
    rw [← Real.rpow_add hBpos]; norm_num
  calc Real.log B * (bigW (wOf B) : ℝ)
      ≤ Real.log B * B ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hW hlogB_nonneg
    _ ≤ B / Real.log B := by
        rw [le_div_iff₀ hlogB_pos]
        nlinarith [mul_le_mul_of_nonneg_left hlogsq (le_of_lt hBhalf_pos), hBeq]

end Work.HP
