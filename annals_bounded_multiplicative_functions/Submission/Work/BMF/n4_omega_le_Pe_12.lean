import Mathlib
import Submission.Work.BMF.n4_polylog_le
import Submission.Work.BMF.n4err_omega_le
import Submission.Work.BMF.vk_prime_sums

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem n4_omega_le_Pe_12 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (Real.log P) ^ (ℓ + 4) →
      (q.primeFactors.card : ℝ) ≤ P * Real.exp (-c₁ * (Real.log P) ^ (1 / 12 : ℝ)) := by
  -- `ω(q)·log x ≤ C·x·exp(-c (log x)^{1/12})` for `q ≤ (log x)^A` (`vk_omega_mul_log_le`).
  obtain ⟨C, hCpos, hC⟩ := vk_omega_mul_log_le ((ℓ + 4 : ℕ) : ℝ) c₁ (by positivity) hc₁
  refine ⟨max 3 (Real.exp C), ?_, ?_⟩
  · exact le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_left _ _)
  intro P hP q hq hqq
  have hP3 : 3 ≤ P := le_trans (le_max_left _ _) hP
  have hPC : Real.exp C ≤ P := le_trans (le_max_right _ _) hP
  have hPpos : 0 < P := by linarith
  have hlog_ge_C : C ≤ Real.log P := by
    have h1 := Real.log_le_log (Real.exp_pos C) hPC
    rwa [Real.log_exp] at h1
  have hlog_pos : 0 < Real.log P := lt_of_lt_of_le hCpos hlog_ge_C
  haveI : NeZero q := ⟨Nat.one_le_iff_ne_zero.mp hq⟩
  -- the hypothesis `q ≤ (log P)^{ℓ+4}` written with the real power.
  have hq' : (q : ℝ) ≤ Real.log P ^ ((ℓ + 4 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; exact hqq
  have hkey := hC P hP3 q hq'
  have hexp_nonneg : 0 ≤ P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)) :=
    mul_nonneg hPpos.le (Real.exp_pos _).le
  -- `C / log P ≤ 1` because `log P ≥ C`.
  have hratio : C / Real.log P ≤ 1 := (div_le_one hlog_pos).mpr hlog_ge_C
  calc (q.primeFactors.card : ℝ)
      ≤ C * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)) / Real.log P :=
        (le_div_iff₀ hlog_pos).mpr hkey
    _ = (C / Real.log P) * (P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))) := by ring
    _ ≤ 1 * (P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_right hratio hexp_nonneg
    _ = P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)) := one_mul _

end Work.BMF
