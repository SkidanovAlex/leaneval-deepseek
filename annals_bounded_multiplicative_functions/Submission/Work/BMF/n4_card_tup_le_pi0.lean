import Mathlib
import Submission.Work.BMF.tuple_setup
import Submission.Work.BMF.primesIn_card_le_pi0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **The number of admissible tuples is `O(π₀(P)^m)`.** -/
lemma n4_card_tup_le_pi0 : ∃ Cc P₀ : ℝ, 0 < Cc ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ (q m : ℕ),
    ((tup P q m).card : ℝ) ≤ Cc ^ m * pi0 P ^ m := by
  obtain ⟨C, P₁, hC, hbound⟩ := primesIn_card_le_pi0
  refine ⟨C, max 2 P₁, hC, le_trans (by norm_num) (le_max_left 2 P₁), ?_⟩
  intro P hP q m
  have hP1 : (1:ℝ) < P := by
    have : (2:ℝ) ≤ P := le_trans (le_max_left 2 P₁) hP
    linarith
  have hlog : 0 < Real.log P := Real.log_pos hP1
  have hpi0 : 0 ≤ pi0 P := by
    rw [pi0]; exact le_of_lt (div_pos (by linarith) hlog)
  have hPb : P₁ ≤ P := le_trans (le_max_right 2 P₁) hP
  have hb := hbound P hPb
  have hcard : ((tup P q m).card : ℝ) ≤ (((primesIn P (2*P)).card : ℝ))^m := by
    calc ((tup P q m).card : ℝ) ≤ ((((primesIn P (2*P)).card)^m : ℕ) : ℝ) := by
          exact_mod_cast (card_tup_le (P := P) (q := q) (ℓ := m))
      _ = (((primesIn P (2*P)).card : ℝ))^m := by push_cast; ring
  calc ((tup P q m).card : ℝ) ≤ (((primesIn P (2*P)).card : ℝ))^m := hcard
    _ ≤ (C * pi0 P)^m := pow_le_pow_left₀ (by positivity) hb m
    _ = C^m * pi0 P^m := mul_pow C (pi0 P) m

end Work.BMF
