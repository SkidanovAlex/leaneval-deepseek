import Mathlib
import Submission.Work.BW.natDegree_le_of_eventually_le_pow
import Submission.Work.BW.le_natDegree_of_eventually_le_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A polynomial bounded above by `C·t^n` for all `t ≥ 1` and below by `c·t^n` (`c > 0`) for all large `t` has degree exactly `n`. -/
theorem natDegree_eq_of_bounds {q : Polynomial ℚ} {n : ℕ} {c : ℚ} (hc : 0 < c)
    (hupper : ∃ C : ℚ, ∀ t : ℕ, 1 ≤ t → q.eval (t : ℚ) ≤ C * (t : ℚ) ^ n)
    (hlower : ∃ T : ℕ, ∀ t : ℕ, T ≤ t → c * (t : ℚ) ^ n ≤ q.eval (t : ℚ)) :
    q.natDegree = n := by
  obtain ⟨C, hC⟩ := hupper
  obtain ⟨T, hT⟩ := hlower
  -- Reinterpret both one-sided bounds as eventual statements along `atTop`.
  have hlow_ev : ∀ᶠ t : ℕ in Filter.atTop, c * (t : ℚ) ^ n ≤ q.eval (t : ℚ) :=
    Filter.eventually_atTop.mpr ⟨T, fun t ht => hT t ht⟩
  have hup_ev : ∀ᶠ t : ℕ in Filter.atTop, q.eval (t : ℚ) ≤ C * (t : ℚ) ^ n :=
    Filter.eventually_atTop.mpr ⟨1, fun t ht => hC t ht⟩
  -- The lower bound forces eventual positivity of `q` on the naturals.
  have hpos : ∀ᶠ t : ℕ in Filter.atTop, 0 < q.eval (t : ℚ) := by
    filter_upwards [hlow_ev, Filter.eventually_ge_atTop (max 1 T)] with t hl ht
    have ht1 : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast le_trans (le_max_left 1 T) ht
    have hpow : (1 : ℚ) ≤ (t : ℚ) ^ n := one_le_pow₀ ht1
    have hcpos : 0 < c * (t : ℚ) ^ n := mul_pos hc (lt_of_lt_of_le zero_lt_one hpow)
    linarith
  exact le_antisymm (natDegree_le_of_eventually_le_pow hpos hup_ev)
    (le_natDegree_of_eventually_le_pow hc hlow_ev)

end Work.BW
