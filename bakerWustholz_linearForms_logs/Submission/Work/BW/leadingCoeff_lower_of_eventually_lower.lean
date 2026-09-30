import Mathlib
import Submission.Work.BW.leadingCoeff_le_of_eventually_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If a polynomial `q` of degree `n` satisfies `q(t) ≥ c·t^n` for all large natural `t`, then `leadingCoeff q ≥ c`.

(Apply `Work.BW.leadingCoeff_le_of_eventually_le` to `p := Polynomial.C c * Polynomial.X ^ n`, whose `natDegree` is `n` when `c ≠ 0` and whose values are `c·t^n`; if `c = 0` use that `q` is eventually nonnegative, hence its leading coefficient is nonnegative, via `Work.BW.eventually_eval_neg_of_leadingCoeff_neg`.) -/
theorem leadingCoeff_lower_of_eventually_lower {q : Polynomial ℚ} {n : ℕ} (hqn : q.natDegree = n)
    {c : ℚ} (h : ∃ T : ℕ, ∀ t : ℕ, T ≤ t → c * (t : ℚ) ^ n ≤ q.eval (t : ℚ)) :
    c ≤ q.leadingCoeff := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    by_contra hcon
    rw [not_le] at hcon
    have hev := eventually_eval_neg_of_leadingCoeff_neg hcon
    rcases h with ⟨T, hT⟩
    rcases (hev.and (Filter.eventually_atTop.2 ⟨T, hT⟩)).exists with ⟨t, ht1, ht2⟩
    simp only [zero_mul] at ht2
    linarith
  · have hlc : (Polynomial.C c * Polynomial.X ^ n : Polynomial ℚ).leadingCoeff = c := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_pow, mul_one]
    have hpn : (Polynomial.C c * Polynomial.X ^ n : Polynomial ℚ).natDegree = n := by
      rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hc) (pow_ne_zero n Polynomial.X_ne_zero),
        Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
    have hle : (Polynomial.C c * Polynomial.X ^ n : Polynomial ℚ).leadingCoeff ≤ q.leadingCoeff := by
      apply leadingCoeff_le_of_eventually_le (p := Polynomial.C c * Polynomial.X ^ n) (q := q)
      · rw [hpn, hqn]
      · rcases h with ⟨T, hT⟩
        filter_upwards [Filter.eventually_atTop.2 ⟨T, hT⟩] with t ht
        simpa using ht
    rwa [hlc] at hle

end Work.BW
