import Mathlib
import Submission.Commons.NumberTheory.Zeta.trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos

namespace Commons.NumberTheory.Zeta

theorem mem_strip_of_riemannZeta_eq_zero_of_not_trivial {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re ∧ s.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact htriv (trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hz (not_lt.mp h))
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

end Commons.NumberTheory.Zeta
