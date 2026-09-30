import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For a positive integer `n` and a purely imaginary exponent `-I * u`, the complex
power `(n : ℂ) ^ (-(I * u))` has modulus one. -/
theorem norm_cpow_neg_I_mul (u : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-(Complex.I * u))‖ = 1 := by
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos
    (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < (n : ℝ))]
  simp [Complex.neg_re]

end Work.BMF
