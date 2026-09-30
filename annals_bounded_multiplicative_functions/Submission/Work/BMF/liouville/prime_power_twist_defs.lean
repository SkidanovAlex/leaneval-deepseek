import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open ArithmeticFunction

/-- The complex twist exponent `z = -1 - i·u` used in `prime_power_twist_correction`. -/
noncomputable def twistZ (u : ℝ) : ℂ := -(1 : ℂ) - Complex.I * (u : ℂ)

/-- The pointwise difference between the `(Λ n / log n)`-weighted summand and the prime-indicator
summand, at exponent `twistZ u`. Changing the summand at `n` by this correction turns the
logarithmically weighted von Mangoldt sum into the prime sum. -/
noncomputable def corr (u : ℝ) (n : ℕ) : ℂ :=
  (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)) * (n : ℂ) ^ (twistZ u)
    - (if n.Prime then (n : ℂ) ^ (twistZ u) else 0)

end Work.BMF.liouville
