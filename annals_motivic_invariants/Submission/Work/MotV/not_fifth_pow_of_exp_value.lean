import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-- If `v g = exp m` in the (multiplicatively written) value group `WithZero (Multiplicative ℤ)`
and `m` is not divisible by `5`, then `v g` is not a fifth power of any value `v u`: taking
logarithms, `log ((v u) ^ 5) = 5 • log (v u)`, so the exponent `m` of `v g` would have to be
divisible by `5`. -/
theorem not_fifth_pow_of_exp_value {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) {g : F} {m : ℤ}
    (h : v g = WithZero.exp m) (hm : ¬ (5 : ℤ) ∣ m) : ¬ ∃ u : F, v g = (v u) ^ 5 := by
  rintro ⟨u, hu⟩
  refine hm ⟨WithZero.log (v u), ?_⟩
  have hlog := congrArg WithZero.log hu
  rw [h, WithZero.log_exp, WithZero.log_pow] at hlog
  rw [nsmul_eq_mul] at hlog
  norm_num at hlog
  exact hlog

end Work.MotV
