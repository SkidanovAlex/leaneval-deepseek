import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **T6a.** If `v π = vOne` (`π` is a uniformizer), then `π * (π^2)^ε` (`ε = ±1`) is not a fifth
power in `K`.  Route: `v (π * (π^2)^ε) = vOne * (vOne^2)^ε = ofAdd (-1 - 2ε)`; a fifth power has
value `(v u)^5 = ofAdd (-5 k)`, and `-1 - 2ε = -5 k` has no solution in `ℤ` for `ε = ±1`.
Declare it in namespace `Work.MotT` so that its full name is `Work.MotT.not_fifth_pow_of_vOne`. -/
theorem not_fifth_pow_of_vOne {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    {π : K} (hπ : v π = Work.MotT.vOne) (ε : ℤˣ) (u : K) :
    v (π * (π ^ 2) ^ (ε : ℤ)) ≠ v u ^ 5 := by
  intro hcontra
  -- `vOne` is `exp (-1)` on the nose; compute the value of the left hand side.
  have hπe : v π = WithZero.exp (-1 : ℤ) := hπ
  have hpow2 : v (π ^ 2) = WithZero.exp (-2 : ℤ) := by
    rw [Valuation.map_pow, hπe]
    rw [show (-2 : ℤ) = -1 + -1 by norm_num, WithZero.exp_add, pow_two]
  have hLHS : v (π * (π ^ 2) ^ (ε : ℤ)) = WithZero.exp (-1 - 2 * (ε : ℤ)) := by
    rw [Valuation.map_mul, hπe, map_zpow₀ v (π ^ 2) (ε : ℤ), hpow2, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, WithZero.exp_inj]
    simp only [zsmul_eq_mul, Int.cast_id]
    first | refl_ring1 | ring
  -- Apply `log` (which inverts `exp`, hence separates the values) to the hypothetical equality.
  have hlog := congrArg WithZero.log hcontra
  rw [hLHS, WithZero.log_exp, WithZero.log_pow] at hlog
  rcases Int.units_eq_one_or ε with h1 | h1
  · rw [h1] at hlog
    norm_num at hlog
    omega
  · rw [h1] at hlog
    norm_num at hlog
    omega

end Work.MotT
