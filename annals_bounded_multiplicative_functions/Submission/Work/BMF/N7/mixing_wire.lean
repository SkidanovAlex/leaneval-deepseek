import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.N7.tbound_core
import Submission.Work.BMF.vk_exp_sum
import Submission.Work.BMF.N7.mixing_v6

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Wiring N7 to its own re-proof of the V-chain

`Work.BMF.N7.mixing_v6_main` is a copy of node V6 (`Submission.Work.BMF.zeta_prime_sum_twist`)
with the fleet's `logDeriv_LFunction_VK` (V4) and `ztw_param` replaced by
`Work.BMF.N7.logDeriv_LFunction_VK_of_growth_zf` and `Work.BMF.N7.ztw_paramN7`, fed by
`Work.BMF.N7.L_growth_VK_of_V1` (V2) and `Work.BMF.N7.zf_VK_N7` (V3).  Its only input from outside
is V1 (`Work.BMF.vk_exp_sum`), whose type is definitionally
`Work.BMF.VKExpSumRestrictedN7` (checked with `example : VKExpSumRestrictedN7 := vk_exp_sum`).

So N7 can be completed independently of the fleet's V2/V3/V4: as soon as V1 is proved and the three
conditional leaves `L_growth_VK_of_V1`, `logDeriv_LFunction_VK_of_growth_zf`, `ztw_paramN7` are
proved (they are being proved in parallel), `prime_exp_sum_bound_21_N7` below is sorry-free. -/

namespace Work.BMF.N7

open Polynomial

/-- The twisted von Mangoldt asymptotic (`21/20` range, `1/12` error) obtained from the N7 chain. -/
theorem twistedLambdaVK12_of_N7_chain : Work.BMF.TwistedLambdaVK12 := by
  obtain ⟨c, C, hc, h⟩ := Work.BMF.N7.mixing_v6_main vk_exp_sum
  exact ⟨c, C, hc, fun x hx u hu => h x (by linarith) u hu⟩

/-- **Prime exponential sum bound** (the input of N7), obtained from the N7 chain. -/
theorem prime_exp_sum_bound_21_N7 :
    ∃ K P₀ : ℝ, 0 < K ∧ ∀ (P η : ℝ), P₀ ≤ P →
      |η| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) / (2 * Real.pi) →
      ‖∑ p ∈ Work.BMF.primesIn P (2 * P), Work.BMF.eC (η * Real.log p)‖ ≤
        K * Work.BMF.pi0 P * (1 / (1 + |η|) + 1 / Real.log P) :=
  Work.BMF.prime_exp_sum_bound_21_of twistedLambdaVK12_of_N7_chain

end Work.BMF.N7
