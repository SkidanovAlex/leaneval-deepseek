import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates
import Submission.Work.FTS_EllLimOK.ProducerH.ProducerH_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- **The deliverable `core1_1a3`**, from the route-(b) hypothesis. -/
theorem core1_1a3_proved (hb : RouteB) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      Work.FTS.FinalV2.EllLimOK3 (pExp α) E :=
  core1_1a3_of_routeB ProducerH.ProducerH_proved hb


end Work.FTS_EllLimOK
