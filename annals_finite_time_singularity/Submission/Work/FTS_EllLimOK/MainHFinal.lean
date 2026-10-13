/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.MainHFinal` — the unconditional deliverable

`RulingELF.ProducerH` (`L1 ∧ L2 ∧ L3`, assembled in `ProducerH.ProducerH_proved`) and
`MainH.core1_1a3_of_routeB` give the lead's `FinalV2.Producers.core1_1a3` conclusion from the
route-(b) hypothesis alone:

```
hb : ∃ α₁ > 0, ∀ α, 0 < α → α ≤ α₁ → ∀ g, ClassC α g → ∃ Ψ, EllClassOk 8 α g Ψ
```

— the exact hypothesis installed by the lead's ruling of 2026-10-11, with the exact conclusion
(`∃ Ce > 0, ∃ α₀ > 0, ∀ α ≤ α₀, ∃ E linear, (packages on the class `C`) ∧ FinalV2.EllLimOK3`).

`core1_1a3_proved` is `FinalV2.Producers.core1_1a3` with this hypothesis;
`EllLimOK_proved` is the order-`2` closure of the original request of this area.
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS_EllLimOK.MainH
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

/-- **The original request of this area**: the order-`2` limit closure `StrongEps.EllLimOK` from
the route-(b) hypothesis. -/
theorem EllLimOK_proved (hb : RouteB) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      Work.FTS.StrongEps.EllLimOK (pExp α) E :=
  EllLimOK_of_routeB ProducerH.ProducerH_proved hb

end Work.FTS_EllLimOK
