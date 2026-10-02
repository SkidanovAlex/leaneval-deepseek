/-
# `Work.FinalFix.FQCRoot` — FQC's height-`0` seed as the `root` field of `FinalInputs`

Area `Submission/Work/FinalFix/` of the mandelbar project.  The `FQC` area delivers the height-`0`
parameter as (`Submission/Work/FQC/Seed.lean`)

```lean
Work.FQC.exists_critHeight_zero_of (d₁) (fl) (hpetal) (hphase) (hsimple) (hU) :
    ∃ c₀ : ℂ, ∃ d₀ : Work.EL.RootParabolic c₀, Work.FQC.critHeight d₀ = 0
```

with `Work.FQC.critHeight d = critHeightAt d (EcalleData.canonical d)` (`FQC/Flower.lean`).  The
`root` field of `Work.Final.FinalInputs` asks for FQC's export in the `Final` vocabulary
(`NOTES_LEAD_mandelbar_residuals.md` §4, row `c₀`/`arc`/`critHeight_zero`):

```lean
Work.FinalFix.RootArcHeightZero = ∃ c₀ : ℂ, ∃ A : Work.Final.RootArc c₀, A.critHeight = 0.
```

This module proves that the `FQC` form *is* the `Final` form, so the lead can write

```lean
FinalInputs.root := Work.FinalFix.RootArcHeightZero.of_FQC_exists hU
    (Work.FQC.exists_critHeight_zero_of d₁ fl hpetal hphase hsimple hU)
```

The only non-formal ingredient is the independence of the height of the choice of Écalle data
(`Work.FQC.FatouUnique`, an input of the `FQC` area) together with the bridge
`Work.Final.critHeight_eq_FQC` (this area's `FQC.Defs`-level module `Submission/Work/Final/`).
-/
import Submission.Work.FinalFix.RootExport
import Submission.Work.Final.FQCBridge
import Submission.Work.FQC.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.FinalFix

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **FQC's height-`0` parameter at a fixed root-parabolic parameter is a `RootArc` of height
`0`.**  The flower of the root-arc data is chosen canonically (`Work.Final.ofRootParabolic`); the
height does not depend on that choice because it does not depend on the Écalle data at all
(`hU : Work.FQC.FatouUnique`). -/
theorem RootArcHeightZero.of_FQC_critHeight {c₀ : ℂ} (d₀ : Work.EL.RootParabolic c₀)
    (hU : Work.FQC.FatouUnique) (h : Work.FQC.critHeight d₀ = 0) : RootArcHeightZero := by
  refine ⟨c₀, Work.Final.ofRootParabolic d₀, ?_⟩
  have h2 : (Work.Final.ofRootParabolic d₀).critHeight
      = Work.FQC.critHeightAt d₀
          (Work.FQC.EcalleData.ofFlower d₀ (Work.Final.ofRootParabolic d₀).fl) :=
    Work.Final.critHeight_eq_FQC d₀ (Work.Final.ofRootParabolic d₀).fl
  have h1 : Work.FQC.critHeight d₀
      = Work.FQC.critHeightAt d₀
          (Work.FQC.EcalleData.ofFlower d₀ (Work.Final.ofRootParabolic d₀).fl) := by
    rw [Work.FQC.critHeight]
    exact hU.eq d₀ (Work.FQC.EcalleData.canonical d₀) _
  rw [h2]
  exact h1.symm.trans h

/-- **FQC's export, in the exact form of `FinalInputs.root`.**  This is the theorem the lead
instantiates with the `FQC` area's seed theorem `Work.FQC.exists_critHeight_zero_of`. -/
theorem RootArcHeightZero.of_FQC_exists (hU : Work.FQC.FatouUnique)
    (h : ∃ c₀ : ℂ, ∃ d₀ : Work.EL.RootParabolic c₀, Work.FQC.critHeight d₀ = 0) :
    RootArcHeightZero := by
  obtain ⟨c₀, d₀, hd⟩ := h
  exact RootArcHeightZero.of_FQC_critHeight d₀ hU hd

end Work.FinalFix
