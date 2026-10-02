/-
# EL nest: the conversion from the generic flower to the specialised `FlowerData`

The interface `Work.ELNest.NestData` (`Setup.lean`) is fed, among other data, by the Leau–Fatou
flower at the parabolic point `z₁` of `F c = (Tsq c)^[5]`, with the antiholomorphic square root
`G c = (Tantibar c)^[5]`.  The *generic* flower produced by the `FatouCoord` area is

```lean
Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁
```

while `Work.ELNest.FlowerData c z₀` (`Defs.lean`) is the same structure written out with the two
maps specialised to `F c` and `G c` — a specialisation that is *necessary*, because a structure
field whose type mentions the generic `ParabolicFlower (F c) (G c) z₀` (with the two functions as
arguments) makes the elaborator's `isDefEq` blow up when the structure is unpacked.

This file provides the conversion in the direction the caller needs,
`Work.ELNest.FlowerData.ofFatouCoord`: it constructs the specialised bundle from the generic one,
field by field.  The two directions are *not* an equivalence as stated: the generic structure
carries two pieces of data that the nest arguments never use and that are therefore not fields of
`FlowerData`, namely `Ψ_diff : Differentiable ℂ Ψ` and the antiholomorphy
`IsAntiholomorphicOn (G c) Pa` inside `φa_fatou` (only the equation
`φa (G c z) = star (φa z) + 1/2`, the third component of `IsAntiholomorphicFatouOn`, is kept).
Adding them back would make `FlowerData` ↔ `ParabolicFlower (F c) (G c) z₀` an equivalence.
-/
import Mathlib
import Submission.Work.ELNest.Defs
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c z₀ : ℂ}

/-- **The generic flower yields a `FlowerData`.**  Every field of `Work.ELNest.FlowerData c z₀`
is the corresponding field of `Work.FatouCoord.ParabolicFlower (F c) (G c) z₀`; the Fatou
condition is the third component of `IsAntiholomorphicFatouOn`, and the injectivity of `φa` is the
second conjunct of the generic `φa_fatou` field.  `Ψ_diff` and the antiholomorphy of the chart are
dropped (the nest arguments do not use them). -/
def FlowerData.ofFatouCoord (fl : Work.FatouCoord.ParabolicFlower (F c) (G c) z₀) :
    FlowerData c z₀ where
  Pa := fl.Pa
  φa := fl.φa
  Ψ := fl.Ψ
  isOpen_Pa := fl.isOpen_Pa
  isPreconnected_Pa := fl.isPreconnected_Pa
  z₀_not_mem := fl.z₀_not_mem
  mapsTo_Pa := fl.mapsTo_Pa
  tendsto_Pa := fl.tendsto_Pa
  enters_Pa := fl.enters_Pa
  φa_fatou := fl.φa_fatou.1.2.2
  φa_inj := fl.φa_fatou.2
  Ψ_shift := fl.Ψ_shift
  Ψ_anti := fl.Ψ_anti
  Ψ_small := fl.Ψ_small
  Ψ_inj := fl.Ψ_inj
  Ψ_ends := fl.Ψ_ends
  cover := fl.cover

@[simp] theorem FlowerData.ofFatouCoord_Pa (fl : Work.FatouCoord.ParabolicFlower (F c) (G c) z₀) :
    (FlowerData.ofFatouCoord fl).Pa = fl.Pa := rfl

@[simp] theorem FlowerData.ofFatouCoord_φa (fl : Work.FatouCoord.ParabolicFlower (F c) (G c) z₀) :
    (FlowerData.ofFatouCoord fl).φa = fl.φa := rfl

@[simp] theorem FlowerData.ofFatouCoord_Ψ (fl : Work.FatouCoord.ParabolicFlower (F c) (G c) z₀) :
    (FlowerData.ofFatouCoord fl).Ψ = fl.Ψ := rfl

end Work.ELNest
