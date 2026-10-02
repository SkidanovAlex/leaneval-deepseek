/-
# Bridge to the `FQC` area: the critical Écalle height is the same quantity

Area `Submission/Work/Final/`.  The `FQC` area (`Submission/Work/FQC/`) reads the critical Écalle
height off a structure `Work.FQC.EcalleData d` (the attracting petal and its Fatou coordinate,
abstracted so that a quasiconformally transported petal is allowed):

```lean
Work.FQC.nEnter (E : EcalleData d) : ℕ                       -- first entry into `E.Pa`
Work.FQC.critHeightAt (d : RootParabolic c) (E : EcalleData d) : ℝ := (E.φa ((F c)^[nEnter E] c)).im
Work.FQC.EcalleData.ofFlower (d) (fl) : EcalleData d          -- from a Leau–Fatou flower
```

This is *the same* quantity as `Work.Final.RootArc.critHeight`: the two `nEnter`s are the two
`Nat.find`s of the same existential (the entry of the critical orbit into the same petal), and the
two heights are the imaginary parts of the same coordinate.  This module records the bridge, so
that the `root` field of `Work.Final.FinalInputs` (FQC's export, whose height-`0` clause is
`A.critHeight = 0`) is a statement about one and the same function of the parameter as the `FQC`
area's `heightShift`.

**The Fatou equation.**  Reading the height off at a *later* time needs the Abel equation
`φa (F z) = φa z + 1` on the petal, i.e. the hypothesis `φa_shift` that `FatouCoordFix` exports
and that `Work.FQC.PetalInput` carries (see the interface note in `RootArc.lean`).  A
`Work.FQC.PetalInput d fl` supplies it directly, because its field `φa_shift` *is*
`Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5]) fl`; the last theorem below records
the resulting tap-time independence in the vocabulary of this area, without importing the
`FQC` petal interface (which is under active development).
-/
import Submission.Work.Final.Defs
import Submission.Work.Final.RootArc
import Submission.Work.FQC.Defs

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

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The entry time into the petal is the same for `RootArc` and for `FQC`.**  Both are the
`Nat.find` of the same existential: the first `n` with the `n`-th iterate of the critical value in
the petal `fl.Pa`. -/
theorem nEnter_eq_FQC {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :
    RootArc.nEnter (⟨d, fl⟩ : RootArc c) =
      Work.FQC.nEnter (Work.FQC.EcalleData.ofFlower d fl) :=
  rfl

/-- **The critical Écalle height is the same for `RootArc` and for `FQC`.** -/
theorem critHeight_eq_FQC {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :
    RootArc.critHeight (⟨d, fl⟩ : RootArc c) =
      Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) := by
  rw [RootArc.critHeight, Work.FQC.critHeightAt, nEnter_eq_FQC d fl]
  rfl

/-- **The critical height is the Écalle height of every iterate of the critical orbit past the
entry time**, from the Abel equation `φa_shift` on the petal (the content of
`Work.FQC.PetalInput.φa_shift`, which *is* `Work.FinalFix.HasPhiShift`, so a `PetalInput`
instantiates this lemma with `h := h.φa_shift`). -/
theorem critHeight_eq_ecalleHeightAt_of_shift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hshift : Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5]) fl)
    {n : ℕ} (hn : RootArc.nEnter (⟨d, fl⟩ : RootArc c) ≤ n) :
    RootArc.critHeight (⟨d, fl⟩ : RootArc c) = RootArc.ecalleHeightAt ⟨d, fl⟩ n :=
  RootArc.critHeight_eq_ecalleHeightAt (A := ⟨d, fl⟩) hshift hn

end Work.Final
