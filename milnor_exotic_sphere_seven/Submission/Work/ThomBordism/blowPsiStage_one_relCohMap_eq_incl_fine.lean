import Mathlib
import Submission.Work.ThomBordism.blowPsi
import Submission.Work.ThomBordism.valuePmOneV2Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# (F2), fine form: the collapse's local form and the inclusion agree on the fine pair

This is the *fine* variant of the proved `Work.ThomBordism.blowPsiStage_one_relCohMap_eq_incl`: the
relative pair is not the `C.inv`-described pair `(openTubePunct, tubeInvPunct)` but the **point-wise**
pair

  `({y : ↥C.openTube | y.1 ≠ E.e x}, tubePtSet E C x)`

whose excluded sets are described by the ambient condition "not the base point `E.e x`" (and which
are the sets in which the *local* classes based at `E.e x` live — `tubeTransMap`, `tubePtSet`,
`ambientStandardClass`).

The proof is *the same* as for the coarse form and is even simpler: the hypothesis `hp` of the
statement is *literally* the pair condition for the interpolation `blowPsiHomotopy E C` between the
identity (`blowPsiStage E C 0 = openTubeIncl E C`, proved as `blowPsiStage_zero`) and the collapse's
local form (`blowPsiStage E C 1`).  So `Work.Thom.relCohMap_homotopic` gives
`(blowPsiStage 0)^* = (blowPsiStage 1)^*` on this pair and `Work.Thom.relCohMap_congrA` replaces
`blowPsiStage 0` by the inclusion.  Nothing needs to be known about the relation between the fine
sets and the `C.inv`-sets.
-/

namespace Work.ThomBordism

theorem blowPsiStage_one_relCohMap_eq_incl_fine {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) (m : ℕ)
    (hp : ∀ (t : unitInterval) (y : ↥C.openTube),
      (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x →
        Work.ThomBordism.blowPsiStage E C t y ∈ Work.ThomBordism.tubePtSet E C x) :
    Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 1)
        ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
        (Work.ThomBordism.tubePtSet E C x)
        (hp 1) ℤ m
      = Work.Thom.relCohMap (Work.ThomBordism.openTubeIncl E C)
          ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
          (Work.ThomBordism.tubePtSet E C x)
          (fun y hy => hy) ℤ m := by
  have h1 : Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 0)
        ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
        (Work.ThomBordism.tubePtSet E C x) (hp 0) ℤ m
      = Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 1)
        ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
        (Work.ThomBordism.tubePtSet E C x) (hp 1) ℤ m :=
    Work.Thom.relCohMap_homotopic
      ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      (Work.ThomBordism.tubePtSet E C x) (hp 0) (hp 1)
      (blowPsiHomotopy E C) hp ℤ m
  have h2 : Work.Thom.relCohMap (Work.ThomBordism.openTubeIncl E C)
        ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
        (Work.ThomBordism.tubePtSet E C x) (fun y hy => hy) ℤ m
      = Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 0)
        ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
        (Work.ThomBordism.tubePtSet E C x) (hp 0) ℤ m :=
    Work.Thom.relCohMap_congrA
      ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      (Work.ThomBordism.tubePtSet E C x) (blowPsiStage_zero E C).symm
      (fun y hy => hy) (hp 0) ℤ m
  exact h1.symm.trans h2.symm

end Work.ThomBordism
