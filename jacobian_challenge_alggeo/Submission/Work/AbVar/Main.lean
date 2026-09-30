/-
Area AV (abelian-variety toolkit) for the Jacobian challenge: table of contents.
-/
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.Gen
import Submission.Work.AbVar.SmoothIntegral
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.TestObjects.gm_geometricallyIntegral
import Submission.Work.AbVar.TestObjects.ga_geometricallyIntegral
import Submission.Work.AbVar.Extend
import Submission.Work.AbVar.Extend.desc_of_flat_surjective_quasiCompact
import Submission.Work.AbVar.Rigidity.rigidity
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.P1.const_of_action
import Submission.Work.AbVar.P1Action.Action
import Submission.Work.AbVar.ProjectiveLine.smooth
import Submission.Work.AbVar.ProjectiveLine.geometricallyIrreducible
import Submission.Work.AbVar.ProjectiveLine.geometricallyIntegral
import Submission.Work.AbVar.ProjectiveLine.isProper_P1
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.AbVar.ProjectiveLine.scalingActionData
import Submission.Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine
import Submission.Work.AbVar.Rigidity.isReduced_tensorObj_of_geometricallyIntegral
import Submission.Work.AbVar.Rigidity.rigid_isAlgClosed
import Submission.Work.AbVar.Hom.isMonHom_of_isPointedMap
import Submission.Work.AbVar.Hom.sectionLeft_homObstruction
import Submission.Work.AbVar.Hom.sectionRight_homObstruction
import Submission.Work.AbVar.Hom.isGroupHom_of_pointed_of_homObstruction_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area AV — abelian-variety toolkit

Import this module for the whole chapter. The main entry points are

* `Work.AbVar.IsAbelianVariety` — smooth + proper + geometrically irreducible over a field;
  `GeometricallyIntegral` and `IsCommMonObj` for such `A` are found by `inferInstance`
  (`SmoothIntegral.lean`);
* `Work.AbVar.Rigidity.rigid_isAlgClosed` — the rigidity lemma over an algebraically closed
  field;
* `Work.AbVar.Hom.isMonHom_of_isPointedMap` — a pointed morphism between proper
  geometrically integral group schemes is a homomorphism;
* `Work.AbVar.eq_of_isDominant`, `Work.AbVar.eq_of_surjective` — two morphisms out of a
  reduced scheme into a separated one which agree on a dominant locus are equal;
* `Work.AbVar.Extend.desc_of_flat_surjective_quasiCompact` and
  `Work.AbVar.desc_of_flat_surjective_quasiCompact_of_dense` — fpqc (flat + surjective +
  quasi-compact) descent of morphisms;
* `Work.AbVar.P1 k` — the projective line as a `k`-scheme, with
  `Work.AbVar.ProjectiveLine.smooth`, `…geometricallyIrreducible`,
  `…geometricallyIntegral`, `…isProper_P1`;
* `Work.AbVar.P1Action.scalingAct`, `Work.AbVar.ProjectiveLine.scalingActionData` — the
  `𝔾_m`-scaling action on `ℙ¹`, its fixed point and its dense orbit, packaged as the data
  consumed by the rigidity corollary `Work.AbVar.P1.const_of_action`;
* `Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine` — **P1CONST**: every morphism
  `P1 k ⟶ A` into a proper group scheme is constant;
* `Work.AbVar.Gm`, `Work.AbVar.Ga`, `Work.AbVar.P1.const_of_action`.

See `Submission/Work/AbVar/NOTES.md` for the current status of each contract item.
-/
