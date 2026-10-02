import Mathlib
import Submission.Work.ThomBordism.tubeSign
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.ThomBordism.absThomCompareIso
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Degree casts of the two comparisons of the tubular chapter

`Work.Tubular.compPull E n` and `Work.ThomBordism.compPullZ Z N n` are composites of two
`relCohMap`s, so they commute with a change of degrees by `Work.Thom.relCohMap_cast`.  These are
the cast lemmas that carry the ν-side computation of `Work.ThomBordism.tubeDataPerFamily` from the
degree `8 + k` (where the comparisons are naturally stated) to the degree `k + 8` of
`Work.Tubular.tubeThomRep_of_nuPairing`.
-/

open CategoryTheory
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **`compPull` commutes with a change of degrees.** -/
theorem compPull_cast {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {a b : ℕ}
    (h : a = b)
    (β : Work.Thom.RelCoh ℤ a (OnePoint (Work.Tubular.NormalTotal E)) (Work.Tubular.onePointNonzero E)) :
    Work.Tubular.compPull E b (h ▸ β) = h ▸ (Work.Tubular.compPull E a β) := by
  show (Work.Thom.relCohMap (Work.Tubular.homeoV E) (Work.Tubular.normalNonzero E)
      (Work.Tubular.excSub E) (fun x hx => (Work.Tubular.homeoV_mem E x).mp hx) ℤ b).hom
      ((Work.Thom.relCohMap (Work.Tubular.infComplIncl E) (Work.Tubular.excSub E)
        (Work.Tubular.onePointNonzero E) (fun y hy => hy) ℤ b).hom (h ▸ β))
    = h ▸ ((Work.Thom.relCohMap (Work.Tubular.homeoV E) (Work.Tubular.normalNonzero E)
        (Work.Tubular.excSub E) (fun x hx => (Work.Tubular.homeoV_mem E x).mp hx) ℤ a).hom
      ((Work.Thom.relCohMap (Work.Tubular.infComplIncl E) (Work.Tubular.excSub E)
        (Work.Tubular.onePointNonzero E) (fun y hy => hy) ℤ a).hom β))
  rw [Work.Thom.relCohMap_cast (Work.Tubular.infComplIncl E) (Work.Tubular.excSub E)
      (Work.Tubular.onePointNonzero E) (fun y hy => hy) h β]
  rw [Work.Thom.relCohMap_cast (Work.Tubular.homeoV E) (Work.Tubular.normalNonzero E)
      (Work.Tubular.excSub E) (fun x hx => (Work.Tubular.homeoV_mem E x).mp hx) h _]

/-- **`compPullZ` commutes with a change of degrees.** -/
theorem compPullZ_cast {ι : Type} {Z : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι}
    (N : NormLike Z) {a b : ℕ} (h : a = b)
    (β : Work.Thom.RelCoh ℤ a (OnePoint Z.TotalSpace) (absNZ Z)) :
    compPullZ Z N b (h ▸ β) = h ▸ (compPullZ Z N a β) := by
  show (Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
      (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ b).hom
      ((Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ b).hom (h ▸ β))
    = h ▸ ((Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
        (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ a).hom
      ((Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ a).hom β))
  rw [Work.Thom.relCohMap_cast (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) h β]
  rw [Work.Thom.relCohMap_cast (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
      (fun x hx => (some_mem_excSubZ Z x).mp hx) h _]

end

end Work.ThomBordism
