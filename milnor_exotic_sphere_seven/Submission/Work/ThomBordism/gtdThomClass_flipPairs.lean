import Mathlib
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.GtdFlip.Crux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

theorem gtdThomClass_flipPairs {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) {k m : ℕ} (hodd : Odd k) (hm : 1 ≤ m)
    (gauss : C(B, Work.ThomBordism.Grassmann.OG k m))
    (Gplus : C(Z.TotalSpace, (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace))
    (hbp : ∀ p : Z.TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k m).proj (Gplus p) = gauss p.1)
    (Gminus : C(Z.TotalSpace, (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace))
    (hbp' : ∀ p : Z.TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k m).proj (Gminus p)
        = Work.ThomBordism.Grassmann.ogFlip k m (gauss p.1))
    (hvec : ∀ p : Z.TotalSpace,
      Work.ThomBordism.Grassmann.evalVec (Gminus p)
        = Work.ThomBordism.Grassmann.evalVec (Gplus p))
    (hmem : ∀ p ∈ Work.Thom.zeroComplement Z,
      Gplus p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m))
    (hmem' : ∀ p ∈ Work.Thom.zeroComplement Z,
      Gminus p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) :
    (Work.Thom.relCohMap Gminus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hmem' ℤ k).hom
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ
      = - ((Work.Thom.relCohMap Gplus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hmem ℤ k).hom
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ) :=
  Work.ThomBordism.GtdFlip.gtdThomClass_flipPairs_of_crux k m
    (Work.ThomBordism.GtdFlip.gtdFlip_crux k m hodd hm)
    Z hodd hm gauss Gplus hbp Gminus hbp' hvec hmem hmem'

end Work.ThomBordism
