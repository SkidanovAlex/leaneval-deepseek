import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.Tate.Equivs
import Submission.Work.Tate.Hm1ToCoinv_injective
import Submission.Work.Tate.coind_augmentation_eq_ker_norm
import Submission.Work.Tate.coind_norm_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.tate

theorem Hm1Map_comp {G : Type*} {A B C : Type*} [Group G] [Fintype G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (e : A →+ B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (f : B →+ C) (hf : ∀ (g : G) (b : B), f (g • b) = g • f b)
    (hfe : ∀ (g : G) (a : A), (f.comp e) (g • a) = g • (f.comp e) a) :
    Work.Tate.Hm1Map G A C (f.comp e) hfe
      = (Work.Tate.Hm1Map G B C f hf).comp (Work.Tate.Hm1Map G A B e he) := by
  apply AddMonoidHom.ext
  intro x
  induction x using Work.Tate.Hm1_induction_on with
  | h a =>
    simp only [Work.Tate.Hm1Map_Hm1π, AddMonoidHom.comp_apply]
    congr 1

end Work.CohomologicalShrinking.tate
