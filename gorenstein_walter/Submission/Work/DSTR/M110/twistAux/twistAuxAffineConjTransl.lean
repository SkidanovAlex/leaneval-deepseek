import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius

namespace Work.DSTR.M110

open OnePoint

theorem twistAuxAffineConjTransl (F : Type*) [Field F] [DecidableEq F]
    (g : Equiv.Perm (Work.AUTL2.P1 F)) (d : F)
    (hinf : g OnePoint.infty = OnePoint.infty)
    (α β : F) (h : ∀ z : F, g (z : Work.AUTL2.P1 F) = ((α * z + β : F) : Work.AUTL2.P1 F)) :
    g * Work.AUTL2.transl F d = Work.AUTL2.transl F (α * d) * g := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun z => ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Work.AUTL2.transl_infty, hinf,
      Work.AUTL2.transl_infty]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Work.AUTL2.transl_formula, h (z + d), h z,
      Work.AUTL2.transl_formula]
    congr 1
    ring

end Work.DSTR.M110
