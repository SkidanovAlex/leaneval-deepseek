import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.jksym_mul_rule_primary
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FITop3.Witness.primary_mul

namespace Work.FIArea7.P231

/-- The product of two primary Gaussian integers is primary. -/
lemma isPrimary_mul {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : Work.FIPlan.IsPrimary (w * z) :=
  Work.FITop3.Witness.primary_mul hw hz

lemma JKSym_mul_assoc_eq {e w z : GaussianInt} (he : Work.FIPlan.IsPrimary e)
    (hec : IsCoprime e.re e.im) (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z) :
    Work.FIArea7.JKSym (e * w * z)
      = (Work.FIArea7.MultEps e (w * z) : ℂ) * Work.FIArea7.JKSym e * Work.FIArea7.JKSym (w * z)
        * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ)
        * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ) := by
  have hwz : Work.FIPlan.IsPrimary (w * z) := isPrimary_mul hw hz
  have hrule := jksym_mul_rule_primary he hec hwz
  have hd := dirichletSym_mul he hec w z
  rw [mul_assoc, hrule, hd]
  push_cast
  ring

end Work.FIArea7.P231
