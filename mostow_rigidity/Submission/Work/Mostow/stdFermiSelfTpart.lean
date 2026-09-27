import Mathlib
import Submission.Work.Mostow.stdFermiDefs
import Submission.Work.Mostow.stdFermiGeom

namespace Work.Mostow

/-- `fermiSelf` is the standard Fermi chart `stdFermi` read on the coordinates of `E 2`. -/
lemma fermiSelf_eq_stdFermi_stdFermiSelfTpart (x : Submission.Mostow.E 2) :
    Work.Mostow.FermiTwo.fermiSelf x = Work.Mostow.FermiTwo.stdFermi (x 0, x 1) := rfl

theorem stdFermiSelfTpart (x : Submission.Mostow.E 2) :
    Submission.Mostow.tpart (Work.Mostow.FermiTwo.fermiSelf x) =
      Real.cosh (x 0) * Real.cosh (x 1) := by
  rw [fermiSelf_eq_stdFermi_stdFermiSelfTpart, sfg_tpart_stdFermi]
  ring

end Work.Mostow
