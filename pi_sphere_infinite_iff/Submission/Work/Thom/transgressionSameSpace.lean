import Mathlib
import Submission.Work.Thom.tsqHonest
import Submission.Work.Thom.honestDelta_mixedCup
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Thom

theorem transgressionSameSpace (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) (b : Work.Thom.RelCoh ℤ n X A) (k : ℕ) :
    (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.honestDelta X (∅ : Set X) U V hU hV hcov k)
        (Work.Thom.TsqH.Ttop X A n b (k + 1)))
      = (CategoryTheory.CategoryStruct.comp
          (Work.Thom.TsqH.Tov X A U V n b k)
          (CategoryTheory.CategoryStruct.comp
            (Work.Cohomology.honestDelta X A U V hU hV hcov (k + n))
            (CategoryTheory.eqToHom (congrArg (fun m => Work.Cohomology.pdCoh X A m)
              (by omega : k + n + 1 = (k + 1) + n))))) :=
  Work.Thom.honestDelta_mixedCup X A U V hU hV hcov n b k

end Work.Thom
