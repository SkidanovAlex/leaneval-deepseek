import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Whitney.Cup
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Whitney.RelABComplex
import Submission.Work.Whitney.relABZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

/-- **The relative cup product.**  For open `A, B ⊆ X` and any commutative ring `R`, there is a
bilinear cup product `H^m(X,A;R) × H^n(X,B;R) ⟶ H^{m+n}(X,A∪B;R)` compatible with the absolute
cup product under the forgetful maps `H^*(X,-;R) ⟶ H^*(X;R)`.

It is built from the inclusion of cochain complexes `C^*(X,A∪B) ⟶ C^*(X,A+B)`, which is a
quasi-isomorphism for open `A` and `B`, and the Alexander–Whitney product on `C^*(X,A) ∩ C^*(X,B)`. -/
theorem exists_relRelCup {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ) :
    ∃ cup : Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
        Work.Thom.RelCoh R (m + n) X (A ∪ B),
      (∀ (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B),
        (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (cup a b)
          = Work.Cohomology.cupH' R (Work.Whitney.ssB X) m n
              ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b)) :=
  exists_relRelCup_of_quasiIso (R := R) (TopCat.of X) A B
    (fun N => pdABInclRelR_quasiIso (R := R) (M := TopCat.of X) A B hA hB N) m n

end Work.Whitney
