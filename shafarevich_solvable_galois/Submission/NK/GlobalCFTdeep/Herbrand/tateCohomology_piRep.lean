import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.piCplx_homology_iso
import Submission.NK.GlobalCFTdeep.Herbrand.tateComplex_piRep_piCplx_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NK.GlobalCFTdeep.Herbrand

noncomputable section

open CategoryTheory CategoryTheory.Limits
open NK.RepresentationTheory.GroupCohomology (piRep)

/-- **Neukirch–Uchida, `Herbrand` auxiliary: the Tate cohomology of a pointwise product of
representations is the product of the Tate cohomologies of the factors.** -/
theorem tateCohomology_piRep {G : Type} [Group G] [Fintype G] {ι : Type}
    (M : ι → Rep ℤ G) (n : ℤ) :
    Nat.card (tateCohomology (NK.RepresentationTheory.GroupCohomology.piRep M) n) =
      Nat.card ((i : ι) → tateCohomology (M i) n) := by
  obtain ⟨e3⟩ := tateComplex_piRep_piCplx_iso (R := ℤ) M
  obtain ⟨e2⟩ := piCplx_homology_iso (R := ℤ) (fun i => tateComplex (M i)) n
  have e1 :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) n).mapIso e3 ≪≫ e2
  exact Nat.card_congr e1.toLinearEquiv.toEquiv

end

end NK.GlobalCFTdeep.Herbrand
