/-
# Tate cohomology of a pointwise product representation

For a finite group `G` and a family `M : ι → Rep ℤ G` of `ℤ`-linear representations of `G`, let
`piRep M` be the pointwise product representation, acting componentwise on `∀ i, (M i).V`.
This file proves that the Tate cohomology of `piRep M` in every degree is the product of the
Tate cohomologies of the factors:

`Nat.card (tateCohomology (piRep M) n) = Nat.card ((i : ι) → tateCohomology (M i) n)`.

This holds for an arbitrary index type `ι` (in particular an infinite one); the finiteness of `G`
is used through the fact that `Fin k → G` is finite, which makes a finitely supported function
into a product the same as a family of finitely supported functions.

The proof combines two ingredients:

* `tateComplex_piRep_piCplx_iso`: the Tate complex of `piRep M` is the pointwise product complex
  `piCplx ℤ (fun i => tateComplex (M i))` of the Tate complexes of the factors;
* `piCplx_homology_iso`: the homology of a pointwise product complex is the product of the
  homologies.

Everything is assembled in `tateCohomology_piRep` below.
-/
import Mathlib
import Submission.NK.RepresentationTheory.GroupCohomology.piCohomology_injective
import Submission.NK.GlobalCFTdeep.Herbrand.PiCplxDefs
import Submission.NK.GlobalCFTdeep.Herbrand.piCplx_homology_iso
import Submission.NK.GlobalCFTdeep.Herbrand.tateComplex_piRep_piCplx_iso

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
