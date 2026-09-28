import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Cohomology.smallProj_spec
import Submission.Work.Cohomology.exists_sub_small_of_boundary_small
import Submission.Work.Cohomology.existsSmallChainsContraction
import Submission.Work.Cohomology.homotopyEquivOfRetract

/-!
# The small chains are chain homotopy equivalent to the singular chains

Let `X` be a topological space and `U`, `V ⊆ X` an open cover of `X`.  The **small chains**
`C^{U,V}_*(X)` (`Submission/Work/Cohomology/SmallChains.lean`) are the subcomplex of the singular
chains spanned by the simplices whose image lies in `U` or in `V`, and the inclusion
`smallToSing U V` is a quasi-isomorphism (the small simplices theorem,
`Work.Cohomology.smallChains_homology_iso`).  This file proves the stronger chain level statement

`∃ e : HomotopyEquiv (smallChains U V) (singularChains ℤ X), e.hom = smallToSing U V`,

i.e. the inclusion of the small chains is a *chain homotopy equivalence*, with the inclusion itself
as the forward map.  This is what allows the Mayer–Vietoris argument to be dualised: applying
`dualComplex` to `e` gives a homotopy equivalence between the singular cochain complex and the
dual of the small chains, hence the Mayer–Vietoris long exact sequence in cohomology.

## The proof

The argument is purely homological once the two geometric inputs are available:

* the inclusion `C^{U,V}_*(X) → C_*(X)` is a degreewise split monomorphism: the projection
  `Work.Cohomology.smallProj` onto the small simplices along the complement spanned by the
  non-small generators retracts the inclusion, and `Work.Cohomology.smallProj_spec` records the
  two properties used here;
* the quotient complex `C_*(X)/C^{U,V}_*(X)` is acyclic — used here in the form
  `Work.Cohomology.exists_sub_small_of_boundary_small` (a chain whose boundary is small differs
  from a boundary by a small chain) — because some iterate of the barycentric subdivision maps
  every chain into the small chains (`Work.Cohomology.exists_iter_small_chain`) and the homotopy
  `Sd^N ~ id` preserves small chains (`Work.Cohomology.exists_small_homotopy`).

A degreewise split monomorphism `i : A → B` of `ℕ`-indexed chain complexes whose quotient is
acyclic is a homotopy equivalence: writing `θ n = r n ≫ i.f n` for the projection onto `A` and
`π n = 𝟙 - θ n`, the complement `im (π n)` inherits a differential for which it is a complex
isomorphic to the quotient; the acyclicity of the quotient is rectified into a contraction `κ` of
that complement by choosing the value of `κ n` on each non-small generator
(`Work.Cohomology.existsSmallChainsContraction`), and `Work.Cohomology.homotopyEquivOfRetract`
turns such a contraction into the homotopy equivalence, with homotopy inverse
`v n = r n - (κ n ≫ d (n+1) n) ≫ r n`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

theorem smallChainsHomotopyEquiv {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∃ e : HomotopyEquiv (smallChains U V) (singularChains ℤ X), e.hom = smallToSing U V := by
  -- the projection onto the small chains is a retraction of the inclusion ...
  obtain ⟨hcomp, hgenS, hgenN⟩ := smallProj_spec (X := X) U V
  -- ... fixing the generators of the small simplices ...
  have hr2 : ∀ n (σ : Simplex X n) (h : IsSmall U V σ),
      ((smallToSing U V).f n) ((smallProj U V n) (gen X n σ)) = gen X n σ := by
    intro n σ h
    rw [hgenS n σ h]
    exact smallToSing_gen ⟨σ, h⟩
  -- ... while the quotient of the singular chains by the small chains is acyclic; hence there is
  -- a contraction of the complement of the small chains in the singular chains ...
  obtain ⟨κ, h1, h2, h3zero, h3⟩ :=
    existsSmallChainsContraction U V (smallProj U V) hcomp hr2 hgenN
      (exists_sub_small_of_boundary_small U V hU hV hcov)
  -- ... which exhibits the inclusion as a homotopy equivalence.
  exact homotopyEquivOfRetract (smallToSing U V) (smallProj U V) hcomp κ h1 h2 h3zero h3

end Work.Cohomology
