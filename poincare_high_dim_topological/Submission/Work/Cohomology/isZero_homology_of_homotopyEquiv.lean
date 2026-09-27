import Mathlib
import Submission.Work.Cohomology.homologyContractible

/-!
# Vanishing of singular homology is a homotopy invariant

A homotopy equivalence of topological spaces induces an isomorphism on singular homology in every
degree (`Work.Cohomology.homologyEquiv`).  Consequently, if the singular homology of `Y` vanishes
in degree `n` — i.e. it is a zero object of `ModuleCat ℤ` — then so does the singular homology of
any space `X` homotopy equivalent to `Y`.

This is the homology counterpart of the analogous statement for cohomology, and it is used to
transport explicit computations performed on a convenient model space back to the space of
interest.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

/-- **Vanishing of singular homology is a homotopy invariant.**  If `X` is homotopy equivalent to
`Y` and the `n`-th singular homology of `Y` (with `ℤ` coefficients) is a zero object, then so is
the `n`-th singular homology of `X`. -/
theorem isZero_homology_of_homotopyEquiv {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv X Y)
    (n : ℕ)
    (h : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ Y).homology n)) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ X).homology n) := by
  -- Realise the homotopy equivalence as a pair of morphisms in `TopCat` with the required
  -- homotopies.
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  -- Hence `f` induces an isomorphism on singular homology in degree `n`,
  haveI : IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n) :=
    homologyEquiv ℤ X Y f g h1 h2 n
  -- and a zero object is carried to a zero object along an isomorphism.
  exact CategoryTheory.Limits.IsZero.of_iso h
    (CategoryTheory.asIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n))

end

end Work.Cohomology
