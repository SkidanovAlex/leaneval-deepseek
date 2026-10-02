import Mathlib
import Submission.Work.Cohomology.prod_sphere_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

open CategoryTheory Limits Work.Cohomology

/-- The dual of the inclusion of the small chains induces an isomorphism on cohomology.

Hint: `smallChainsHomotopyEquiv` gives a chain homotopy equivalence `e` with
`e.hom = smallToSing U V` together with the *equation* `e.hom = smallToSing U V` (this is stronger
than a bare `Nonempty`, and it is what makes the identification of the underlying map possible).
Dualising the two homotopies with `dualHomotopy` shows that
`homologyMap (dualComplexMap e.hom) n` and `homologyMap (dualComplexMap e.inv) n` are mutually
inverse (`Homotopy.homologyMap_eq`), so `IsIso` follows by `IsIso.mk`; then rewrite `e.hom` to
`smallToSing U V` using the equation. -/
theorem isIso_smallIsoHom {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) : IsIso (smallIsoHom U V hU hV hcov n) := by
  -- The inclusion of the small chains admits a chain homotopy inverse, with `e.hom` *equal* to
  -- the inclusion itself (not merely homotopic to it).
  obtain ⟨e, he⟩ := smallChainsHomotopyEquiv U V hU hV hcov
  -- Unfold `smallIsoHom`, which is by definition the map induced on cohomology by the dual of
  -- `smallToSing U V`.
  show IsIso (HomologicalComplex.homologyMap
    (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n)
  rw [← he]
  -- The inverse is the map induced on cohomology by the dual of `e.inv`.  Both composites are
  -- homotopic to the identity, because `dualHomotopy` dualises the two homotopies of `e` (with
  -- the two sides interchanged, as the dual is contravariant).
  refine IsIso.mk ⟨HomologicalComplex.homologyMap
    (dualComplexMap ℤ (singularChains ℤ X) (smallChains U V) e.inv) n, ?_, ?_⟩
  · -- `(dual e.hom) ≫ (dual e.inv) = dual (e.inv ≫ e.hom) ≃ dual (𝟙 _) = 𝟙 _`
    rw [← HomologicalComplex.homologyMap_comp,
      ← dualComplexMap_comp (R := ℤ) (f := e.inv) (g := e.hom),
      (dualHomotopy ℤ e.homotopyInvHomId).symm.homologyMap_eq, dualComplexMap_id,
      HomologicalComplex.homologyMap_id]
  · -- `(dual e.inv) ≫ (dual e.hom) = dual (e.hom ≫ e.inv) ≃ dual (𝟙 _) = 𝟙 _`
    rw [← HomologicalComplex.homologyMap_comp,
      ← dualComplexMap_comp (R := ℤ) (f := e.hom) (g := e.inv),
      (dualHomotopy ℤ e.homotopyHomInvId).symm.homologyMap_eq, dualComplexMap_id,
      HomologicalComplex.homologyMap_id]

end Work.Cohomology

