import Mathlib
import Submission.Work.Homology.MayerVietoris
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.SmallChains

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology Simplicial Limits

/-!
# Surjectivity of the degree-zero Mayer–Vietoris map `H₀(U) ⊞ H₀(V) → H₀(X)`

For an open cover `X = U ∪ V`, the Mayer–Vietoris map

`mvRightX U V hU hV hcov 0 : H₀(U) ⊞ H₀(V) ⟶ H₀(X)`

is surjective: the degree-zero part of the Mayer–Vietoris sequence ends in `H₀(X)`, because there
is no term below degree `0`.

The proof is purely formal.  The chain-level Mayer–Vietoris map `mvRight U V` is an epimorphism of
chain complexes, since `mvShort U V` is short exact (`mvShort_shortExact`); a morphism of
homological complexes is an epimorphism exactly when it is degreewise so, hence `mvRight.f 0` is
epi.  A degreewise epimorphism induces an epimorphism on homology in degree `0`, because there is
no outgoing differential from degree `0` for the complex shape `down ℕ`
(`HomologicalComplex.epi_homologyMap_of_epi_of_not_rel`).  Composing with the small-chains
isomorphism `smallIso` — an isomorphism, hence an epimorphism — gives the claim.
-/

namespace Work.Final

theorem mvRightX_zero_surjective {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    (Work.Cohomology.mvRightX U V hU hV hcov 0).hom.range = ⊤ := by
  -- `mvRight` is an epimorphism of chain complexes, hence so is its degree-`0` component.
  have hEpiR : Epi (Work.Cohomology.mvRight U V) :=
    (Work.Cohomology.mvShort_shortExact U V).epi_g
  have hEpi0 : Epi ((Work.Cohomology.mvRight U V).f 0) := inferInstance
  -- In degree `0` the differential `d 0 (-1)` is out of the range of the index set `ℕ`, so an
  -- epimorphism in degree `0` induces an epimorphism on homology in degree `0`.
  have hEpiH : Epi (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0
      (by intro j; simp [ComplexShape.down])
  -- `mvRightX` is `homologyMap mvRight 0` followed by the (iso, hence epi) small-chains map.
  have hEpiX : Epi (Work.Cohomology.mvRightX U V hU hV hcov 0) := by
    rw [Work.Cohomology.mvRightX]
    exact epi_comp _ _
  exact (ModuleCat.epi_iff_range_eq_top _).mp hEpiX

end Work.Final
