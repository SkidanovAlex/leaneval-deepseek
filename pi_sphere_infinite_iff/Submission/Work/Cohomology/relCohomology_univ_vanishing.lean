import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.RelCup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative cohomology of a space modulo itself vanishes

For any space `Y` and any `n`, the relative cohomology `H^n(Y, Y; ℤ)` of the pair `(Y, Y)` is the
zero module: the relative cochain complex of `(Y, Y)` is the kernel of the restriction map
`C^*(Y) ⟶ C^*(Y)`, which is (up to the canonical identification `↥(Set.univ) ≅ Y`) the identity of
`C^*(Y)`; it is an isomorphism, so all its relative cochain groups vanish, and a complex all of
whose terms are zero objects is acyclic (`HomologicalComplex.ExactAt.of_isZero`).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The canonical inclusion `Y ⟶ ↥(Set.univ : Set Y)`. -/
def univInclX (Y : TopCat) : Y ⟶ TopCat.of (Set.univ : Set Y) :=
  TopCat.ofHom ⟨fun y => ⟨y, Set.mem_univ y⟩,
    Continuous.subtype_mk continuous_id (fun y => Set.mem_univ y)⟩

theorem univInclX_comp (Y : TopCat) :
    univInclX Y ≫ subtypeIncl Y (Set.univ : Set Y) = 𝟙 Y := by
  apply TopCat.hom_ext
  ext y
  rfl

/-- The cochain map `C^*(Y) ⟶ C^*(↥univ)` induced by the inclusion of the full subspace. -/
theorem dualChainMap_univIncl_comp (Y : TopCat) (n : ℕ)
    (x : (singularCochainComplex ℤ Y).X n) :
    ((dualChainMap ℤ Y (TopCat.of (Set.univ : Set Y)) (univInclX Y)).f n).hom
        (((dualChainMap ℤ (TopCat.of (Set.univ : Set Y)) Y
          (subtypeIncl Y (Set.univ : Set Y))).f n).hom x) = x := by
  have hid := dualChainMap_comp ℤ (univInclX Y) (subtypeIncl Y (Set.univ : Set Y))
  rw [univInclX_comp Y, dualChainMap_id] at hid
  have h2 := congrArg (fun φ => φ.f n) hid
  have h3 := congrArg ModuleCat.Hom.hom h2
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h3
  have h4 := congrArg (fun (φ : (singularCochainComplex ℤ Y).X n →ₗ[ℤ]
      (singularCochainComplex ℤ Y).X n) => φ x) h3
  simpa using h4.symm

/-- The relative cochains of the pair `(Y, Y)` are zero. -/
theorem relKern_univ_subsingleton (Y : TopCat) (n : ℕ) :
    Subsingleton ↥(relKern ℤ Y (Set.univ : Set Y) n) := by
  have hzero : ∀ a : relKern ℤ Y (Set.univ : Set Y) n,
      (a : (singularCochainComplex ℤ Y).X n) = 0 := by
    intro a
    have hmem : ((dualChainMap ℤ (TopCat.of (Set.univ : Set Y)) Y
        (subtypeIncl Y (Set.univ : Set Y))).f n).hom a.1 = 0 := a.2
    rw [← dualChainMap_univIncl_comp Y n a.1, hmem, map_zero]
  exact ⟨fun a b => Subtype.ext (by rw [hzero a, hzero b])⟩

/-- `H^n(Y, Y) = 0`. -/
theorem relCohomology_univ_vanishing (Y : TopCat) (n : ℕ) :
    Subsingleton (relCohomology ℤ Y Set.univ n) := by
  haveI hX : IsZero ((relComplex ℤ Y (Set.univ : Set Y)).X n) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact relKern_univ_subsingleton Y n
  haveI h : IsZero (HomologicalComplex.homology (relComplex ℤ Y (Set.univ : Set Y)) n) :=
    (HomologicalComplex.ExactAt.of_isZero (K := relComplex ℤ Y (Set.univ : Set Y))
      hX).isZero_homology
  exact ModuleCat.isZero_iff_subsingleton.mp h

end

end Work.Cohomology
