import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.punit
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The positive-degree singular homology of a contractible space

This file proves that the singular chain complex (with coefficients in a commutative ring `R`, in
particular in `ℤ`) of a contractible space `X` has vanishing homology in every positive degree.

The argument has the same shape as `Work.Cohomology.contractible` for cohomology, but with the
chain complex in place of the cochain complex:

* a contractible space is homotopy equivalent to the one-point space `PUnit`
  (`ContractibleSpace.hequiv`), and homotopic maps induce homotopic chain maps on singular chains
  (`TopCat.Homotopy.singularChainComplexFunctorObjMap`), hence equal maps on homology
  (`Homotopy.homologyMap_eq`); so a homotopy equivalence induces an *isomorphism* on singular
  homology (`Work.Cohomology.homologyEquiv` below);
* the singular chain complex of the point is computed explicitly: `Cₙ(PUnit) ≅ R` with
  `d (2j+1) (2j) = 0` and `d (2j+2) (2j+1)` an isomorphism, so it is exact in every positive
  degree, i.e. `Hₙ(PUnit) = 0` for `n > 0` (`Work.Cohomology.homologyPUnit`).

Since a zero object is characterised up to isomorphism, `Hₙ(X) = 0` for `n > 0` as well.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.Cohomology

noncomputable section

/-! ## The vanishing of the homology of the one-point space in positive degrees -/

/-- In even degrees `2j+2` (`j ≥ 0`) the singular chain complex of the point is exact: the
differential `d (2j+3) (2j+2)` vanishes while `d (2j+2) (2j+1)` is an isomorphism. -/
theorem homologyPUnit_even (R : Type) [CommRing R] (j : ℕ) :
    CategoryTheory.Limits.IsZero ((ptChains R).homology (2 * j + 2)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [(ptChains R).exactAt_iff' (2 * j + 3) (2 * j + 2) (2 * j + 1)
    (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (2 * j + 3) (2 * j + 2) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (2 * j + 2) (2 * j + 1) from rfl))]
  have hf : ((ptChains R).sc' (2 * j + 3) (2 * j + 2) (2 * j + 1)).f = 0 := by
    rw [show ((ptChains R).sc' (2 * j + 3) (2 * j + 2) (2 * j + 1)).f
        = (ptChains R).d (2 * j + 3) (2 * j + 2) from rfl]
    rw [show 2 * j + 3 = 2 * (j + 1) + 1 from by omega,
      show 2 * j + 2 = 2 * (j + 1) from by omega]
    exact ptChains_d_zero R (j + 1)
  haveI : IsIso ((ptChains R).d (2 * j + 2) (2 * j + 1)) := isIso_ptChains_d R j
  refine (ShortComplex.exact_iff_mono
    ((ptChains R).sc' (2 * j + 3) (2 * j + 2) (2 * j + 1)) hf).mpr ?_
  change Mono ((ptChains R).d (2 * j + 2) (2 * j + 1))
  infer_instance

/-- In odd degrees `2j+1` the singular chain complex of the point is exact: the differential
`d (2j+1) (2j)` vanishes while `d (2j+2) (2j+1)` is an isomorphism. -/
theorem homologyPUnit_odd (R : Type) [CommRing R] (j : ℕ) :
    CategoryTheory.Limits.IsZero ((ptChains R).homology (2 * j + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [(ptChains R).exactAt_iff' (2 * j + 2) (2 * j + 1) (2 * j)
    (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (2 * j + 2) (2 * j + 1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (2 * j + 1) (2 * j) from rfl))]
  have hg : ((ptChains R).sc' (2 * j + 2) (2 * j + 1) (2 * j)).g = 0 := by
    rw [show ((ptChains R).sc' (2 * j + 2) (2 * j + 1) (2 * j)).g
        = (ptChains R).d (2 * j + 1) (2 * j) from rfl]
    exact ptChains_d_zero R j
  haveI : IsIso ((ptChains R).d (2 * j + 2) (2 * j + 1)) := isIso_ptChains_d R j
  refine (ShortComplex.exact_iff_epi
    ((ptChains R).sc' (2 * j + 2) (2 * j + 1) (2 * j)) hg).mpr ?_
  change Epi ((ptChains R).d (2 * j + 2) (2 * j + 1))
  infer_instance

/-- The singular homology of the one-point space vanishes in every positive degree. -/
theorem homologyPUnit (R : Type) [CommRing R] (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero ((ptChains R).homology n) := by
  rcases Nat.even_or_odd n with hn' | hn'
  · obtain ⟨j, hj⟩ := hn'
    rw [show n = 2 * (j - 1) + 2 from by omega]
    exact homologyPUnit_even R (j - 1)
  · obtain ⟨j, hj⟩ := hn'
    rw [show n = 2 * j + 1 from by omega]
    exact homologyPUnit_odd R j

/-! ## Homotopy invariance of singular homology -/

/-- Two homotopic continuous maps induce equal maps on singular homology.  Equivalently (via
`IsIso.mk`), a homotopy equivalence of spaces induces an *isomorphism* on singular homology in
every degree. -/
theorem homologyEquiv (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (g : Y ⟶ X)
    (h1 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f g)
      (CategoryTheory.CategoryStruct.id X))
    (h2 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g f)
      (CategoryTheory.CategoryStruct.id Y)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (chainMap R X Y f) n) := by
  have hcomp1 : chainMap R X Y f ≫ chainMap R Y X g = chainMap R X X (f ≫ g) := by
    simp only [chainMap, Functor.map_comp]
  have hcomp2 : chainMap R Y X g ≫ chainMap R X Y f = chainMap R Y Y (g ≫ f) := by
    simp only [chainMap, Functor.map_comp]
  have hid1 : chainMap R X X (𝟙 X) = 𝟙 (singularChains R X) := by
    simp only [chainMap, CategoryTheory.Functor.map_id]
  have hid2 : chainMap R Y Y (𝟙 Y) = 𝟙 (singularChains R Y) := by
    simp only [chainMap, CategoryTheory.Functor.map_id]
  have hh1 : Homotopy (chainMap R X X (f ≫ g)) (chainMap R X X (𝟙 X)) :=
    h1.singularChainComplexFunctorObjMap (ModuleCat.of R R)
  have hh2 : Homotopy (chainMap R Y Y (g ≫ f)) (chainMap R Y Y (𝟙 Y)) :=
    h2.singularChainComplexFunctorObjMap (ModuleCat.of R R)
  refine IsIso.mk ⟨HomologicalComplex.homologyMap (chainMap R Y X g) n, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, hcomp1, Homotopy.homologyMap_eq hh1 n, hid1,
      HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, hcomp2, Homotopy.homologyMap_eq hh2 n, hid2,
      HomologicalComplex.homologyMap_id]

/-! ## The positive-degree singular homology of a contractible space -/

/-- The positive-degree singular homology of a contractible space vanishes, with coefficients in
any commutative ring `R`. -/
theorem homologyContractible_ring (R : Type) [CommRing R] {X : TopCat} [ContractibleSpace X]
    (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains R X).homology n) := by
  -- `X` is homotopy equivalent to the one-point space
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit
  let f : X ⟶ TopCat.of PUnit := TopCat.ofHom e.toFun
  let g : TopCat.of PUnit ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of PUnit)) := e.right_inv.some
  -- so `Hₙ(X) ≅ Hₙ(PUnit)`, and the latter is a zero object
  haveI : IsIso (HomologicalComplex.homologyMap (chainMap R X (TopCat.of PUnit) f) n) :=
    homologyEquiv R X (TopCat.of PUnit) f g h1 h2 n
  exact CategoryTheory.Limits.IsZero.of_iso (homologyPUnit R n hn)
    (CategoryTheory.asIso (HomologicalComplex.homologyMap (chainMap R X (TopCat.of PUnit) f) n))

/-- **The positive-degree singular homology of a contractible space vanishes** (with `ℤ`
coefficients). -/
theorem homologyContractible {X : TopCat} [ContractibleSpace X] (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ X).homology n) :=
  homologyContractible_ring ℤ n hn

end

end Work.Cohomology
