import Submission.Work.ThreeConnected.Excision.Cover
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.RelMVLes

/-!
# Relative homology vanishes over a deformation retract

Let `A ⊆ X`.  If the inclusion `i : A ⟶ X` has a retraction `r : X ⟶ A` with `r ∘ i = id_A` and a
homotopy `i ∘ r ≃ id_X`, then the relative homology of the pair `(X, A)` vanishes in every positive
degree; and `i` induces an isomorphism on homology in every degree.

The degree `0` case of the vanishing needs the identification of `H₀` of a pair with the cokernel of
`H₀(A) ⟶ H₀(X)` and is *not* proved here (see `README.md` §3.2).

## Main results

* `Work.ThreeConnected.homeoInterAU` — the canonical homeomorphism between `A` and `A` viewed as a
  subset of `U` (for `A ⊆ U`);
* `Work.ThreeConnected.Excision.isIso_chainMap_of_homotopy_retract`;
* `Work.ThreeConnected.Excision.homologyMap_cokernel_pi_eq_zero`;
* `Work.ThreeConnected.Excision.isZero_relChains_of_retract_succ`;
* `Work.ThreeConnected.Excision.isZero_relChains_of_deformationRetractPair_succ`;
* `Work.ThreeConnected.Excision.isIso_inclChains_of_deformationRetractPair`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Manifold Topology ContDiff
open Classical

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

/-- **The canonical homeomorphism between `A` and `A` viewed as a subset of `U`**, for `A ⊆ U`: both
are the set of points of `X` lying in `A`. -/
def homeoInterAU {X : TopCat.{0}} {A U : Set X} (h : A ⊆ U) :
    TopCat.of A ≅ TopCat.of (interAU A U) where
  hom := TopCat.ofHom ⟨fun a => (⟨⟨a.1, h a.2⟩, a.2⟩ : ↥(interAU A U)), by fun_prop⟩
  inv := TopCat.ofHom ⟨fun b => (⟨b.1.1, b.2⟩ : ↥A), by fun_prop⟩
  hom_inv_id := by
    apply TopCat.hom_ext
    ext a
    rfl
  inv_hom_id := by
    apply TopCat.hom_ext
    ext b
    rfl

end

namespace Excision

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

variable {X Y : TopCat.{0}}

/-- **A homotopy equivalence of spaces induces an isomorphism on homology.**  If `f : Y ⟶ X` and
`r : X ⟶ Y` satisfy `f ≫ r = 𝟙 Y` and `r ≫ f ≃ 𝟙 X`, then `f` induces an isomorphism on singular
homology in every degree. -/
theorem isIso_chainMap_of_homotopy_retract (f : Y ⟶ X) (r : X ⟶ Y) (h1 : f ≫ r = 𝟙 Y)
    (H : Nonempty (TopCat.Homotopy (r ≫ f) (𝟙 X))) :
    ∀ j, IsIso (HomologicalComplex.homologyMap (chainMap ℤ Y X f) j) := by
  intro j
  obtain ⟨H⟩ := H
  have hC : Homotopy (chainMap ℤ X Y r ≫ chainMap ℤ Y X f) (𝟙 (singularChains ℤ X)) := by
    have hthis := H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
    simpa only [chainMap, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      using hthis
  have hid2 : chainMap ℤ Y Y (𝟙 Y) = 𝟙 (singularChains ℤ Y) :=
    CategoryTheory.Functor.map_id _ _
  have hsplit : HomologicalComplex.homologyMap (chainMap ℤ Y X f) j
      ≫ HomologicalComplex.homologyMap (chainMap ℤ X Y r) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      show chainMap ℤ Y X f ≫ chainMap ℤ X Y r = chainMap ℤ Y Y (f ≫ r) from by
        simp only [chainMap, Functor.map_comp],
      h1, hid2, HomologicalComplex.homologyMap_id]
  refine IsIso.mk ⟨HomologicalComplex.homologyMap (chainMap ℤ X Y r) j, hsplit, ?_⟩
  rw [← HomologicalComplex.homologyMap_comp, Homotopy.homologyMap_eq hC j,
    HomologicalComplex.homologyMap_id]

/-- **The composite with the projection to the relative complex is null-homotopic.**  If
`r ≫ f ≃ 𝟙 X` then `C_*(X) ⟶ C_*(X)/C_*(Y)` is homotopic to `0`, hence induces `0` on homology. -/
theorem homologyMap_cokernel_pi_eq_zero (f : Y ⟶ X) (r : X ⟶ Y)
    (H : Nonempty (TopCat.Homotopy (r ≫ f) (𝟙 X))) (j : ℕ) :
    HomologicalComplex.homologyMap (cokernel.π (chainMap ℤ Y X f)) j = 0 := by
  obtain ⟨H⟩ := H
  have hC : Homotopy (chainMap ℤ X Y r ≫ chainMap ℤ Y X f) (𝟙 (singularChains ℤ X)) := by
    have hthis := H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
    simpa only [chainMap, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      using hthis
  have hc : chainMap ℤ Y X f ≫ cokernel.π (chainMap ℤ Y X f) = 0 := cokernel.condition _
  have hq : Homotopy (0 : singularChains ℤ X ⟶ cokernel (chainMap ℤ Y X f))
      (cokernel.π (chainMap ℤ Y X f)) := by
    have h0 := hC.compRight (cokernel.π (chainMap ℤ Y X f))
    rw [Category.assoc, hc, comp_zero, Category.id_comp] at h0
    exact h0
  rw [← Homotopy.homologyMap_eq hq j, HomologicalComplex.homologyMap_zero]

end

end Excision

namespace Excision

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

/-- **The relative homology of a pair vanishes over a deformation retract** (positive degrees).  If
`i : A ⟶ X` is the inclusion of `A ⊆ X` and `r : X ⟶ A` satisfies `r ∘ i = id_A` and
`i ∘ r ≃ id_X`, then `H_j(X,A) = 0` for every `j ≥ 1`. -/
theorem isZero_relChains_of_retract_succ {X : TopCat.{0}} {A : Set X}
    (r : X ⟶ TopCat.of A) (i : TopCat.of A ⟶ X) (hi : i = subtypeIncl X A)
    (h1 : i ≫ r = 𝟙 (TopCat.of A)) (H : Nonempty (TopCat.Homotopy (r ≫ i) (𝟙 X))) :
    ∀ j, IsZero ((relChains X A).homology (j + 1)) := by
  subst hi
  intro j
  have hπ : HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) (j + 1) = 0 :=
    homologyMap_cokernel_pi_eq_zero (subtypeIncl X A) r H (j + 1)
  have hcomp : chainMap ℤ (TopCat.of A) X (subtypeIncl X A) ≫ chainMap ℤ X (TopCat.of A) r
      = 𝟙 (singularChains ℤ (TopCat.of A)) := by
    have hmap : chainMap ℤ (TopCat.of A) X (subtypeIncl X A) ≫ chainMap ℤ X (TopCat.of A) r
        = chainMap ℤ (TopCat.of A) (TopCat.of A) (subtypeIncl X A ≫ r) := by
      simp only [chainMap, Functor.map_comp]
    rw [hmap, h1, show chainMap ℤ (TopCat.of A) (TopCat.of A) (𝟙 (TopCat.of A)) = 𝟙 _ from
      CategoryTheory.Functor.map_id _ _]
  have hsplit : HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) j
      ≫ HomologicalComplex.homologyMap (chainMap ℤ X (TopCat.of A) r) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_id]
  have hretract : ∀ z : ((singularChains ℤ (TopCat.of A)).homology j),
      (HomologicalComplex.homologyMap (chainMap ℤ X (TopCat.of A) r) j)
        ((HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) j) z) = z := by
    intro z
    have := congrArg (fun (g : ((singularChains ℤ (TopCat.of A)).homology j) ⟶
        ((singularChains ℤ (TopCat.of A)).homology j)) => g z) hsplit
    simpa using this
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) j).hom := by
    intro x y hxy
    rw [← hretract x, ← hretract y, hxy]
  have hδmono : Mono (Work.Cohomology.hPairδ X A j) :=
    (Work.Cohomology.hPair_exact₃ X A j).mono_g hπ
  have hδinj : Function.Injective (Work.Cohomology.hPairδ X A j).hom :=
    (ModuleCat.mono_iff_injective _).mp hδmono
  have hrange : LinearMap.range (Work.Cohomology.hPairδ X A j).hom = ⊥ := by
    rw [ShortComplex.Exact.moduleCat_range_eq_ker (Work.Cohomology.hPair_exact₁ X A j),
      LinearMap.ker_eq_bot]
    exact hinj
  refine (ModuleCat.isZero_iff_subsingleton).mpr ⟨fun x y => ?_⟩
  have hx : (Work.Cohomology.hPairδ X A j).hom x = 0 := by
    have hmem : (Work.Cohomology.hPairδ X A j).hom x ∈
        LinearMap.range (Work.Cohomology.hPairδ X A j).hom := ⟨x, rfl⟩
    rw [hrange] at hmem
    simpa using hmem
  have hy : (Work.Cohomology.hPairδ X A j).hom y = 0 := by
    have hmem : (Work.Cohomology.hPairδ X A j).hom y ∈
        LinearMap.range (Work.Cohomology.hPairδ X A j).hom := ⟨y, rfl⟩
    rw [hrange] at hmem
    simpa using hmem
  rw [← hδinj.eq_iff, hx, hy]

/-- **The canonical inclusion of a subset into a larger subset**, as a morphism of spaces. -/
def inclSubtype {X : TopCat.{0}} {B C : Set X} (hBC : B ⊆ C) : TopCat.of B ⟶ TopCat.of C :=
  TopCat.ofHom ⟨fun b => (⟨b.1, hBC b.2⟩ : C), by fun_prop⟩

/-- The map `TopCat.of U ⟶ TopCat.of (interAU A U)` obtained from a retraction `U ⟶ A` and the
canonical identification of `A` with its copy inside `U`. -/
def retractInterAU {X : TopCat.{0}} {A U : Set X} (hAU : A ⊆ U) (r : TopCat.of U ⟶ TopCat.of A) :
    TopCat.of U ⟶ TopCat.of (interAU A U) :=
  r ≫ (homeoInterAU (X := X) hAU).hom

theorem subtypeIncl_interAU_eq {X : TopCat.{0}} {A U : Set X} (hAU : A ⊆ U)
    (i : TopCat.of A ⟶ TopCat.of U) (hi : ∀ a : A, i a = (⟨a.1, hAU a.2⟩ : U)) :
    subtypeIncl (TopCat.of U) (interAU A U)
      = (homeoInterAU (X := X) hAU).inv ≫ i := by
  apply TopCat.hom_ext
  ext b
  have h : (b.1 : U) = i (⟨b.1.1, b.2⟩ : A) := by rw [hi]
  exact congrArg (fun z : U => (z : X)) h

theorem subtypeIncl_comp_retractInterAU {X : TopCat.{0}} {A U : Set X} (hAU : A ⊆ U)
    (r : TopCat.of U ⟶ TopCat.of A) (i : TopCat.of A ⟶ TopCat.of U)
    (hi : subtypeIncl (TopCat.of U) (interAU A U)
      = (homeoInterAU (X := X) hAU).inv ≫ i) (hcomp : i ≫ r = 𝟙 (TopCat.of A)) :
    subtypeIncl (TopCat.of U) (interAU A U) ≫ retractInterAU hAU r
      = 𝟙 (TopCat.of (interAU A U)) := by
  rw [retractInterAU, hi, ← Category.assoc]
  rw [Category.assoc ((homeoInterAU (X := X) hAU).inv) i r]
  rw [hcomp, Category.comp_id]
  exact Iso.inv_hom_id _

theorem retractInterAU_comp_subtypeIncl {X : TopCat.{0}} {A U : Set X} (hAU : A ⊆ U)
    (r : TopCat.of U ⟶ TopCat.of A) (i : TopCat.of A ⟶ TopCat.of U)
    (hi : subtypeIncl (TopCat.of U) (interAU A U)
      = (homeoInterAU (X := X) hAU).inv ≫ i) :
    retractInterAU hAU r ≫ subtypeIncl (TopCat.of U) (interAU A U) = r ≫ i := by
  rw [retractInterAU, hi, Category.assoc r (homeoInterAU (X := X) hAU).hom
    ((homeoInterAU (X := X) hAU).inv ≫ i)]
  rw [← Category.assoc ((homeoInterAU (X := X) hAU).hom) ((homeoInterAU (X := X) hAU).inv) i]
  rw [Iso.hom_inv_id, Category.id_comp]

/-- **The relative homology of `(U, U ∩ A)` vanishes in positive degrees when `A` is a deformation
retract of `U`.** -/
theorem isZero_relChains_of_deformationRetractPair_succ
    {X : TopCat.{0}} {U A : Set X} (h : IsDeformationRetractPair (X := X) U A) :
    ∀ j, IsZero ((relChains (TopCat.of U) (interAU A U)).homology (j + 1)) := by
  obtain ⟨hAU, r, i, hi, hr, H⟩ := h
  have hcomp : i ≫ r = 𝟙 (TopCat.of A) := by
    apply TopCat.hom_ext
    ext a
    exact congrArg (fun z : A => (z : X)) (hr a)
  have hfi := subtypeIncl_interAU_eq hAU i hi
  refine isZero_relChains_of_retract_succ (retractInterAU hAU r)
    (subtypeIncl (TopCat.of U) (interAU A U)) rfl
    (subtypeIncl_comp_retractInterAU hAU r i hfi hcomp) ?_
  obtain ⟨H⟩ := H
  exact ⟨by rw [retractInterAU_comp_subtypeIncl hAU r i hfi]; exact H⟩

/-- **The inclusion of `A` into `U` is a homology isomorphism when `A` is a deformation retract of
`U`.** -/
theorem isIso_inclChains_of_deformationRetractPair
    {X : TopCat.{0}} {U A : Set X} (h : IsDeformationRetractPair (X := X) U A) :
    ∀ j, IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of (interAU A U)) (TopCat.of U)
        (subtypeIncl (TopCat.of U) (interAU A U))) j) := by
  obtain ⟨hAU, r, i, hi, hr, H⟩ := h
  have hcomp : i ≫ r = 𝟙 (TopCat.of A) := by
    apply TopCat.hom_ext
    ext a
    exact congrArg (fun z : A => (z : X)) (hr a)
  have hfi := subtypeIncl_interAU_eq hAU i hi
  have h1 := subtypeIncl_comp_retractInterAU hAU r i hfi hcomp
  obtain ⟨H⟩ := H
  refine isIso_chainMap_of_homotopy_retract (subtypeIncl (TopCat.of U) (interAU A U))
    (retractInterAU hAU r) h1 ?_
  exact ⟨by rw [retractInterAU_comp_subtypeIncl hAU r i hfi]; exact H⟩

end

end Excision

end Work.ThreeConnected
