import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.CoreClass
import Submission.Work.Orient.Boundary.HalfCompactZero
import Submission.Work.Orient.Boundary.HalfCoverGlue
import Submission.Work.Orient.Boundary.HalfCover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative fundamental class from the core isomorphism

This file proves `Work.Orient.Boundary.RelFundClassOfCoreIso`: from the *geometric* input
`Work.Orient.CoreIsoAllCoresProp` — the existence of a compact core `C₀` of the interior such that the
restriction of pairs `H_{n+1}(W, ∂W) ⟶ H_{n+1}(W, W∖C)` is an isomorphism for every compact
`C ⊇ C₀` of the interior — and an orientation family `γ` on `W`, one obtains a relative fundamental
class `w ∈ H_{n+1}(W, ∂W)`.

The proof has three ingredients, the first two of which are pure homological algebra proved here:

* `Work.Orient.Boundary.exists_coreClass` (already in the directory) produces, over *any* compact
  subset `C` of the interior, a class `u_C ∈ H_{n+1}(W, W∖C)` whose localisation at every point of
  `C` is the generator `γ`;

* **uniqueness over a compact set of the interior** (`Work.Orient.Boundary.HalfCompactZero`) shows
  that the classes `u_C` are compatible: for `C ⊆ C'` one has `resRelH (C ⊆ C') u_{C'} = u_C`;

* the isomorphism of `CoreIsoProp` then transports `u_{C₀}` back to `H_{n+1}(W, ∂W)`, and the
  localisation of the resulting class at an arbitrary interior point `x` is computed by choosing
  `C' = C₀ ∪ K` with `K` a coordinate half-ball around `x` inside the interior: the restriction of
  the class along `∂W ⊆ C'ᶜ ⊆ {x}ᶜ` is the localisation of `u_{C'}` at `x`, i.e. `γ x`.
-/

/-! ## WARNING

The hypothesis `Work.Orient.CoreIsoAllCoresProp` of this lemma is **false**
(`Work.Orient.CoreIsoProp` in `Boundary.lean` carries the refutation: for `W = [0,1]` and
`C = C₀ ∪ (c,d)` the group `H_1(W, W∖C)` gains a free summand), so this lemma is a *vacuous*
implication.  It is kept as the record of the (instructive) route; the same route with the corrected
hypothesis `Work.Orient.CoreIsoProp` needs, in addition, the *local constancy of the local degree*
(the arbitrary-point form of `Work.Orient.Boundary.HalfRestrictIso`) instead of the comparison of two
cores. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold
open Work.ThomBordism
open Work.Orient.Port

namespace Work.Orient.Boundary

noncomputable section

/-! ## The chain-level API of the relative inclusions -/

/-- `chainMap` of the identity is the identity. -/
theorem chainMap_identity (X : TopCat) :
    Work.Cohomology.chainMap ℤ X X (𝟙 X) = 𝟙 (Work.Cohomology.singularChains ℤ X) :=
  CategoryTheory.Functor.map_id _ _

/-- The projection `cokernel.π` is natural with respect to the relative inclusion. -/
theorem relChainsIncl_π (X : TopCat) {A B : Set X} (h : A ⊆ B) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)
      ≫ Work.Orient.relChainsIncl X h
    = CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X B) := by
  rw [Work.Orient.relChainsIncl, Work.Cohomology.relChainsMapOf,
    Work.Cohomology.cokernel_π_map, chainMap_identity, Category.id_comp]

/-- **Functoriality of the relative inclusions.** -/
theorem relChainsIncl_fac (X : TopCat) {A B C : Set X} (h1 : A ⊆ B) (h2 : B ⊆ C)
    (h3 : A ⊆ C) :
    Work.Orient.relChainsIncl X h1 ≫ Work.Orient.relChainsIncl X h2
      = Work.Orient.relChainsIncl X h3 := by
  apply (CategoryTheory.cancel_epi
    (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [← Category.assoc, relChainsIncl_π X h1, relChainsIncl_π X h2, relChainsIncl_π X h3]

/-- The relative inclusion depends only on the underlying inclusion of sets: Lean's
definitional proof irrelevance makes the two maps definitionally equal. -/
theorem relChainsIncl_congr (X : TopCat) {A B : Set X} (h h' : A ⊆ B) :
    Work.Orient.relChainsIncl X h = Work.Orient.relChainsIncl X h' := rfl

/-- The relative inclusion agrees with `relCokerMap`. -/
theorem relChainsIncl_eq_relCokerMap_aux (X : TopCat) {A B : Set X} (h h' : A ⊆ B) :
    Work.Orient.relChainsIncl X h' = Work.Cohomology.relCokerMap X A B h := by
  apply (CategoryTheory.cancel_epi
    (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [relChainsIncl_π X h', Work.Cohomology.relCokerMap_comp_π]

/-- **The restriction map of relative homology is the homology of the relative inclusion.** -/
theorem resRelH_eq_relChainsIncl (M : TopCat) (m : ℕ) {A B : Set M} (h : A ⊆ B)
    (h' : Bᶜ ⊆ Aᶜ) :
    resRelH M m h = (HomologicalComplex.homologyMap
      (Work.Orient.relChainsIncl M (A := Bᶜ) (B := Aᶜ) h') m).hom := by
  have h1 : resRelH M m h = (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap M Bᶜ Aᶜ (Set.compl_subset_compl.mpr h)) m).hom := rfl
  rw [h1, relChainsIncl_eq_relCokerMap_aux M (A := Bᶜ) (B := Aᶜ)
    (Set.compl_subset_compl.mpr h) h']

/-! ## The main theorem -/

theorem RelFundClassOfCoreIso (n : ℕ) (h : Work.Orient.CoreIsoAllCoresProp n)
    (W : TopCat) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      Work.Orient.LocH W (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n W γ) :
    ∃ w : (Work.Cohomology.relChains W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1),
      Work.Orient.IsRelFundClass W (n + 1) ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) w := by
  classical
  let B : Set W := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
  have hBclosed : IsClosed B :=
    ModelWithCorners.isClosed_boundary (I := modelWithCornersEuclideanHalfSpace (n + 1))
      (M := W) (n := 1) (by norm_num)
  obtain ⟨C₀, hC₀cpt, hC₀int, hiso⟩ := h W
  obtain ⟨u, hu⟩ := exists_coreClass n W hC₀cpt hC₀int γ hγ
  have hA : B ⊆ C₀ᶜ := fun y hy hyc => hC₀int y hyc hy
  let F₀ := HomologicalComplex.homologyMap
    (Work.Orient.relChainsIncl W (A := B) (B := C₀ᶜ) hA) (n + 1)
  haveI hF₀iso : IsIso F₀ := hiso C₀ hC₀cpt (Set.Subset.refl C₀) hC₀int
  have hF₀u : F₀.hom ((CategoryTheory.inv F₀).hom u) = u := by
    have hc : ModuleCat.Hom.hom (CategoryTheory.inv F₀ ≫ F₀) = LinearMap.id := by
      rw [CategoryTheory.IsIso.inv_hom_id, ModuleCat.hom_id]
    rw [ModuleCat.hom_comp] at hc
    exact LinearMap.congr_fun hc u
  refine ⟨(CategoryTheory.inv F₀).hom u, ?_⟩
  intro x hx
  obtain ⟨r, hr, hgood, hKsub⟩ :=
    exists_halfBall_subset n (W := W) (U := Bᶜ) hBclosed.isOpen_compl hx
  set K : Set W := halfBallPiece (n + 1) W x r with hKdef
  have hKcpt : IsCompact K := halfBallPiece_isCompact (n := n + 1) x r hr hgood
  have hxK : x ∈ K := mem_halfBallPiece_center (n := n + 1) hr
  set C' : Set W := C₀ ∪ K with hC'def
  have hC'cpt : IsCompact C' := hC₀cpt.union hKcpt
  have hC₀sub : C₀ ⊆ C' := Set.subset_union_left
  have hC'int : ∀ y ∈ C', y ∉ B := by
    intro y hy
    rcases hy with hy | hy
    · exact hC₀int y hy
    · exact hKsub hy
  have hxC' : x ∈ C' := Or.inr hxK
  have hB1 : B ⊆ C'ᶜ := fun y hy hyc => hC'int y hyc hy
  have hcomp : C'ᶜ ⊆ C₀ᶜ := Set.compl_subset_compl.mpr hC₀sub
  have hK' : C'ᶜ ⊆ {y : W | y ≠ x} := fun y hy hyx => hy (hyx ▸ hxC')
  let F' := HomologicalComplex.homologyMap
    (Work.Orient.relChainsIncl W (A := B) (B := C'ᶜ) hB1) (n + 1)
  haveI hF'iso : IsIso F' := hiso C' hC'cpt hC₀sub hC'int
  let H' := HomologicalComplex.homologyMap
    (Work.Orient.relChainsIncl W (A := C'ᶜ) (B := C₀ᶜ) hcomp) (n + 1)
  obtain ⟨u', hu'⟩ := exists_coreClass n W hC'cpt hC'int γ hγ
  -- the classes `u` and `u'` agree on `C₀` (uniqueness over a compact set of the interior)
  have hres : resRelH W (n + 1) hC₀sub u' = u := by
    have h0 : resRelH W (n + 1) hC₀sub u' - u = 0 := by
      refine HalfCompactZero n W hC₀cpt hC₀int _ ?_
      intro y hy
      have h2 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr hy)
          (resRelH W (n + 1) hC₀sub u')
          = resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hC₀sub hy)) u' :=
        LinearMap.congr_fun (RelHmap_comp' W (n + 1) (Set.singleton_subset_iff.mpr hy) hC₀sub
          (Set.singleton_subset_iff.mpr (hC₀sub hy))) u'
      calc resRelH W (n + 1) (Set.singleton_subset_iff.mpr hy)
              (resRelH W (n + 1) hC₀sub u' - u)
          = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hy) (resRelH W (n + 1) hC₀sub u')
            - resRelH W (n + 1) (Set.singleton_subset_iff.mpr hy) u := map_sub _ _ _
        _ = resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hC₀sub hy)) u'
            - resRelH W (n + 1) (Set.singleton_subset_iff.mpr hy) u := by rw [h2]
        _ = γ y (hC'int y (hC₀sub hy)) - γ y (hC₀int y hy) := by
              rw [hu' y (hC₀sub hy), hu y hy]
        _ = 0 := sub_self _
    exact sub_eq_zero.mp h0
  -- the factorisation `F₀ = F' ≫ H'`
  have hfacF : F₀ = F' ≫ H' := by
    change HomologicalComplex.homologyMap
        (Work.Orient.relChainsIncl W (A := B) (B := C₀ᶜ) hA) (n + 1)
      = HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := B) (B := C'ᶜ) hB1) (n + 1)
        ≫ HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := C'ᶜ) (B := C₀ᶜ) hcomp) (n + 1)
    rw [← HomologicalComplex.homologyMap_comp]
    congr 1
    rw [relChainsIncl_fac W hB1 hcomp hA]
  haveI : IsIso (F' ≫ H') := hfacF ▸ hF₀iso
  haveI hH'iso : IsIso H' := IsIso.of_isIso_comp_left F' H'
  have hH'inj : Function.Injective H'.hom :=
    (ModuleCat.mono_iff_injective H').mp inferInstance
  have hH'eq : H'.hom = resRelH W (n + 1) hC₀sub :=
    (resRelH_eq_relChainsIncl W (n + 1) hC₀sub hcomp).symm
  have hF₀hom : F₀.hom = H'.hom ∘ₗ F'.hom := by
    rw [hfacF, ModuleCat.hom_comp]
  have hF'w : F'.hom ((CategoryTheory.inv F₀).hom u) = u' := by
    apply hH'inj
    have h1 : H'.hom (F'.hom ((CategoryTheory.inv F₀).hom u)) = u := by
      rw [← LinearMap.comp_apply, ← hF₀hom]
      exact hF₀u
    rw [h1, hH'eq]
    exact hres.symm
  -- the localisation of `w` at the interior point `x`
  have hrelPunct : Work.Orient.relPunct W B x hx
      = Work.Orient.relChainsIncl W (A := B) (B := C'ᶜ) hB1
        ≫ Work.Orient.relChainsIncl W (A := C'ᶜ) (B := {y : W | y ≠ x}) hK' := by
    rw [show Work.Orient.relPunct W B x hx
        = Work.Orient.relChainsIncl W (A := B) (B := {y : W | y ≠ x})
            (fun y hy hyx => hx (hyx ▸ hy)) from rfl,
      relChainsIncl_fac W hB1 hK' (fun y hy hyx => hx (hyx ▸ hy))]
  have stepA : (HomologicalComplex.homologyMap (Work.Orient.relPunct W B x hx) (n + 1)).hom
        ((CategoryTheory.inv F₀).hom u)
      = (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W (A := C'ᶜ)
          (B := {y : W | y ≠ x}) hK') (n + 1)).hom
        (F'.hom ((CategoryTheory.inv F₀).hom u)) := by
    rw [hrelPunct, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    rfl
  have hxsub : ({x} : Set W) ⊆ C' := Set.singleton_subset_iff.mpr hxC'
  have stepB : (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W (A := C'ᶜ)
        (B := {y : W | y ≠ x}) hK') (n + 1)).hom = resRelH W (n + 1) hxsub :=
    (resRelH_eq_relChainsIncl W (n + 1) hxsub hK').symm
  have hloc : (HomologicalComplex.homologyMap (Work.Orient.relPunct W B x hx) (n + 1)).hom
        ((CategoryTheory.inv F₀).hom u) = γ x hx := by
    rw [stepA, hF'w, stepB]
    exact hu' x hxC'
  rw [hloc]
  exact hγ.1 x hx

end

end Work.Orient.Boundary
