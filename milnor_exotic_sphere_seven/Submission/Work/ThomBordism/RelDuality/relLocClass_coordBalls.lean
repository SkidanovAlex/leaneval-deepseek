import Mathlib
import Submission.Work.ThomBordism.RelDuality.Supp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]

section Dside

variable [T2Space (Double 8 M)] [CompactSpace (Double 8 M)]
  [ChartedSpace (EuclideanSpace ℝ (Fin 9)) (Double 8 M)]

/-- `suppMap_natural` at the level of homology morphisms. -/
theorem suppMap_natural_hom {K K' : Set M} {L L' : Set (Double 8 M)} (hKK' : K ⊆ K')
    (hLL' : L ⊆ L') (h : SuppObs K L) (h' : SuppObs K' L') :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (suppMap (M := M) K' L' h') 9)
        (HomologicalComplex.homologyMap
          (Work.Cohomology.relCokerMap (TopCat.of (Double 8 M)) (L'ᶜ) (Lᶜ)
            (Set.compl_subset_compl.mpr hLL')) 9)
      = CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap
          (Work.Cohomology.relCokerMap (TopCat.of M) (K'ᶜ) (Kᶜ)
            (Set.compl_subset_compl.mpr hKK')) 9)
        (HomologicalComplex.homologyMap (suppMap (M := M) K L h) 9) := by
  rw [show (Set.compl_subset_compl.mpr hLL') = (fun x hxL' hxL => hxL' (hLL' hxL)) from rfl,
    show (Set.compl_subset_compl.mpr hKK') = (fun x hxK' hxK => hxK' (hKK' hxK)) from rfl]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    suppMap_natural (M := M) (K := K) (K' := K') (L := L) (L' := L') hKK' hLL' h h']

/-- `suppMap_natural` at the level of elements. -/
theorem suppMap_natural_apply {K K' : Set M} {L L' : Set (Double 8 M)} (hKK' : K ⊆ K')
    (hLL' : L ⊆ L') (h : SuppObs K L) (h' : SuppObs K' L') (u : RelH (TopCat.of M) 9 K') :
    RelHmap (TopCat.of (Double 8 M)) 9 hLL'
        ((HomologicalComplex.homologyMap (suppMap (M := M) K' L' h') 9) u)
      = (HomologicalComplex.homologyMap (suppMap (M := M) K L h) 9)
          (RelHmap (TopCat.of M) 9 hKK' u) := by
  rw [RelHmap, RelHmap]
  have h1 := suppMap_natural_hom (M := M) hKK' hLL' h h'
  have h2 := congrArg (fun ψ => ModuleCat.Hom.hom ψ) h1
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
  exact congrArg (fun L => L u) h2

/-- `relLocClass_restrict` at the level of homology morphisms. -/
theorem relLocClass_restrict_hom
    (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9)
    {K K' : Set (Double 8 M)} (h : K ⊆ K') :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double 8 M)) (K'ᶜ))) 9)
        (HomologicalComplex.homologyMap
          (Work.Cohomology.relCokerMap (TopCat.of (Double 8 M)) (K'ᶜ) (Kᶜ)
            (Set.compl_subset_compl.mpr h)) 9)
      = HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double 8 M)) (Kᶜ))) 9 := by
  rw [show (Set.compl_subset_compl.mpr h) = (fun x hx hxK => hx (h hxK)) from rfl,
    ← HomologicalComplex.homologyMap_comp, Work.Cohomology.relCokerMap_comp_π]

/-- `relLocClass_restrict` at the level of elements. -/
theorem relLocClass_restrict_apply
    (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9)
    {K K' : Set (Double 8 M)} (h : K ⊆ K') :
    RelHmap (TopCat.of (Double 8 M)) 9 h
        (Work.Cohomology.relLocClass (TopCat.of (Double 8 M)) 9 c K')
      = Work.Cohomology.relLocClass (TopCat.of (Double 8 M)) 9 c K := by
  rw [RelHmap, Work.Cohomology.relLocClass, Work.Cohomology.relLocClass]
  have h1 := relLocClass_restrict_hom (M := M) c h
  have h2 := congrArg (fun ψ => ModuleCat.Hom.hom ψ) h1
  rw [ModuleCat.hom_comp] at h2
  exact congrArg (fun L => L c) h2

end Dside

/-- `bdryIncl_comp` at the level of homology morphisms. -/
theorem bdryIncl_comp_hom {K K' : Set M} (hK : K ⊆ (bdry9 M)ᶜ) (hK' : K' ⊆ (bdry9 M)ᶜ)
    (hK'K : K' ⊆ K) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (bdryIncl (M := M) K hK) 9)
        (HomologicalComplex.homologyMap
          (Work.Cohomology.relCokerMap (TopCat.of M) (Kᶜ : Set M) (K'ᶜ : Set M)
            (Set.compl_subset_compl.mpr hK'K)) 9)
      = (HomologicalComplex.homologyMap (bdryIncl (M := M) K' hK') 9) := by
  rw [show (Set.compl_subset_compl.mpr hK'K) = (fun x hxK hxK' => hxK (hK'K hxK')) from rfl,
    ← HomologicalComplex.homologyMap_comp, bdryIncl_comp (M := M) hK hK' hK'K]

/-- `bdryIncl_comp` at the level of elements. -/
theorem bdryIncl_comp_apply {K K' : Set M} (hK : K ⊆ (bdry9 M)ᶜ) (hK' : K' ⊆ (bdry9 M)ᶜ)
    (hK'K : K' ⊆ K) (u : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9) :
    RelHmap (TopCat.of M) 9 hK'K
        ((HomologicalComplex.homologyMap (bdryIncl (M := M) K hK) 9) u)
      = (HomologicalComplex.homologyMap (bdryIncl (M := M) K' hK') 9) u := by
  rw [RelHmap]
  have h1 := bdryIncl_comp_hom (M := M) hK hK' hK'K
  have h2 := congrArg (fun ψ => ModuleCat.Hom.hom ψ) h1
  rw [ModuleCat.hom_comp] at h2
  exact congrArg (fun L => L u) h2

/-- The local class of a global class at a point, in the `relLocClass` form. -/
theorem localClassAt_eq_relLocClass (c : (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology 9)
    (z : M) :
    Work.ThomBordism.localClassAt (TopCat.of M) 9 c z
      = Work.Cohomology.relLocClass (TopCat.of M) 9 c ({z} : Set M) := by
  rw [Work.ThomBordism.localClassAt, Work.Cohomology.relLocClass]
  congr 2

/-! ## The key computation -/


/-- **The dictionary between `localClassAt` and `relLocClass`, for an arbitrary space.**  Both are the
image of `c` in `H_9(X, X∖{x})`; the two spellings of the excluded set (`{y | y ≠ x}` and `{x}ᶜ`)
are definitionally equal.  The `X`-general form is what makes the rewriting in
`relLocClass_coordBalls` cheap: the version specialised to the manifold `M` would force the
elaborator to compare `Double 8 M` with `M`. -/
theorem localClassAt_eq_relLocClass_gen (X : TopCat.{0})
    (c : (Work.Cohomology.singularChains ℤ X).homology 9) (x : X) :
    Work.ThomBordism.localClassAt X 9 c x
      = Work.Cohomology.relLocClass X 9 c ({x} : Set X) := by
  rw [Work.ThomBordism.localClassAt, Work.Cohomology.relLocClass]
  congr 2

/-- **(★)** The local class of the fundamental class `cD` of the double at a finite union of
coordinate balls contained in the interior of the first half equals the image of the relative
fundamental class `w` of `(M, ∂M)` under the first-copy inclusion.

The proof is Hatcher 3.27(a) (`Work.ThomBordism.unionZero`) applied to the difference of the two
classes: a class of `H_9(D, D∖⋃B)` which dies at one point `x b ∈ B b` of every ball is zero. -/
theorem relLocClass_coordBalls
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
    [T2Space (Double 8 M)] [CompactSpace (Double 8 M)]
    [ChartedSpace (EuclideanSpace ℝ (Fin 9)) (Double 8 M)]
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9)
    (hM : ∀ (y : M) (hy : y ∉ bdry9 M),
      Work.ThomBordism.localClassAt (TopCat.of (Double 8 M)) 9 cD (doubleιM y)
        = (HomologicalComplex.homologyMap (DoubleFC.pairMapιM 8 M y) 9)
            (RelDoubleClass.locW (n := 8) (M := M) w y hy))
    {β : Type} (s : Finset β) (B : β → Set (Double 8 M)) (y : β → M)
    (hball : ∀ b ∈ s, IsCoordBall 9 (TopCat.of (Double 8 M)) (B b))
    (hx : ∀ b ∈ s, doubleιM (y b) ∈ B b)
    (hsub : (⋃ b ∈ s, B b) ⊆ DoubleFC.intImg 8 M) :
    Work.Cohomology.relLocClass (TopCat.of (Double 8 M)) 9 cD (⋃ b ∈ s, B b)
      = (HomologicalComplex.homologyMap
          (suppMap (M := M) (suppOf (M := M) (⋃ b ∈ s, B b)) (⋃ b ∈ s, B b)
            (by intro z hz hzL; exact hz hzL)) 9)
          ((HomologicalComplex.homologyMap
            (bdryIncl (M := M) (suppOf (M := M) (⋃ b ∈ s, B b))
              (by
                intro z hz
                have h1 : z ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hsub hz
                rw [suppOf_intImg] at h1
                exact h1)) 9) w) := by
  classical
  rw [← sub_eq_zero]
  refine Work.ThomBordism.unionZero 9 (by norm_num) (TopCat.of (Double 8 M)) s B
    (fun b => doubleιM (y b)) hball hx _ ?_
  intro b hb
  rw [map_sub, sub_eq_zero]
  -- the point `ιM (y b)` is interior, because it lies in the union inside `intImg`
  have hyint : y b ∉ bdry9 M := by
    have h1 : doubleιM (y b) ∈ DoubleFC.intImg 8 M :=
      hsub (Set.mem_iUnion₂.mpr ⟨b, hb, hx b hb⟩)
    have h2 : y b ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := h1
    rw [suppOf_intImg] at h2
    exact h2
  -- the inclusion `{ιM (y b)} ⊆ ⋃B`
  have hball_pt : ({doubleιM (y b)} : Set (Double 8 M)) ⊆ (⋃ b ∈ s, B b) :=
    Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨b, hb, hx b hb⟩)
  -- the inclusion `{y b} ⊆ suppOf ⋃B`
  have hy_pt : ({y b} : Set M) ⊆ suppOf (M := M) (⋃ b ∈ s, B b) := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Set.mem_iUnion₂.mpr ⟨b, hb, hx b hb⟩
  -- the left hand side restricts to the local class of `cD` at `ιM (y b)`
  rw [relLocClass_restrict_apply (c := cD) (K := ({doubleιM (y b)} : Set (Double 8 M)))
      (K' := (⋃ b ∈ s, B b)) hball_pt]
  rw [← localClassAt_eq_relLocClass_gen (X := TopCat.of (Double 8 M)) cD (doubleιM (y b))]
  rw [hM (y b) hyint]
  -- the right hand side is `suppMap` of the local class of `w` at `y b`
  rw [suppMap_natural_apply (M := M) (K := ({y b} : Set M))
      (K' := suppOf (M := M) (⋃ b ∈ s, B b))
      (L := ({doubleιM (y b)} : Set (Double 8 M))) (L' := (⋃ b ∈ s, B b))
      hy_pt hball_pt
      (by intro z hz hzL
          exact hz (Set.mem_singleton_iff.mpr
            (doubleιM_injective (Set.mem_singleton_iff.mp hzL))))
      (by intro z hz hzL; exact hz hzL) _]
  rw [bdryIncl_comp_apply (M := M) (K := suppOf (M := M) (⋃ b ∈ s, B b))
      (K' := ({y b} : Set M))
      (hK := (by
        intro z hz
        have h1 : z ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hsub hz
        rw [suppOf_intImg] at h1
        exact h1))
      (hK' := (by intro z hz hyz; exact hyint (Set.mem_singleton_iff.mp hz ▸ hyz)))
      (hK'K := hy_pt)]
  rw [suppMap_singleton (M := M) (y b),
    bdryIncl_singleton_eq_locW (M := M) (w := w) (y b) hyint]

end

end Work.ThomBordism.RelDuality
