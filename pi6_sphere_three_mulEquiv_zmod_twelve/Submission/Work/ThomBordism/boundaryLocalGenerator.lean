import Mathlib
import Submission.Work.ThomBordism.localClassAt
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.existsBoundaryBordism
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.ThomBordism.doubleFC.relFactor
import Submission.Work.Orient.Boundary.localHomology_corner

/-!
# `\partial w` is a fundamental class of `\partial W`

The boundary class `Work.Cohomology.hPairδ W W.\partial 8 W.w` of a null-bordism family
`W : NullBordismFamily ι F` is a **local generator** at every point of the boundary: this is the
statement `Work.ThomBordism.boundaryLocalGenerator`, the input needed by
`Work.ThomBordism.doubleFundamentalClass` and by `Work.ThomBordism.goodUniv_of_localGen`.

The proof is the standard one.  Writing `c = \sum_i (incl_i)_* (F i).c` (`W.hw`), the local class at
a point `p` is linear in `c`; all the summands except the one containing `p` have local class `0`
(a class supported away from `p` has vanishing local class, `localClassAt_homologyMap_eq_zero_of_ne`)
and the summand containing `p` is a local generator because the inclusion of the corresponding
boundary piece is an *open embedding*, so that it induces an isomorphism on local homology
(`isIso_openEmbPairMap_of_isOpenEmbedding`), and isomorphisms send generators to generators.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

theorem localClassAt_sum {X : TopCat.{0}} (n : ℕ) (x : X) {ι : Type} [Fintype ι]
    (f : ι → ↑(HomologicalComplex.homology (Cohomology.chainC ℤ (TopCat.toSSet.obj X)) n)) :
    localClassAt X n (∑ i, f i) x = ∑ i, localClassAt X n (f i) x := by
  unfold localClassAt
  exact map_sum _ _ _

theorem localClassAt_homologyMap_eq_zero_of_ne {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y)
    (hy : ∀ z : X, f z ≠ y) (n : ℕ)
    (c : ↑(HomologicalComplex.homology (Cohomology.chainC ℤ (TopCat.toSSet.obj X)) n)) :
    localClassAt Y n (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ X Y f) n c) y = 0 := by
  let f' : X ⟶ TopCat.of ({y}ᶜ : Set Y) :=
    TopCat.ofHom ⟨fun z => ⟨f z, hy z⟩, Continuous.subtype_mk f.hom.continuous _⟩
  have hfac : f = f' ≫ Cohomology.subtypeIncl Y ({y}ᶜ : Set Y) := by ext z; rfl
  have hchainzero : Cohomology.chainMap ℤ X Y f ≫
      CategoryTheory.Limits.cokernel.π (Cohomology.inclChains Y ({y}ᶜ : Set Y)) = 0 := by
    rw [hfac, Cohomology.chainMap_comp', Category.assoc,
      show Cohomology.inclChains Y ({y}ᶜ : Set Y) ≫
        cokernel.π (Cohomology.inclChains Y ({y}ᶜ : Set Y)) = 0 from cokernel.condition _]
    simp
  have hzero : (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ X Y f) n) ≫
      (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Cohomology.inclChains Y ({y}ᶜ : Set Y))) n) = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, hchainzero]
    simp
  unfold localClassAt
  exact congrArg (fun φ => (ConcreteCategory.hom φ) c) hzero

theorem localClassAt_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y)
    (g : TopCat.of ({z : X | z ≠ x}) ⟶ TopCat.of ({z : Y | z ≠ y}))
    (w : Cohomology.subtypeIncl X ({z : X | z ≠ x}) ≫ f
      = g ≫ Cohomology.subtypeIncl Y ({z : Y | z ≠ y}))
    (n : ℕ) (c : ↑(HomologicalComplex.homology (Cohomology.chainC ℤ (TopCat.toSSet.obj X)) n)) :
    localClassAt Y n (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ X Y f) n c) y
      = (ConcreteCategory.hom (HomologicalComplex.homologyMap
          (Cohomology.relChainsMapOf X Y ({z : X | z ≠ x}) ({z : Y | z ≠ y}) f g w) n))
          (localClassAt X n c x) := by
  unfold localClassAt
  have h1 : (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ X Y f) n) ≫
      (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Cohomology.inclChains Y ({z : Y | z ≠ y}))) n)
      = (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Cohomology.inclChains X ({z : X | z ≠ x}))) n) ≫
        (HomologicalComplex.homologyMap
          (Cohomology.relChainsMapOf X Y ({z : X | z ≠ x}) ({z : Y | z ≠ y}) f g w) n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      Cohomology.capRel_cokernel_π_relChainsMapOf]
  exact congrArg (fun ρ => (ConcreteCategory.hom ρ) c) h1

private theorem span_singleton_of_isIso {A B : ModuleCat ℤ} (φ : A ⟶ B) [IsIso φ] (a : A)
    (h : Submodule.span ℤ {a} = ⊤) :
    Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} = ⊤ := by
  have hmap : Submodule.map (ModuleCat.Hom.hom φ) (Submodule.span ℤ {a}) =
      Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} := by
    rw [Submodule.map_span]
    simp
  have htop : Submodule.map (ModuleCat.Hom.hom φ) (⊤ : Submodule ℤ A) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr]
    exact (ModuleCat.epi_iff_surjective _).mp (IsIso.epi_of_iso φ)
  rw [← hmap, h, htop]

/-! ## The pair map and its isomorphism property -/

noncomputable def openEmbPairMapG {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (y : Y)
    (hinj : Function.Injective f) (hxy : f x = y) :
    TopCat.of {z : X | z ≠ x} ⟶ TopCat.of {z : Y | z ≠ y} :=
  TopCat.ofHom ⟨fun z => ⟨f z.1, fun h => z.2 (hinj (h.trans hxy.symm))⟩,
    Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩

theorem openEmbPairMapW {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (y : Y)
    (hinj : Function.Injective f) (hxy : f x = y) :
    Cohomology.subtypeIncl X {z : X | z ≠ x} ≫ f
      = openEmbPairMapG f x y hinj hxy ≫ Cohomology.subtypeIncl Y {z : Y | z ≠ y} := by
  ext z; rfl

noncomputable def openEmbPairMap {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (y : Y)
    (hinj : Function.Injective f) (hxy : f x = y) :
    Cohomology.relChains X {z : X | z ≠ x} ⟶ Cohomology.relChains Y {z : Y | z ≠ y} :=
  Cohomology.relChainsMapOf X Y {z : X | z ≠ x} {z : Y | z ≠ y} f (openEmbPairMapG f x y hinj hxy)
    (openEmbPairMapW f x y hinj hxy)

theorem isIso_openEmbPairMap_of_isOpenEmbedding {X Y : TopCat.{0}} [T1Space ↥X] [T1Space ↥Y]
    (f : X ⟶ Y) (x : X) (y : Y) (hinj : Function.Injective f) (hxy : f x = y)
    (hemb : Topology.IsOpenEmbedding (fun z : ↥X => f z)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (openEmbPairMap f x y hinj hxy) n) := by
  have hU : IsOpen (Set.univ : Set ↥X) := isOpen_univ
  have hV : IsOpen (Set.range (fun z : ↥X => f z)) := hemb.isOpen_range
  have hA : IsOpen ({z : ↥X | z ≠ x}) := (isClosed_singleton (x := x)).isOpen_compl
  have hB : IsOpen ({z : ↥Y | z ≠ y}) := (isClosed_singleton (x := y)).isOpen_compl
  have hcovU : (Set.univ : Set ↥X) ∪ {z : ↥X | z ≠ x} = Set.univ := Set.univ_union _
  have hcovV : Set.range (fun z : ↥X => f z) ∪ {z : ↥Y | z ≠ y} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    by_cases h : q = y
    · subst h
      exact Or.inl ⟨x, hxy⟩
    · exact Or.inr h
  let hh : ↥(Set.univ : Set ↥X) ≃ₜ ↥(Set.range (fun z : ↥X => f z)) :=
    (Homeomorph.Set.univ ↥X).trans hemb.toIsEmbedding.toHomeomorph
  have hh_coe : ∀ z : ↥(Set.univ : Set ↥X),
      ((hh z : ↥(Set.range (fun z : ↥X => f z))) : ↥Y) = f z.1 := by
    intro z
    rw [Homeomorph.trans_apply, Topology.IsEmbedding.toHomeomorph_apply_coe,
      Homeomorph.Set.univ_apply]
  have hhA : ∀ z : ↥(Set.univ : Set ↥X),
      z ∈ {z : ↥(Set.univ : Set ↥X) | (z : ↥X) ∈ ({z : ↥X | z ≠ x})} ↔
        hh z ∈ {q : ↥(Set.range (fun z : ↥X => f z)) | (q : ↥Y) ∈ ({z : ↥Y | z ≠ y})} := by
    intro z
    simp only [Set.mem_setOf_eq]
    rw [hh_coe z]
    constructor
    · intro hz h
      exact hz (hinj (h.trans hxy.symm))
    · intro hz hz'
      exact hz (by rw [hz', hxy])
  let h' := Orient.Boundary.homeomorphRestrict hh
    {z : ↥(Set.univ : Set ↥X) | (z : ↥X) ∈ ({z : ↥X | z ≠ x})}
    {q : ↥(Set.range (fun z : ↥X => f z)) | (q : ↥Y) ∈ ({z : ↥Y | z ≠ y})} hhA
  let hTop : TopCat.of ↥(Set.univ : Set ↥X) ⟶ TopCat.of ↥(Set.range (fun z : ↥X => f z)) :=
    TopCat.ofHom hh.toHomotopyEquiv.toFun
  let h'Top : TopCat.of ↥{z : ↥(Set.univ : Set ↥X) | (z : ↥X) ∈ ({z : ↥X | z ≠ x})}
      ⟶ TopCat.of ↥{q : ↥(Set.range (fun z : ↥X => f z)) | (q : ↥Y) ∈ ({z : ↥Y | z ≠ y})} :=
    TopCat.ofHom h'.toHomotopyEquiv.toFun
  have hsub : Cohomology.subtypeIncl X (Set.univ : Set ↥X) ≫ f
      = hTop ≫ Cohomology.subtypeIncl Y (Set.range (fun z : ↥X => f z)) := by
    apply TopCat.ext
    intro z
    exact hh_coe z
  have hsub' : Cohomology.inclInterA X (Set.univ : Set ↥X) ({z : ↥X | z ≠ x})
        ≫ openEmbPairMapG f x y hinj hxy
      = h'Top ≫ Cohomology.inclInterA Y (Set.range (fun z : ↥X => f z)) ({z : ↥Y | z ≠ y}) := by
    apply TopCat.ext
    intro z
    exact Subtype.ext (hh_coe z.1)
  have hsub'' : Cohomology.subtypeIncl (TopCat.of (Set.univ : Set ↥X))
        {z : ↥(Set.univ : Set ↥X) | (z : ↥X) ∈ ({z : ↥X | z ≠ x})} ≫ hTop
      = h'Top ≫ Cohomology.subtypeIncl (TopCat.of (Set.range (fun z : ↥X => f z)))
        {q : ↥(Set.range (fun z : ↥X => f z)) | (q : ↥Y) ∈ ({z : ↥Y | z ≠ y})} := by
    apply TopCat.ext
    intro z
    exact Subtype.ext rfl
  have hk : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Cohomology.chainMap ℤ (TopCat.of (Set.univ : Set ↥X))
        (TopCat.of (Set.range (fun z : ↥X => f z))) hTop) k) := fun k =>
    Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of ↥(Set.univ : Set ↥X)) (Y := TopCat.of ↥(Set.range (fun z : ↥X => f z)))
      hh.toHomotopyEquiv k
  have hk' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Cohomology.chainMap ℤ
        (TopCat.of ↥{z : ↥(Set.univ : Set ↥X) | (z : ↥X) ∈ ({z : ↥X | z ≠ x})})
        (TopCat.of ↥{q : ↥(Set.range (fun z : ↥X => f z)) | (q : ↥Y) ∈ ({z : ↥Y | z ≠ y})})
        h'Top) k) := fun k =>
    Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of ↥{z : ↥(Set.univ : Set ↥X) | (z : ↥X) ∈ ({z : ↥X | z ≠ x})})
      (Y := TopCat.of ↥{q : ↥(Set.range (fun z : ↥X => f z)) | (q : ↥Y) ∈ ({z : ↥Y | z ≠ y})})
      h'.toHomotopyEquiv k
  have key : IsIso (HomologicalComplex.homologyMap (Cohomology.relChainsMapOf X Y
      {z : ↥X | z ≠ x} {z : ↥Y | z ≠ y} f (openEmbPairMapG f x y hinj hxy) (openEmbPairMapW f x y hinj hxy)) n) :=
    doubleFC.isIso_homologyMap_relChainsMapOf_of_factorization
      (X := X) (Y := Y) (A := {z : ↥X | z ≠ x}) (B := {z : ↥Y | z ≠ y})
      f (openEmbPairMapG f x y hinj hxy) (openEmbPairMapW f x y hinj hxy)
      (Set.univ : Set ↥X) (Set.range (fun z : ↥X => f z)) hU hV hA hB hcovU hcovV
      hTop hsub h'Top hsub' hsub'' n hk hk'
  exact key

end

end Work.ThomBordism

namespace Work.ThomBordism

noncomputable section

/-- **The boundary class is a fundamental class of the boundary.**  For a null-bordism family
`W : NullBordismFamily ι F`, the connecting class `\partial w \in H_8(\partial W;\mathbb{Z})`
generates the local homology `H_8(\partial W, \partial W \setminus \{p\})` at every point `p` of the
boundary. -/
theorem boundaryLocalGenerator {ι : Type} [Fintype ι] {F : ι → Work.ThomBordism.Man8}
    (W : Work.ThomBordism.NullBordismFamily ι F) :
    Work.ThomBordism.IsLocalGenerator
      (TopCat.of (Work.ThomBordism.bdrySet W.W)) 8
      (Work.Cohomology.hPairδ (TopCat.of W.W) (Work.ThomBordism.bdrySet W.W) 8 W.w) := by
  intro p
  -- v4.35: the parser now reads this multi-line `{a}` as extended-binder notation; spell the singleton out
  show Submodule.span ℤ (singleton (localClassAt (TopCat.of (bdrySet W.W)) 8
      (Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w) p)) = ⊤
  generalize hq : W.bdry p = q
  obtain ⟨i₀, y₀⟩ := q
  let push : (i : ι) → (F i).X ⟶ TopCat.of (bdrySet W.W) :=
    fun i => TopCat.ofHom ⟨fun z => W.bdry.symm ⟨i, z⟩,
      W.bdry.continuous_invFun.comp continuous_sigmaMk⟩
  have hfy : push i₀ y₀ = p := by
    show W.bdry.symm ⟨i₀, y₀⟩ = p
    rw [← hq, W.bdry.symm_apply_apply]
  have hsum : localClassAt (TopCat.of (bdrySet W.W)) 8
        (Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w) p
      = ∑ i : ι, localClassAt (TopCat.of (bdrySet W.W)) 8
          (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ (F i).X
            (TopCat.of (bdrySet W.W)) (push i)) 8 (F i).c) p := by
    rw [W.hw]
    exact localClassAt_sum (X := TopCat.of (bdrySet W.W)) 8 p _
  have hother : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i₀ →
      localClassAt (TopCat.of (bdrySet W.W)) 8
        (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ (F j).X
          (TopCat.of (bdrySet W.W)) (push j)) 8 (F j).c) p = 0 := by
    intro j _ hj
    refine localClassAt_homologyMap_eq_zero_of_ne (push j) p ?_ 8 (F j).c
    intro z hz
    have h3 : (⟨j, z⟩ : Σ i, (F i).pt) = W.bdry p := by
      refine W.bdry.symm.injective ?_
      show W.bdry.symm (⟨j, z⟩ : Σ i, (F i).pt) = W.bdry.symm (W.bdry p)
      rw [W.bdry.symm_apply_apply]
      exact hz
    have h4 : (⟨j, z⟩ : Σ i, (F i).pt) = ⟨i₀, y₀⟩ := h3.trans hq
    exact hj ((Sigma.mk.injEq _ _ _ _).mp h4).1
  have hinj : Function.Injective (push i₀) := by
    intro a b hab
    have h1 : (⟨i₀, a⟩ : Σ i, (F i).pt) = ⟨i₀, b⟩ := W.bdry.symm.injective hab
    simpa using h1
  have hemb : Topology.IsOpenEmbedding (fun z : (F i₀).pt => push i₀ z) :=
    (W.bdry.symm.isOpenEmbedding).comp (Topology.IsOpenEmbedding.sigmaMk)
  have hgen : Submodule.span ℤ (singleton (localClassAt (TopCat.of (bdrySet W.W)) 8
        (HomologicalComplex.homologyMap (Cohomology.chainMap ℤ (F i₀).X
          (TopCat.of (bdrySet W.W)) (push i₀)) 8 (F i₀).c) p)) = ⊤ := by
    have hfund : Submodule.span ℤ (singleton (localClassAt (F i₀).X 8 (F i₀).c y₀)) = ⊤ :=
      (F i₀).c_fund y₀
    haveI : IsIso (HomologicalComplex.homologyMap (openEmbPairMap (push i₀) y₀ p hinj hfy) 8) :=
      isIso_openEmbPairMap_of_isOpenEmbedding (f := push i₀) (x := y₀) (y := p) hinj hfy hemb 8
    rw [localClassAt_naturality (push i₀) y₀ p hfy (openEmbPairMapG (push i₀) y₀ p hinj hfy)
      (openEmbPairMapW (push i₀) y₀ p hinj hfy) 8 (F i₀).c]
    exact span_singleton_of_isIso
      (HomologicalComplex.homologyMap (openEmbPairMap (push i₀) y₀ p hinj hfy) 8)
      (localClassAt (F i₀).X 8 (F i₀).c y₀) hfund
  rw [hsum, Finset.sum_eq_single i₀ hother (fun h => absurd (Finset.mem_univ i₀) h)]
  exact hgen

end

end Work.ThomBordism
