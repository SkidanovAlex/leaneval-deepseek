import Mathlib
import Submission.Work.ThomBordism.localisation_constr_of_eqOn
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The localisation construction depends only on the germ (general T1 space)

This is the general-space form of `Work.ThomBordism.localisation_constr_of_eqOn`.  Nothing in the
latter proof uses the sphere: for a T1 space `X`, a point `y : X` and two self-maps `φ₀, φ₁` which
agree on an open neighbourhood `N` of `y` (and which are injective on the fibres over `φ₀ y = φ₁ y`,
so that they restrict to the complements of the two points), the induced maps

`H_n(X, X∖{y}) → H_n(X, X∖{φ₀ y})`

agree.  The proof uses only: `{y}ᶜ` open (T1), the cover `N ∪ {y}ᶜ = X`, the excision
quasi-isomorphism `H_n(N, N∖{y}) → H_n(X, X∖{y})`, and functoriality of `relChainsMapOf`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

/-- `relChainsMapOf` only depends on the two maps of the pair, not on the proof of the
compatibility of the pair map. -/
private theorem relChainsMapOf_congr_map' {X Y : TopCat} {A : Set X} {B : Set Y} {f f' : X ⟶ Y}
    {g g' : TopCat.of A ⟶ TopCat.of B} (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  cases hf
  cases hg
  rw [Subsingleton.elim w w']

theorem relLocClass_germ_eq {n : ℕ} {X : TopCat} [T1Space X]
    {φ₀ φ₁ : C(X, X)} {N : Set X} (hN : IsOpen N) {y : X} (hy : y ∈ N)
    (h : ∀ z ∈ N, φ₀ z = φ₁ z) (h0 : φ₀ y = φ₁ y)
    (hfib₀ : ∀ z, φ₀ z = φ₀ y → z = y) (hfib₁ : ∀ z, φ₁ z = φ₁ y → z = y)
    (c : (Work.Cohomology.singularChains ℤ X).homology n) :
    (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X X ({y}ᶜ : Set X) ({φ₀ y}ᶜ : Set X) (TopCat.ofHom φ₀)
          (TopCat.ofHom ⟨fun a => ⟨φ₀ a.1, fun hh => a.2 (hfib₀ a.1 hh)⟩,
            Continuous.subtype_mk (φ₀.continuous.comp continuous_subtype_val) _⟩)
          (by ext a; rfl)) n).hom
        (Work.Cohomology.relLocClass X n c ({y} : Set X))
      = (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X X ({y}ᶜ : Set X) ({φ₀ y}ᶜ : Set X) (TopCat.ofHom φ₁)
          (TopCat.ofHom ⟨fun a => ⟨φ₁ a.1, fun hh => a.2 (hfib₁ a.1 (hh.trans h0))⟩,
            Continuous.subtype_mk (φ₁.continuous.comp continuous_subtype_val) _⟩)
          (by ext a; rfl)) n).hom
        (Work.Cohomology.relLocClass X n c ({y} : Set X)) := by
  -- the excluded point is closed (T1)
  have hSc : IsOpen ({y}ᶜ : Set X) := isClosed_singleton.isOpen_compl
  -- `N` and the complement of `y` cover the space
  have hcov : N ∪ ({y}ᶜ : Set X) = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hz : z = y
    · exact Or.inl (by rwa [hz])
    · exact Or.inr hz
  -- excision: `H_n(N, N∖{y}) → H_n(X, X∖{y})` is an isomorphism
  haveI hJ : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap X N ({y}ᶜ : Set X)) n) :=
    Work.Cohomology.excision_relChainsMap_isIso X N ({y}ᶜ : Set X) hN hSc hcov n
  -- the two restrictions of `φ₀`, `φ₁` to the complement of `y`
  set G₀ : TopCat.of ({y}ᶜ : Set X) ⟶ TopCat.of ({φ₀ y}ᶜ : Set X) :=
    TopCat.ofHom ⟨fun a => ⟨φ₀ a.1, fun hh => a.2 (hfib₀ a.1 hh)⟩,
      Continuous.subtype_mk (φ₀.continuous.comp continuous_subtype_val) _⟩ with hG₀
  set G₁ : TopCat.of ({y}ᶜ : Set X) ⟶ TopCat.of ({φ₀ y}ᶜ : Set X) :=
    TopCat.ofHom ⟨fun a => ⟨φ₁ a.1, fun hh => a.2 (hfib₁ a.1 (hh.trans h0))⟩,
      Continuous.subtype_mk (φ₁.continuous.comp continuous_subtype_val) _⟩ with hG₁
  -- the two maps on relative chain complexes of the statement
  set T₀ := Work.Cohomology.relChainsMapOf X X ({y}ᶜ : Set X) ({φ₀ y}ᶜ : Set X)
      (TopCat.ofHom φ₀) G₀ (by ext a; rfl) with hT₀
  set T₁ := Work.Cohomology.relChainsMapOf X X ({y}ᶜ : Set X) ({φ₀ y}ᶜ : Set X)
      (TopCat.ofHom φ₁) G₁ (by ext a; rfl) with hT₁
  -- the excision inclusion composed with either map is the chain map of the restricted pair map
  have hcomp₀ : Work.Cohomology.relChainsMap X N ({y}ᶜ : Set X) ≫ T₀
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥N) X
          {z : ↥N | (z : X) ∈ ({y}ᶜ : Set X)} ({φ₀ y}ᶜ : Set X)
          (Work.Cohomology.subtypeIncl X N ≫ TopCat.ofHom φ₀)
          (Work.Cohomology.inclInterA X N ({y}ᶜ : Set X) ≫ G₀) (by ext a; rfl) :=
    Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _
  have hcomp₁ : Work.Cohomology.relChainsMap X N ({y}ᶜ : Set X) ≫ T₁
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥N) X
          {z : ↥N | (z : X) ∈ ({y}ᶜ : Set X)} ({φ₀ y}ᶜ : Set X)
          (Work.Cohomology.subtypeIncl X N ≫ TopCat.ofHom φ₁)
          (Work.Cohomology.inclInterA X N ({y}ᶜ : Set X) ≫ G₁) (by ext a; rfl) :=
    Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _
  -- the two restricted pair maps agree, because `φ₀` and `φ₁` agree on `N`
  have hf_eq : Work.Cohomology.subtypeIncl X N ≫ TopCat.ofHom φ₀
      = Work.Cohomology.subtypeIncl X N ≫ TopCat.ofHom φ₁ := by
    apply TopCat.ext
    intro z
    exact h z z.2
  have hg_eq : (Work.Cohomology.inclInterA X N ({y}ᶜ : Set X)) ≫ G₀
      = (Work.Cohomology.inclInterA X N ({y}ᶜ : Set X)) ≫ G₁ := by
    apply TopCat.ext
    intro z
    exact Subtype.ext (h z.1.1 z.1.2)
  have hcongr : Work.Cohomology.relChainsMapOf (TopCat.of ↥N) X
        {z : ↥N | (z : X) ∈ ({y}ᶜ : Set X)} ({φ₀ y}ᶜ : Set X)
        (Work.Cohomology.subtypeIncl X N ≫ TopCat.ofHom φ₀)
        (Work.Cohomology.inclInterA X N ({y}ᶜ : Set X) ≫ G₀) (by ext a; rfl)
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥N) X
        {z : ↥N | (z : X) ∈ ({y}ᶜ : Set X)} ({φ₀ y}ᶜ : Set X)
        (Work.Cohomology.subtypeIncl X N ≫ TopCat.ofHom φ₁)
        (Work.Cohomology.inclInterA X N ({y}ᶜ : Set X) ≫ G₁) (by ext a; rfl) :=
    relChainsMapOf_congr_map' hf_eq hg_eq _ _
  -- hence the excision inclusion followed by the two maps agree
  have hmap : HomologicalComplex.homologyMap T₀ n = HomologicalComplex.homologyMap T₁ n := by
    apply (cancel_epi (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap X N ({y}ᶜ : Set X)) n)).1
    rw [← HomologicalComplex.homologyMap_comp, hcomp₀, ← HomologicalComplex.homologyMap_comp,
      hcomp₁]
    exact congrArg (fun K => HomologicalComplex.homologyMap K n) hcongr
  rw [hmap]

end

end Work.ThomBordism
