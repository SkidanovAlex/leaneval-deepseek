import Mathlib
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The localisation construction depends only on the germ

For a manifold `M`, a point `y : M` and a self-map `φ : M → M` which is *injective on the fibre
over* `φ y` (so that `φ` restricts to the complements of the two points), the induced map

`H_n(M, M∖{y}) → H_n(M, M∖{φ y})`

(the "localisation construction") depends on `φ` only through its germ at `y`: the local homology of
the pair `(M, M∖{y})` is computed by the *excision isomorphism* from an open neighbourhood
`H_n(N, N∖{y}) ≅ H_n(M, M∖{y})`, and on that neighbourhood the two maps agree.

The statement below is the case `M = Sⁿ`, but neither the geometry of the sphere nor the
injectivity hypotheses are used for anything but the *formation* of the pair maps: the proof only
uses that `N` is an open neighbourhood of `y` on which the two maps agree, together with the
excision quasi-isomorphism of `(N, N∖{y}) ⊆ (Sⁿ, Sⁿ∖{y})` and the functoriality of
`Work.Cohomology.relChainsMapOf` in the pair of maps.
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
private theorem relChainsMapOf_congr_map {X Y : TopCat} {A : Set X} {B : Set Y} {f f' : X ⟶ Y}
    {g g' : TopCat.of A ⟶ TopCat.of B} (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  cases hf
  cases hg
  rw [Subsingleton.elim w w']

theorem localisation_constr_of_eqOn {n : ℕ}
    {φ₀ φ₁ : C(Work.Stems.sphere n, Work.Stems.sphere n)}
    {N : Set (Work.Stems.sphere n)} (hN : IsOpen N) {y : Work.Stems.sphere n} (hy : y ∈ N)
    (h : ∀ z ∈ N, φ₀ z = φ₁ z) (h0 : φ₀ y = φ₁ y)
    (hfib₀ : ∀ z, φ₀ z = φ₀ y → z = y) (hfib₁ : ∀ z, φ₁ z = φ₁ y → z = y)
    (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))).homology n) :
    (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of (Work.Stems.sphere n))
          (TopCat.of (Work.Stems.sphere n))
          ({y}ᶜ : Set (Work.Stems.sphere n)) ({φ₀ y}ᶜ : Set (Work.Stems.sphere n)) (TopCat.ofHom φ₀)
          (TopCat.ofHom ⟨fun a => ⟨φ₀ a.1, fun hh => a.2 (hfib₀ a.1 hh)⟩,
            Continuous.subtype_mk (φ₀.continuous.comp continuous_subtype_val) _⟩)
          (by ext a; rfl)) n).hom
        (Work.Cohomology.relLocClass (TopCat.of (Work.Stems.sphere n)) n c ({y} : Set (Work.Stems.sphere n)))
      = (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of (Work.Stems.sphere n))
          (TopCat.of (Work.Stems.sphere n))
          ({y}ᶜ : Set (Work.Stems.sphere n)) ({φ₀ y}ᶜ : Set (Work.Stems.sphere n)) (TopCat.ofHom φ₁)
          (TopCat.ofHom ⟨fun a => ⟨φ₁ a.1, fun hh => a.2 (hfib₁ a.1 (hh.trans h0))⟩,
            Continuous.subtype_mk (φ₁.continuous.comp continuous_subtype_val) _⟩)
          (by ext a; rfl)) n).hom
        (Work.Cohomology.relLocClass (TopCat.of (Work.Stems.sphere n)) n c ({y} : Set (Work.Stems.sphere n))) := by
  -- the excluded point is closed (the sphere is a metric, hence T1, space)
  have hSc : IsOpen ({y}ᶜ : Set (Work.Stems.sphere n)) := isClosed_singleton.isOpen_compl
  -- `N` and the complement of `y` cover the sphere
  have hcov : N ∪ ({y}ᶜ : Set (Work.Stems.sphere n)) = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hz : z = y
    · exact Or.inl (by rwa [hz])
    · exact Or.inr hz
  -- excision: `H_n(N, N∖{y}) → H_n(Sⁿ, Sⁿ∖{y})` is an isomorphism
  haveI hJ : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (Work.Stems.sphere n)) N
        ({y}ᶜ : Set (Work.Stems.sphere n))) n) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (Work.Stems.sphere n)) N
      ({y}ᶜ : Set (Work.Stems.sphere n)) hN hSc hcov n
  -- the two restrictions of `φ₀`, `φ₁` to the complement of `y`
  set G₀ : TopCat.of ({y}ᶜ : Set (Work.Stems.sphere n)) ⟶
      TopCat.of ({φ₀ y}ᶜ : Set (Work.Stems.sphere n)) :=
    TopCat.ofHom ⟨fun a => ⟨φ₀ a.1, fun hh => a.2 (hfib₀ a.1 hh)⟩,
      Continuous.subtype_mk (φ₀.continuous.comp continuous_subtype_val) _⟩ with hG₀
  set G₁ : TopCat.of ({y}ᶜ : Set (Work.Stems.sphere n)) ⟶
      TopCat.of ({φ₀ y}ᶜ : Set (Work.Stems.sphere n)) :=
    TopCat.ofHom ⟨fun a => ⟨φ₁ a.1, fun hh => a.2 (hfib₁ a.1 (hh.trans h0))⟩,
      Continuous.subtype_mk (φ₁.continuous.comp continuous_subtype_val) _⟩ with hG₁
  -- the two maps on relative chain complexes of the statement
  set T₀ := Work.Cohomology.relChainsMapOf (TopCat.of (Work.Stems.sphere n))
      (TopCat.of (Work.Stems.sphere n)) ({y}ᶜ : Set (Work.Stems.sphere n))
      ({φ₀ y}ᶜ : Set (Work.Stems.sphere n)) (TopCat.ofHom φ₀) G₀ (by ext a; rfl) with hT₀
  set T₁ := Work.Cohomology.relChainsMapOf (TopCat.of (Work.Stems.sphere n))
      (TopCat.of (Work.Stems.sphere n)) ({y}ᶜ : Set (Work.Stems.sphere n))
      ({φ₀ y}ᶜ : Set (Work.Stems.sphere n)) (TopCat.ofHom φ₁) G₁ (by ext a; rfl) with hT₁
  -- the excision inclusion composed with either map is the chain map of the restricted pair map
  have hcomp₀ : Work.Cohomology.relChainsMap (TopCat.of (Work.Stems.sphere n)) N
        ({y}ᶜ : Set (Work.Stems.sphere n)) ≫ T₀
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥N) (TopCat.of (Work.Stems.sphere n))
          {z : ↥N | (z : Work.Stems.sphere n) ∈ ({y}ᶜ : Set (Work.Stems.sphere n))}
          ({φ₀ y}ᶜ : Set (Work.Stems.sphere n))
          (Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere n)) N ≫ TopCat.ofHom φ₀)
          (Work.Cohomology.inclInterA (TopCat.of (Work.Stems.sphere n)) N
            ({y}ᶜ : Set (Work.Stems.sphere n)) ≫ G₀) (by ext a; rfl) :=
    Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _
  have hcomp₁ : Work.Cohomology.relChainsMap (TopCat.of (Work.Stems.sphere n)) N
        ({y}ᶜ : Set (Work.Stems.sphere n)) ≫ T₁
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥N) (TopCat.of (Work.Stems.sphere n))
          {z : ↥N | (z : Work.Stems.sphere n) ∈ ({y}ᶜ : Set (Work.Stems.sphere n))}
          ({φ₀ y}ᶜ : Set (Work.Stems.sphere n))
          (Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere n)) N ≫ TopCat.ofHom φ₁)
          (Work.Cohomology.inclInterA (TopCat.of (Work.Stems.sphere n)) N
            ({y}ᶜ : Set (Work.Stems.sphere n)) ≫ G₁) (by ext a; rfl) :=
    Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _
  -- the two restricted pair maps agree, because `φ₀` and `φ₁` agree on `N`
  have hf_eq : Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere n)) N ≫ TopCat.ofHom φ₀
      = Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere n)) N ≫ TopCat.ofHom φ₁ := by
    apply TopCat.ext
    intro z
    exact h z z.2
  have hg_eq : (Work.Cohomology.inclInterA (TopCat.of (Work.Stems.sphere n)) N
        ({y}ᶜ : Set (Work.Stems.sphere n))) ≫ G₀
      = (Work.Cohomology.inclInterA (TopCat.of (Work.Stems.sphere n)) N
        ({y}ᶜ : Set (Work.Stems.sphere n))) ≫ G₁ := by
    apply TopCat.ext
    intro z
    exact Subtype.ext (h z.1.1 z.1.2)
  have hcongr : Work.Cohomology.relChainsMapOf (TopCat.of ↥N) (TopCat.of (Work.Stems.sphere n))
        {z : ↥N | (z : Work.Stems.sphere n) ∈ ({y}ᶜ : Set (Work.Stems.sphere n))}
        ({φ₀ y}ᶜ : Set (Work.Stems.sphere n))
        (Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere n)) N ≫ TopCat.ofHom φ₀)
        (Work.Cohomology.inclInterA (TopCat.of (Work.Stems.sphere n)) N
          ({y}ᶜ : Set (Work.Stems.sphere n)) ≫ G₀) (by ext a; rfl)
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥N) (TopCat.of (Work.Stems.sphere n))
        {z : ↥N | (z : Work.Stems.sphere n) ∈ ({y}ᶜ : Set (Work.Stems.sphere n))}
        ({φ₀ y}ᶜ : Set (Work.Stems.sphere n))
        (Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere n)) N ≫ TopCat.ofHom φ₁)
        (Work.Cohomology.inclInterA (TopCat.of (Work.Stems.sphere n)) N
          ({y}ᶜ : Set (Work.Stems.sphere n)) ≫ G₁) (by ext a; rfl) :=
    relChainsMapOf_congr_map hf_eq hg_eq _ _
  -- hence the excision inclusion followed by the two maps agree
  have hmap : HomologicalComplex.homologyMap T₀ n = HomologicalComplex.homologyMap T₁ n := by
    apply (cancel_epi (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (Work.Stems.sphere n)) N
        ({y}ᶜ : Set (Work.Stems.sphere n))) n)).1
    rw [← HomologicalComplex.homologyMap_comp, hcomp₀, ← HomologicalComplex.homologyMap_comp,
      hcomp₁]
    exact congrArg (fun K => HomologicalComplex.homologyMap K n) hcongr
  rw [hmap]

end

end Work.ThomBordism

