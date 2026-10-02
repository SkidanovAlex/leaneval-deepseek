import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Fundamental classes are transported by a homeomorphism

If `c ∈ H_n(M; ℤ)` is a fundamental class of `M` (`Work.Orient.IsFundClass M n c`: its local class
at every point generates the local homology `H_n(M, M∖{x})`), and `e : M ≃ₜ M'` is a homeomorphism,
then the image of `c` under the induced map on singular homology is a fundamental class of `M'`.

The mathematical content is small but the formalisation needs the *naturality of the local classes
under a map of pairs*: for a continuous map `f : M → M'` carrying the excluded set `Kᶜ ⊆ M` into
`K'ᶜ ⊆ M'` (with `g` the restriction, `hw` the compatibility), the induced map of relative chain
complexes `relChainsMapOf M M' Kᶜ K'ᶜ f g hw` sends the local class of `c` at `K` to the local
class at `K'` of the image of `c`:

`Work.ThomBordism.Transversality.OrientBridge.relLocClass_map_pair`.

(The formalisation obstacle is that `relLocClass` is phrased with `cokernel (inclChains M Kᶜ)` while
`relChainsMapOf` is phrased with `relChains M Kᶜ`; these are the same object definitionally but not
syntactically, so the intermediate rewrites need `erw` and the transparency option below.)

Applied to `K = {x}`, `K' = {e x}` with `g` the restriction of the homeomorphism, the induced map
on `H_n` is an isomorphism (`relChainsMapOf_homologyMap_isIso`), hence carries a generator to a
generator.  No manifold structure is needed: the statement holds for an arbitrary homeomorphism of
topological spaces.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.Transversality.OrientBridge

/-- **The compatibility of `relChainsMapOf` with the projections to the relative chain complexes**:
the map induced by a map of pairs commutes with the canonical projections onto the cokernels. -/
theorem cokernel_π_relChainsMapOf {X Y : TopCat} {A : Set X} {B : Set Y} {f : X ⟶ Y}
    {g : TopCat.of A ⟶ TopCat.of B}
    {w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B} :
    cokernel.π (Work.Cohomology.inclChains X A) ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B) (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℤ X Y f) _

/-- **Naturality of the local classes under a map of pairs.**

For `f : M ⟶ M'`, `g` a map of the pairs `(M, Kᶜ) → (M', K'ᶜ)` and `c ∈ H_n(M; ℤ)`, the map of
relative chain complexes `relChainsMapOf M M' Kᶜ K'ᶜ f g hw` carries the local class of `c` at `K`
to the local class at `K'` of the image of `c` under `f`. -/
theorem relLocClass_map_pair {M M' : TopCat} {n : ℕ} (f : M ⟶ M') {K : Set M} {K' : Set M'}
    (g : TopCat.of ↥(Kᶜ) ⟶ TopCat.of ↥(K'ᶜ))
    (hw : Work.Cohomology.subtypeIncl M Kᶜ ≫ f = g ≫ Work.Cohomology.subtypeIncl M' K'ᶜ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) :
    (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf M M' Kᶜ K'ᶜ f g hw) n)
        (Work.Cohomology.relLocClass M n c K)
      = Work.Cohomology.relLocClass M' n
          (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ M M' f) n c) K' := by
  simp only [Work.Cohomology.relLocClass]
  erw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, cokernel_π_relChainsMapOf]
  erw [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]

/-- **A fundamental class is transported to a fundamental class by a homeomorphism.**

If `c ∈ H_n(M; ℤ)` generates the local homology at every point of `M` and `e : M ≃ₜ M'`, then the
image of `c` under the chain map induced by `e` generates the local homology at every point of `M'`.

The proof localises at a point `x : M`: the homeomorphism restricts to a homeomorphism of the
complements of `x` and of `e x`, and the induced map on `H_n(M, M∖{x}) ⟶ H_n(M', M'∖{e x})` is an
isomorphism (`Work.Cohomology.relChainsMapOf_homologyMap_isIso`, applied to the two homotopy
equivalences), so it carries generators to generators; the identification of the two local classes
is `relLocClass_map_pair`. -/
theorem isFundClass_map_homeomorph {M M' : TopCat} {n : ℕ} (e : M ≃ₜ M')
    {c : (Work.Cohomology.singularChains ℤ M).homology n} (hc : Work.Orient.IsFundClass M n c) :
    Work.Orient.IsFundClass M' n
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ M M'
        (TopCat.ofHom ⟨fun x => e x, e.continuous_toFun⟩)) n c) := by
  intro y
  -- localise at `x = e⁻¹ y`
  obtain ⟨x, rfl⟩ : ∃ x : M, e x = y := ⟨e.symm y, e.apply_symm_apply y⟩
  let f : M ⟶ M' := TopCat.ofHom ⟨fun z => e z, e.continuous_toFun⟩
  let A : Set M := {z : M | z ≠ x}
  let B : Set M' := {w : M' | w ≠ e x}
  -- the restriction of `e` to the complements of `x` and `e x`
  let φ : ↥A ≃ₜ ↥B := Work.Cohomology.homeomorphComplSingleton e x (e x) rfl
  let g : TopCat.of ↥A ⟶ TopCat.of ↥B := TopCat.ofHom φ.toHomotopyEquiv.toFun
  have hw : Work.Cohomology.subtypeIncl M A ≫ f = g ≫ Work.Cohomology.subtypeIncl M' B := by
    apply TopCat.hom_ext
    ext z
    rfl
  -- both maps are quasi-isomorphisms, being homotopy equivalences
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ M M' f) k) := by
    intro k
    exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv (X := M) (Y := M')
      e.toHomotopyEquiv k
  have hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B) g) k) := by
    intro k
    exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of ↥A)
      (Y := TopCat.of ↥B) φ.toHomotopyEquiv k
  -- hence the induced map on the local homology at `x` is an isomorphism
  have hiso := Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := M) (Y := M') A B f g hw n hf hg
  haveI := hiso
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf M M' A B f g hw) n).hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso _).2
  -- the local class of the image is the image of the local class
  have hnat := relLocClass_map_pair (M := M) (M' := M') (n := n) f (K := {x}) (K' := {e x}) g hw c
  have hkey : Work.Orient.locClass M' n
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ M M' f) n c) (e x)
      = (HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf M M' A B f g hw) n)
          (Work.Orient.locClass M n c x) := by
    rw [Work.Orient.locClass_eq_relClass, Work.Orient.locClass_eq_relClass]
    simp only [Work.Orient.relClass]
    exact hnat.symm
  rw [hkey]
  -- an isomorphism carries a generating element to a generating element
  have h1 : Submodule.map
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf M M' A B f g hw) n).hom
      (Submodule.span ℤ {Work.Orient.locClass M n c x})
      = Submodule.span ℤ {((HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf M M' A B f g hw) n) (Work.Orient.locClass M n c x))} := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [← h1, hc x, Submodule.map_top, LinearMap.range_eq_top]
  exact hsurj

end Work.ThomBordism.Transversality.OrientBridge
