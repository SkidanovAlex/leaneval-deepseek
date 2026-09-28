import Mathlib
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.homotopyEquiv_prod_fst

/-!
# Maps of the trivial bundle over a base

Two continuous maps used to compare the pair `(B × ℝⁿ, B × (ℝⁿ∖0))` with the pair
`(ℝⁿ, ℝⁿ∖0)`:

* `Work.Thom.prodSnd B Z` — the second projection `B × Z → Z` (the bundle projection of the
  trivial bundle `B × Z → B`, read in the other direction: it is the map to the fibre);
* `Work.Thom.subtypeProj B Z S` — its restriction to the preimage of `S ⊆ Z`, as a map
  `{p : B × Z // p.2 ∈ S} → S`.
-/

namespace Work.Thom

open CategoryTheory AlgebraicTopology

/-- The second projection `B × Z → Z` as a continuous map. -/
def prodSnd (B Z : Type*) [TopologicalSpace B] [TopologicalSpace Z] : C(B × Z, Z) :=
  ⟨Prod.snd, continuous_snd⟩


/-! ## Suggested route for the restricted projection

`Work.Cohomology.homotopyEquiv_prod_fst` proves that `X × Y → X` is a homotopy equivalence when
`Y` is contractible.  To apply it to `subtypeProj B Z S` one first identifies

`{p : B × Z // p.2 ∈ S} ≃ₜ B × S`

by `Homeomorph.setCongr` (rewriting `{p | p.2 ∈ S}` as `(Set.univ : Set B) ×ˢ S`), then
`Homeomorph.Set.prod (Set.univ : Set B) S`, then
`(Homeomorph.Set.univ B).prodCongr (Homeomorph.refl S)` — the composite of these is a
`ContinuousMap.HomotopyEquiv`, and composing with
`(Homeomorph.prodComm B S).toHomotopyEquiv` and `(homotopyEquiv_prod_fst ↥S B).some` gives a
homotopy equivalence `{p : B × Z // p.2 ∈ S} ≃ₕ S` whose `toFun` is (definitionally) the
projection `⟨(b,z),hz⟩ ↦ ⟨z,hz⟩ = subtypeProj B Z S _`.  The file
`Submission/Work/Cohomology/homotopyEquiv_A1set.lean` does exactly this pattern (for
`punctured sphere × sphere`), and `Work.Thom.isIso_homologyMap_dualChainMap_prodSnd` above is the
unrestricted case proved directly from `id_nullhomotopic`.

Alternatively, build the `HomotopyEquiv` by hand with `toFun := subtypeProj B Z S` and the
explicit homotopy `(t,p) ↦ ⟨(H(t,p.1.1), p.1.2), p.2⟩` where `H : I × B → B` is the nullhomotopy
of `id B` (`id_nullhomotopic B`). -/

/-- The projection `{p : B × Z // p.2 ∈ S} → S`, `⟨(b,z),hz⟩ ↦ ⟨z,hz⟩`. -/
def subtypeProj (B Z : Type*) [TopologicalSpace B] [TopologicalSpace Z] (S : Set Z) :
    C({p : B × Z // p.2 ∈ S}, S) :=
  ⟨fun p => ⟨p.1.2, p.2⟩, Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _⟩

@[simp]
theorem subtypeProj_apply (B Z : Type*) [TopologicalSpace B] [TopologicalSpace Z]
    (S : Set Z) (p : {p : B × Z // p.2 ∈ S}) :
    subtypeProj B Z S p = ⟨p.1.2, p.2⟩ := rfl

/-- For a contractible space `B`, the second projection `B × Z → Z` induces an isomorphism on
singular cohomology with coefficients in `R` in every degree. -/
theorem isIso_homologyMap_dualChainMap_prodSnd {B Z : Type} [TopologicalSpace B]
    [TopologicalSpace Z] [ContractibleSpace B] (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of (B × Z)) (TopCat.of Z) (TopCat.ofHom (prodSnd B Z))) n) := by
  obtain ⟨b₀, hb₀⟩ := id_nullhomotopic B
  let g : C(Z, B × Z) := ⟨fun z => (b₀, z), continuous_const.prodMk continuous_id⟩
  have h2 : (prodSnd B Z).comp g = ContinuousMap.id Z := by
    refine ContinuousMap.ext fun z => ?_
    rfl
  have h1 : g.comp (prodSnd B Z)
      = (ContinuousMap.const B b₀).prodMap (ContinuousMap.id Z) := by
    refine ContinuousMap.ext fun p => ?_
    obtain ⟨b, z⟩ := p
    rfl
  have hid : ContinuousMap.id (B × Z)
      = (ContinuousMap.id B).prodMap (ContinuousMap.id Z) := by
    refine ContinuousMap.ext fun p => ?_
    obtain ⟨b, z⟩ := p
    rfl
  have h2h : ((prodSnd B Z).comp g).Homotopic (ContinuousMap.id Z) :=
    h2.symm ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id Z)
  have h1h : (g.comp (prodSnd B Z)).Homotopic (ContinuousMap.id (B × Z)) :=
    h1.symm ▸ (hid.symm ▸ hb₀.symm.prodMap (ContinuousMap.Homotopic.refl _))
  exact Work.Cohomology.homotopyEquiv R (TopCat.of (B × Z)) (TopCat.of Z)
    (TopCat.ofHom (prodSnd B Z)) (TopCat.ofHom g) h1h.some h2h.some n

end Work.Thom
