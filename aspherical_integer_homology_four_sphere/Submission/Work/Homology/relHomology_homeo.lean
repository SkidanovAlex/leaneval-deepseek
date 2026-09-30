import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.RelChainMap
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.SingHomologyHomeomorph

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Homology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- A homeomorphism `e : X ≃ₜ Y` carrying `A ⊆ X` onto `B ⊆ Y`, regarded as a map of pairs
`(X, A) → (Y, B)`. -/
def pairHomOfHomeo {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (h : ∀ x : X, x ∈ A ↔ e x ∈ B) : PairHom X Y A B where
  hom := homeomorphTopCatHom e
  mapsTo := fun x hx => (h x).1 hx

@[simp]
theorem pairHomOfHomeo_hom {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (h : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    (pairHomOfHomeo e h).hom = homeomorphTopCatHom e := rfl

/-- A homeomorphism of pairs induces an isomorphism on relative homology. -/
theorem relHomology_homeo {X Y : TopCat} (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (h : ∀ x : X, x ∈ A ↔ e x ∈ B) (m : ℕ) :
    Nonempty (relHomology ZMod m X A ≅ relHomology ZMod m Y B) := by
  -- The inverse homeomorphism carries `B` back onto `A`.
  have hsymm : ∀ y : Y, y ∈ B ↔ e.symm y ∈ A := by
    intro y
    simpa using (h (e.symm y)).symm
  let Φ : PairHom X Y A B := pairHomOfHomeo e h
  let Ψ : PairHom Y X B A := pairHomOfHomeo e.symm hsymm
  have hΦ : Φ.hom = homeomorphTopCatHom e := rfl
  have hΨ : Ψ.hom = homeomorphTopCatInv e := rfl
  -- The two maps of pairs are mutually inverse on the level of spaces.
  have hcomp₁ : Φ.hom ≫ Ψ.hom = 𝟙 X := by
    rw [hΦ, hΨ, homeomorphTopCatHom_comp_inv]
  have hcomp₂ : Ψ.hom ≫ Φ.hom = 𝟙 Y := by
    rw [hΦ, hΨ, homeomorphTopCatInv_comp_hom]
  -- Hence so are the induced maps of singular chain complexes.
  have hs₁ : singChainMap ZMod Φ.hom ≫ singChainMap ZMod Ψ.hom = 𝟙 (singChain ZMod X) := by
    rw [← singChainMap_comp, hcomp₁, singChainMap_id]
  have hs₂ : singChainMap ZMod Ψ.hom ≫ singChainMap ZMod Φ.hom = 𝟙 (singChain ZMod Y) := by
    rw [← singChainMap_comp, hcomp₂, singChainMap_id]
  -- The induced maps on relative chain complexes (characterised by `relChainMap_comp_relProj`)
  -- are mutually inverse: `relProj` is an epimorphism, so it suffices to check after composing.
  have h₁ : relChainMap ZMod Φ ≫ relChainMap ZMod Ψ = 𝟙 (relChain ZMod X A) := by
    apply (cancel_epi (relProj ZMod X A)).1
    rw [← Category.assoc, ← relChainMap_comp_relProj (R := ZMod) Φ, Category.assoc,
      ← relChainMap_comp_relProj (R := ZMod) Ψ, ← Category.assoc, hs₁, Category.id_comp,
      Category.comp_id]
  have h₂ : relChainMap ZMod Ψ ≫ relChainMap ZMod Φ = 𝟙 (relChain ZMod Y B) := by
    apply (cancel_epi (relProj ZMod Y B)).1
    rw [← Category.assoc, ← relChainMap_comp_relProj (R := ZMod) Ψ, Category.assoc,
      ← relChainMap_comp_relProj (R := ZMod) Φ, ← Category.assoc, hs₂, Category.id_comp,
      Category.comp_id]
  -- Passing to homology gives the required two-sided inverse.
  refine ⟨{ hom := HomologicalComplex.homologyMap (relChainMap ZMod Φ) m
            inv := HomologicalComplex.homologyMap (relChainMap ZMod Ψ) m
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [← HomologicalComplex.homologyMap_comp, h₁, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, h₂, HomologicalComplex.homologyMap_id]

end

end Work.Homology
