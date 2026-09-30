import Mathlib
import Submission.Work.HomologyExtra.SimplexDisk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyExtra

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- A homeomorphism `e : X ≃ₜ Y` carrying `A ⊆ X` onto `B ⊆ Y` induces an isomorphism on
relative singular homology `H_k(X,A) ≅ H_k(Y,B)` in every degree. -/
theorem isIso_relHomologyMap_pairHomOfHomeomorph {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X}
    {B : Set Y} (he : ∀ x : X, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod k
      (Work.HomologyExtra.pairHomOfHomeomorph e he)) := by
  -- The inverse homeomorphism induces the inverse map of pairs `(Y,B) → (X,A)`.
  have heinv : ∀ y : Y, y ∈ B ↔ e.symm y ∈ A := by
    intro y
    simpa using (he (e.symm y)).symm
  let Φ : Work.Homology.PairHom X Y A B := Work.HomologyExtra.pairHomOfHomeomorph e he
  let Ψ : Work.Homology.PairHom Y X B A := Work.HomologyExtra.pairHomOfHomeomorph e.symm heinv
  have hΦ : Φ.hom = Work.Homology.homeomorphTopCatHom e := rfl
  have hΨ : Ψ.hom = Work.Homology.homeomorphTopCatInv e := rfl
  -- The two maps of pairs are mutually inverse on the level of spaces.
  have hcomp₁ : Φ.hom ≫ Ψ.hom = 𝟙 X := by
    rw [hΦ, hΨ, Work.Homology.homeomorphTopCatHom_comp_inv]
  have hcomp₂ : Ψ.hom ≫ Φ.hom = 𝟙 Y := by
    rw [hΦ, hΨ, Work.Homology.homeomorphTopCatInv_comp_hom]
  -- Hence so are the induced maps of singular chain complexes.
  have hs₁ : Work.Homology.singChainMap Work.Homology.ZMod Φ.hom
      ≫ Work.Homology.singChainMap Work.Homology.ZMod Ψ.hom = 𝟙 _ := by
    rw [← Work.Homology.singChainMap_comp, hcomp₁, Work.Homology.singChainMap_id]
  have hs₂ : Work.Homology.singChainMap Work.Homology.ZMod Ψ.hom
      ≫ Work.Homology.singChainMap Work.Homology.ZMod Φ.hom = 𝟙 _ := by
    rw [← Work.Homology.singChainMap_comp, hcomp₂, Work.Homology.singChainMap_id]
  -- On the relative chain complexes the induced maps (defined by the universal property of the
  -- cokernel, characterised by `relChainMap_comp_relProj`) are mutually inverse: the projection
  -- `relProj` is an epimorphism, so it suffices to check after composing with it.
  have h₁ : Work.Homology.relChainMap Work.Homology.ZMod Φ
      ≫ Work.Homology.relChainMap Work.Homology.ZMod Ψ = 𝟙 _ := by
    apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod X A)).1
    rw [← Category.assoc, ← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod) Φ,
      Category.assoc, ← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod) Ψ,
      ← Category.assoc, hs₁, Category.id_comp, Category.comp_id]
  have h₂ : Work.Homology.relChainMap Work.Homology.ZMod Ψ
      ≫ Work.Homology.relChainMap Work.Homology.ZMod Φ = 𝟙 _ := by
    apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod Y B)).1
    rw [← Category.assoc, ← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod) Ψ,
      Category.assoc, ← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod) Φ,
      ← Category.assoc, hs₂, Category.id_comp, Category.comp_id]
  -- Passing to homology gives the required two-sided inverse.
  refine ⟨HomologicalComplex.homologyMap (Work.Homology.relChainMap Work.Homology.ZMod Ψ) k,
    ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, h₁, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, h₂, HomologicalComplex.homologyMap_id]

end

end Work.HomologyExtra
