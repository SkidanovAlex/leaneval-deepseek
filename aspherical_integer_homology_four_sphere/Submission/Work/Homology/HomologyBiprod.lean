import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Homology commutes with binary biproducts of chain complexes

For chain complexes `K` and `L` of `ℤ`-modules, the `n`-th homology of the
degreewise biproduct `K ⊞ L` is the biproduct of the `n`-th homologies:

`(K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n`.

The isomorphism is built from the maps induced in homology by the structure
maps of the biproduct of complexes: `homologyMap biprod.inl`, `homologyMap
biprod.fst`, etc.  Using the functoriality and additivity of `homologyMap`
together with the identities `biprod.inl ≫ biprod.fst = 𝟙`,
`biprod.total`, ... satisfied by the biproduct of complexes, these maps exhibit
`(K ⊞ L).homology n` as a biproduct of `K.homology n` and `L.homology n`.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Homology

noncomputable section

/-- If `c`, `d` are maps out of the two summands `X`, `Y` of a biproduct and
`a`, `b` are maps into them, and if the "biproduct identities"
`c ≫ a = 𝟙 X`, `d ≫ a = 0`, `c ≫ b = 0`, `d ≫ b = 𝟙 Y` hold, then
`biprod.desc c d` and `biprod.lift a b` are mutually inverse. -/
lemma biprod_desc_lift {C : Type*} [Category* C] [Preadditive C] {X Y Z : C}
    [HasBinaryBiproduct X Y]
    {a : Z ⟶ X} {b : Z ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (hca : c ≫ a = 𝟙 X) (hda : d ≫ a = 0) (hcb : c ≫ b = 0) (hdb : d ≫ b = 𝟙 Y) :
    biprod.desc c d ≫ biprod.lift a b = 𝟙 (X ⊞ Y) := by
  apply biprod.ext_from_iff.mpr
  constructor
  · rw [biprod.inl_desc_assoc]
    rw [biprod.lift_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hca, hcb,
      Category.id_comp, zero_comp, add_zero, Category.comp_id]
  · rw [biprod.inr_desc_assoc]
    rw [biprod.lift_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hda, hdb,
      zero_comp, Category.id_comp, zero_add, Category.comp_id]

/-- Homology commutes with binary biproducts of chain complexes. -/
theorem HomologyBiprod (K L : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Nonempty ((K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n) := by
  let a : (K ⊞ L).homology n ⟶ K.homology n := homologyMap (biprod.fst : K ⊞ L ⟶ K) n
  let b : (K ⊞ L).homology n ⟶ L.homology n := homologyMap (biprod.snd : K ⊞ L ⟶ L) n
  let c : K.homology n ⟶ (K ⊞ L).homology n := homologyMap (biprod.inl : K ⟶ K ⊞ L) n
  let d : L.homology n ⟶ (K ⊞ L).homology n := homologyMap (biprod.inr : L ⟶ K ⊞ L) n
  have hca : c ≫ a = 𝟙 (K.homology n) := by
    simp only [c, a, ← homologyMap_comp, biprod.inl_fst, homologyMap_id]
  have hdb : d ≫ b = 𝟙 (L.homology n) := by
    simp only [d, b, ← homologyMap_comp, biprod.inr_snd, homologyMap_id]
  have hcb : c ≫ b = 0 := by
    simp only [c, b, ← homologyMap_comp, biprod.inl_snd, homologyMap_zero]
  have hda : d ≫ a = 0 := by
    simp only [d, a, ← homologyMap_comp, biprod.inr_fst, homologyMap_zero]
  have hac : a ≫ c + b ≫ d = 𝟙 ((K ⊞ L).homology n) := by
    simp only [a, c, b, d, ← homologyMap_comp, ← homologyMap_add, biprod.total, homologyMap_id]
  exact ⟨{ hom := biprod.lift a b
           inv := biprod.desc c d
           hom_inv_id := by rw [biprod.lift_desc]; exact hac
           inv_hom_id := biprod_desc_lift hca hda hcb hdb }⟩

end

end Work.Homology
