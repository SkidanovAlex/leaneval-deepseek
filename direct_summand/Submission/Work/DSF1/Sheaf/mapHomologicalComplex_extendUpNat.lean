import Mathlib

namespace Work.DSF1.Sheaf

open CategoryTheory Limits

theorem mapHomologicalComplex_extendUpNat {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasZeroObject D]
    (F : CategoryTheory.Functor C D) [F.Additive] (K : CochainComplex C ℕ) :
    Nonempty (CategoryTheory.Iso
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat))
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat)) := by
  let e := ComplexShape.embeddingUpNat
  let M : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  -- A family of isomorphisms `F.obj (extend.X K o) ≅ extend.X M o` which is the
  -- identity in the degrees lying in the image of `ℕ ↪ ℤ`, and an isomorphism
  -- between the two zero objects otherwise.
  let Φ : (o : Option ℕ) →
      F.obj (HomologicalComplex.extend.X K o) ≅ HomologicalComplex.extend.X M o :=
    fun o => match o with
      | some n => Iso.refl _
      | none => IsZero.iso (F.map_isZero (isZero_zero C)) (isZero_zero D)
  -- `Φ` is compatible with the differentials.
  have hA : ∀ (o o' : Option ℕ),
      (Φ o).hom ≫ HomologicalComplex.extend.d M o o' =
      F.map (HomologicalComplex.extend.d K o o') ≫ (Φ o').hom := by
    intro o o'
    rcases o with _ | n
    · rcases o' with _ | m
      · rw [HomologicalComplex.extend.d_none_eq_zero K none none rfl,
            HomologicalComplex.extend.d_none_eq_zero M none none rfl, F.map_zero]
        simp
      · rw [HomologicalComplex.extend.d_none_eq_zero K none (some m) rfl,
            HomologicalComplex.extend.d_none_eq_zero M none (some m) rfl, F.map_zero]
        simp
    · rcases o' with _ | m
      · rw [HomologicalComplex.extend.d_none_eq_zero' K (some n) none rfl,
            HomologicalComplex.extend.d_none_eq_zero' M (some n) none rfl, F.map_zero]
        simp
      · rw [show HomologicalComplex.extend.d M (some n) (some m) = M.d n m from rfl,
            show HomologicalComplex.extend.d K (some n) (some m) = K.d n m from rfl]
        show 𝟙 (F.obj (K.X n)) ≫ F.map (K.d n m) = F.map (K.d n m) ≫ 𝟙 (F.obj (K.X m))
        rw [Category.id_comp, Category.comp_id]
  exact ⟨HomologicalComplex.Hom.isoOfComponents (fun i' => Φ (e.r i'))
    (fun i' j' _ => hA _ _)⟩

end Work.DSF1.Sheaf
