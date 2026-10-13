import Mathlib

universe u v

-- `haveI` registers the `Epi` instance for the connecting map of the long exact sequence.
set_option linter.style.haveILetI false

namespace Work.DSF1.Sheaf

/-- In a preadditive category, an epimorphism that is the zero morphism has a zero target. -/
lemma isZero_target_of_epi_eq_zero {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Preadditive C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Epi f]
    (h : f = 0) : CategoryTheory.Limits.IsZero Y := by
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero, ← CategoryTheory.cancel_epi f]
  rw [h]
  simp

/-- For a distinguished triangle `T` in the bounded-below derived category and an integer `i`,
if `H^{i+1}(T.obj₂)` vanishes then `H^{i+1}(T.obj₁)` vanishes if and only if the induced map
`H^i(T.obj₂) ⟶ H^i(T.obj₃)` is an epimorphism. -/
theorem plus_homologyTriangle_isZero_iff_epi {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory C]
    {T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory.Plus C)}
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) (i : ℤ)
    (h₂ : CategoryTheory.Limits.IsZero ((DerivedCategory.Plus.homologyFunctor C (i+1)).obj T.obj₂)) :
    CategoryTheory.Limits.IsZero ((DerivedCategory.Plus.homologyFunctor C (i+1)).obj T.obj₁) ↔
      CategoryTheory.Epi ((DerivedCategory.Plus.homologyFunctor C i).map T.mor₂) := by
  -- View `T` as a distinguished triangle in the (unbounded) derived category via `Plus.ι`.
  have hT' : DerivedCategory.Plus.ι.mapTriangle.obj T ∈
      CategoryTheory.Pretriangulated.distinguishedTriangles (C := DerivedCategory C) :=
    DerivedCategory.Plus.ι.map_distinguished T hT
  -- The connecting homomorphism `δ : H^i(T₃) ⟶ H^{i+1}(T₁)` of the long exact homology sequence.
  let h : i + 1 = i + 1 := rfl
  let δ := (DerivedCategory.homologyFunctor C 0).homologySequenceδ
      (DerivedCategory.Plus.ι.mapTriangle.obj T) i (i+1) h
  -- The vanishing hypothesis `H^{i+1}(T₂) = 0`, at the level of the derived category.
  have h₂' : CategoryTheory.Limits.IsZero
      (((DerivedCategory.homologyFunctor C 0).shift (i+1)).obj
        (DerivedCategory.Plus.ι.mapTriangle.obj T).obj₂) := h₂
  -- Exactness at `H^{i+1}(T₁)` then makes `δ` an epimorphism.
  haveI : CategoryTheory.Epi δ :=
    ((DerivedCategory.homologyFunctor C 0).homologySequence_exact₁ _ hT' i (i+1) h).epi_f
      (h₂'.eq_of_tgt _ _)
  -- `H^i(T₂) ⟶ H^i(T₃)` is an epimorphism iff `δ = 0` (exactness at `H^i(T₃)`).
  have hiff : CategoryTheory.Epi
      (((DerivedCategory.homologyFunctor C 0).shift i).map
        (DerivedCategory.Plus.ι.mapTriangle.obj T).mor₂) ↔ δ = 0 :=
    (DerivedCategory.homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT' i (i+1) h
  -- Since `δ` is an epimorphism, its target `H^{i+1}(T₁)` is zero iff `δ = 0`.
  have hzero : CategoryTheory.Limits.IsZero
      (((DerivedCategory.homologyFunctor C 0).shift (i+1)).obj
        (DerivedCategory.Plus.ι.mapTriangle.obj T).obj₁) ↔ δ = 0 :=
    ⟨fun hh => hh.eq_of_tgt δ 0, fun hh => isZero_target_of_epi_eq_zero δ hh⟩
  exact hzero.trans hiff.symm

end Work.DSF1.Sheaf
