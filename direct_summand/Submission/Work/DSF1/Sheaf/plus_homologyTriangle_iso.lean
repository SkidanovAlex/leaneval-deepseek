import Mathlib

universe u v

-- `haveI` is used below to register `Mono`/`Epi` instances for the connecting map.
set_option linter.style.haveILetI false

namespace Work.DSF1.Sheaf

theorem plus_homologyTriangle_iso {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory C]
    {T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory.Plus C)}
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) (i : ℤ)
    (h₁ : CategoryTheory.Limits.IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₂))
    (h₂ : CategoryTheory.Limits.IsZero ((DerivedCategory.Plus.homologyFunctor C (i+1)).obj T.obj₂)) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₃ ≅
              (DerivedCategory.Plus.homologyFunctor C (i+1)).obj T.obj₁) := by
  -- View `T` as a distinguished triangle in the (unbounded) derived category via the
  -- triangulated inclusion `Plus.ι`.
  have hT' : DerivedCategory.Plus.ι.mapTriangle.obj T ∈
      CategoryTheory.Pretriangulated.distinguishedTriangles (C := DerivedCategory C) :=
    DerivedCategory.Plus.ι.map_distinguished T hT
  -- The connecting homomorphism of the long exact homology sequence, for `n₀ = i`, `n₁ = i+1`.
  let h : i + 1 = i + 1 := rfl
  let δ := (DerivedCategory.homologyFunctor C 0).homologySequenceδ
      (DerivedCategory.Plus.ι.mapTriangle.obj T) i (i+1) h
  -- Rewriting the two vanishing hypotheses at the level of the derived category.
  have h₁' : CategoryTheory.Limits.IsZero (((DerivedCategory.homologyFunctor C 0).shift i).obj
      (DerivedCategory.Plus.ι.mapTriangle.obj T).obj₂) := h₁
  have h₂' : CategoryTheory.Limits.IsZero (((DerivedCategory.homologyFunctor C 0).shift (i+1)).obj
      (DerivedCategory.Plus.ι.mapTriangle.obj T).obj₂) := h₂
  -- Exactness at `H^i(T₃)` and at `H^{i+1}(T₁)`, using `H^i(T₂) = 0` and `H^{i+1}(T₂) = 0`.
  haveI hm : CategoryTheory.Mono δ :=
    (DerivedCategory.homologyFunctor C 0).homologySequence_exact₃ _ hT' i (i+1) h |>.mono_g
      (h₁'.eq_of_src _ _)
  haveI he : CategoryTheory.Epi δ :=
    (DerivedCategory.homologyFunctor C 0).homologySequence_exact₁ _ hT' i (i+1) h |>.epi_f
      (h₂'.eq_of_tgt _ _)
  have hδ : CategoryTheory.IsIso δ := CategoryTheory.isIso_of_mono_of_epi δ
  exact ⟨@CategoryTheory.asIso _ _ _ _ δ hδ⟩

end Work.DSF1.Sheaf
