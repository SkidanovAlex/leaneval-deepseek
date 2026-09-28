import Mathlib

open CategoryTheory Limits ComposableArrows

namespace Work.Cohomology

theorem isIso_homologyMap_tau1 (R : Type) [CommRing R]
    {S₁ S₂ : CategoryTheory.ShortComplex (CochainComplex (ModuleCat R) ℕ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₂ : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₂ n))
    (h₃ : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ n)) :
    ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₁ n) := by
  intro n
  rcases n with _ | m
  · -- degree 0 : the connecting map into degree 0 is zero, so the reduced five
    -- lemma `isIso_of_isIso_of_mono` applies to the three-term exact sequences
    -- `H₀(X₁) → H₀(X₂) → H₀(X₃)`.
    have hmono₁ : Mono ((HomologicalComplex.HomologySequence.composableArrows₂ S₁ 0).map' 0 1) := by
      have h : Mono S₁.f := hS₁.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₁.f 0
        (fun i hi => by rw [ComplexShape.up_Rel] at hi; omega)
    have hmono₂ : Mono ((HomologicalComplex.HomologySequence.composableArrows₂ S₂ 0).map' 0 1) := by
      have h : Mono S₂.f := hS₂.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₂.f 0
        (fun i hi => by rw [ComplexShape.up_Rel] at hi; omega)
    refine CategoryTheory.Abelian.isIso_of_isIso_of_mono
      (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ 0) ?_ ?_ hmono₁ hmono₂ ?_ ?_
    · exact HomologicalComplex.HomologySequence.composableArrows₂_exact hS₁ 0
    · exact HomologicalComplex.HomologySequence.composableArrows₂_exact hS₂ 0
    · exact h₂ 0
    · have h : IsIso (HomologicalComplex.homologyMap φ.τ₃ 0) := h₃ 0
      exact IsIso.mono_of_iso (HomologicalComplex.homologyMap φ.τ₃ 0)
  · -- degree `m + 1 ≥ 1` : five lemma on the exact sequence
    -- `H_m(X₂) → H_m(X₃) → H_{m+1}(X₁) → H_{m+1}(X₂) → H_{m+1}(X₃)`.
    have hij : (ComplexShape.up ℕ).Rel m (m + 1) := by rw [ComplexShape.up_Rel]
    refine CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 1) (n := 5)
      (by norm_num) ?_ ?_
      (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ m (m + 1) hij)
      1 2 3 4 5 rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
    · exact HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ m (m + 1) hij
    · exact HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ m (m + 1) hij
    · have h : IsIso (HomologicalComplex.homologyMap φ.τ₂ m) := h₂ m
      exact IsIso.epi_of_iso (HomologicalComplex.homologyMap φ.τ₂ m)
    · exact h₃ m
    · exact h₂ (m + 1)
    · have h : IsIso (HomologicalComplex.homologyMap φ.τ₃ (m + 1)) := h₃ (m + 1)
      exact IsIso.mono_of_iso (HomologicalComplex.homologyMap φ.τ₃ (m + 1))

end Work.Cohomology
