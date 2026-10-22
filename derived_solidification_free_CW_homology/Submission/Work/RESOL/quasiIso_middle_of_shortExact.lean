import Mathlib

/-!
# The five lemma for the middle term of a morphism of short exact sequences of complexes

Given a morphism `φ : S₁ ⟶ S₂` between short exact short complexes of cochain complexes in an
abelian category `A`, we show that if the maps induced on homology by `φ.τ₁` and `φ.τ₃` are
isomorphisms, then so is the one induced by `φ.τ₂`.

This is the five lemma applied to the long exact homology sequence of a short exact short complex
of homological complexes,
`... ⟶ H i (S.X₃) ⟶ H j (S.X₁) ⟶ H j (S.X₂) ⟶ H j (S.X₃) ⟶ H k (S.X₁) ⟶ ...`
(`c.Rel i j` and `c.Rel j k`), for `S₁` and for `S₂`, together with the naturality of the
connecting map `δ` (`HomologicalComplex.HomologySequence.δ_naturality`).

Mathlib contains the analogous statements for `φ.τ₃`
(`HomologicalComplex.HomologySequence.mono_homologyMap_τ₃`,
`...epi_homologyMap_τ₃`, `...isIso_homologyMap_τ₃`); the two lemmas below are the missing
counterparts for `φ.τ₂`.
-/

namespace Work.RESOL

open CategoryTheory Limits ComposableArrows HomologicalComplex HomologySequence

namespace ShortExactHomology

section

variable {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} {i j : ι}

/-- The "mono" half of the four lemma, applied to the 4-term exact sequence
`H i (S.X₃) ⟶ H j (S.X₁) ⟶ H j (S.X₂) ⟶ H j (S.X₃)` which is a piece of the long exact
homology sequence of a short exact short complex of homological complexes. -/
lemma mono_homologyMap_τ₂ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (hij : c.Rel i j) (h₁ : Epi (homologyMap φ.τ₃ i)) (h₂ : Mono (homologyMap φ.τ₁ j))
    (h₃ : Mono (homologyMap φ.τ₃ j)) : Mono (homologyMap φ.τ₂ j) := by
  apply Abelian.mono_of_epi_of_mono_of_mono
    ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    ((composableArrows₅_exact hS₁ i j hij).δ₀.δ₀)
    ((composableArrows₅_exact hS₂ i j hij).δ₀.δ₀)
  · dsimp; exact h₁
  · dsimp; exact h₂
  · dsimp; exact h₃

/-- The "epi" half of the four lemma, applied to the 4-term exact sequence
`H i (S.X₁) ⟶ H i (S.X₂) ⟶ H i (S.X₃) ⟶ H j (S.X₁)` which is a piece of the long exact
homology sequence of a short exact short complex of homological complexes. -/
lemma epi_homologyMap_τ₂ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (hij : c.Rel i j) (h₁ : Epi (homologyMap φ.τ₁ i)) (h₂ : Epi (homologyMap φ.τ₃ i))
    (h₃ : Mono (homologyMap φ.τ₁ j)) : Epi (homologyMap φ.τ₂ i) := by
  apply Abelian.epi_of_epi_of_epi_of_mono
    ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    ((composableArrows₅_exact hS₁ i j hij).δlast.δlast)
    ((composableArrows₅_exact hS₂ i j hij).δlast.δlast)
  · dsimp; exact h₁
  · dsimp; exact h₂
  · dsimp; exact h₃

end

end ShortExactHomology

set_option linter.style.haveILetI false in
/-- For a morphism of short exact sequences of cochain complexes in an abelian category, if the
first and the third vertical map are quasi-isomorphisms, then so is the middle one. -/
theorem quasiIso_middle_of_shortExact {A : Type*} [CategoryTheory.Category A]
    [CategoryTheory.Abelian A] {S₁ S₂ : CategoryTheory.ShortComplex (CochainComplex A ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hijm : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
  haveI hm : Mono (HomologicalComplex.homologyMap φ.τ₂ i) :=
    ShortExactHomology.mono_homologyMap_τ₂ φ hS₁ hS₂ hijm
      (by infer_instance) (by infer_instance) (by infer_instance)
  have hije : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
  haveI he : Epi (HomologicalComplex.homologyMap φ.τ₂ i) :=
    ShortExactHomology.epi_homologyMap_τ₂ φ hS₁ hS₂ hije
      (by infer_instance) (by infer_instance) (by infer_instance)
  exact isIso_of_mono_of_epi _

end Work.RESOL
