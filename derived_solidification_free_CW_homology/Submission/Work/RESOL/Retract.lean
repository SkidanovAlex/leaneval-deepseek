/-
AREA RESOL — the retraction criterion for solid-cofibrancy (the crux of B5).

If `K` is a *retract* (in the homotopy category `K(LightCondAb)`) of a solid-cofibrant complex
`T` — i.e. there are `ψ : K ⟶ T`, `φ : T ⟶ K` with `ψ ≫ φ = 𝟙 K` — then `K` is
solid-cofibrant.  Indeed `Qh` is a functor, so it preserves the relation
`Qh ψ ≫ Qh φ = 𝟙`, and the two bijectivity statements for `K` follow from the ones for `T` by
composing with `Qh φ` and `Qh ψ`.

This is the tool used in `RESOL/B5TowerSolid.lean`: a bounded-above complex of atoms is a
retract of the telescope of its truncations.
-/
import Mathlib
import Submission.Work.RESOL.Basic

open CategoryTheory

namespace Work.RESOL

/-- The quotient functor `CochainComplex LightCondAb ℤ ⥤ K(LightCondAb)` (the same as the
abbreviation `Submission.Blueprint.hq` applied to objects). -/
abbrev hqF : Cpx ⥤ KCat := HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)

/-- **The crux of B5, without any truncations**: if `K` is a *retract* (in `Cpx`) of a
solid-cofibrant complex `T` — i.e. there are `ψ : K ⟶ T`, `φ : T ⟶ K` with `ψ ≫ φ = 𝟙 K` —
then `K` is solid-cofibrant. -/
theorem solidCofibrant_of_retract {K T : Cpx} (ψ : K ⟶ T) (φ : T ⟶ K)
    (h : ψ ≫ φ = 𝟙 K) (hT : Submission.Blueprint.SolidCofibrant T) :
    Submission.Blueprint.SolidCofibrant K := by
  intro N
  have hψφ : hqF.map ψ ≫ hqF.map φ = 𝟙 (hqF.obj K) := by
    rw [← hqF.map_comp, h, hqF.map_id]
  constructor
  · intro f g hfg
    simp only [] at hfg
    have h1 : hqF.map φ ≫ f = hqF.map φ ≫ g := by
      apply (hT N).1
      show DerivedCategory.Qh.map (hqF.map φ ≫ f) = DerivedCategory.Qh.map (hqF.map φ ≫ g)
      rw [DerivedCategory.Qh.map_comp, DerivedCategory.Qh.map_comp, hfg]
    calc f = 𝟙 (hqF.obj K) ≫ f := (Category.id_comp f).symm
      _ = (hqF.map ψ ≫ hqF.map φ) ≫ f := by rw [hψφ]
      _ = hqF.map ψ ≫ (hqF.map φ ≫ f) := Category.assoc _ _ _
      _ = hqF.map ψ ≫ (hqF.map φ ≫ g) := by rw [h1]
      _ = (hqF.map ψ ≫ hqF.map φ) ≫ g := (Category.assoc _ _ _).symm
      _ = 𝟙 (hqF.obj K) ≫ g := by rw [hψφ]
      _ = g := Category.id_comp g
  · intro y
    obtain ⟨x, hx⟩ := (hT N).2 (DerivedCategory.Qh.map (hqF.map φ) ≫ y)
    simp only [] at hx
    refine ⟨hqF.map ψ ≫ x, ?_⟩
    show DerivedCategory.Qh.map (hqF.map ψ ≫ x) = y
    rw [DerivedCategory.Qh.map_comp, hx, ← Category.assoc, ← DerivedCategory.Qh.map_comp, hψφ,
      DerivedCategory.Qh.map_id, Category.id_comp]

end Work.RESOL
