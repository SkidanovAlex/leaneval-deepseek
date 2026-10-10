import Mathlib
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.prodOver_affine_assoc
import Submission.Work.K3Inputs.stablyBirat_of_isoOver

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open MotivicInvariants
open Work.K3Inputs

noncomputable section

/-! ## Transport of the first factor of a product along an isomorphism over the base

This is the mirror image of `Work.K3Inputs.prodOver_iso_of_right` (in
`Submission/Work/K3Inputs/prodOver_affine_assoc.lean`), which transports the *second* factor.
Together the two give the invariance of `Work.K3.prodOver` in both variables. -/

/-- **Transport of the first factor along an isomorphism over the base.**

If `e : X ≅ X'` is an isomorphism over `Spec 𝕜`, then `X ×_𝕜 A ≅ X' ×_𝕜 A` over `Spec 𝕜`,
for every `𝕜`-scheme `A`.  The morphism is `pullback.map` along `e.hom` and `𝟙 A`; it is an
isomorphism since both components are, and it is over `Spec 𝕜` because `e` is. -/
theorem prodOver_iso_of_left (𝕜 : Type) [Field 𝕜] {X X' : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [X'.Over (Spec (.of 𝕜))] (A : Scheme.{0}) [A.Over (Spec (.of 𝕜))] (e : X ≅ X')
    (he : e.hom.IsOver (Spec (.of 𝕜))) :
    ∃ E : Work.K3.prodOver 𝕜 X A ≅ Work.K3.prodOver 𝕜 X' A, E.hom.IsOver (Spec (.of 𝕜)) := by
  have he' : e.hom ≫ (X' ↘ Spec (.of 𝕜)) = (X ↘ Spec (.of 𝕜)) :=
    (Hom.isOver_iff (S := Spec (.of 𝕜))).mp he
  have he'' : e.inv ≫ (X ↘ Spec (.of 𝕜)) = (X' ↘ Spec (.of 𝕜)) := by
    rw [← he', ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let φ : pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ⟶
      pullback (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) :=
    pullback.lift (pullback.fst _ _ ≫ e.hom) (pullback.snd _ _)
      (by rw [Category.assoc, he']; exact pullback.condition)
  let ψ : pullback (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ⟶
      pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) :=
    pullback.lift (pullback.fst _ _ ≫ e.inv) (pullback.snd _ _)
      (by rw [Category.assoc, he'']; exact pullback.condition)
  have hφf : φ ≫ pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
      = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom := pullback.lift_fst _ _ _
  have hφs : φ ≫ pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
      = pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := pullback.lift_snd _ _ _
  have hψf : ψ ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
      = pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.inv := pullback.lift_fst _ _ _
  have hψs : ψ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
      = pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := pullback.lift_snd _ _ _
  have hφψ : φ ≫ ψ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := by
    apply pullback.hom_ext
    · calc (φ ≫ ψ) ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
          = φ ≫ (ψ ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = φ ≫ (pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.inv) := by rw [hψf]
        _ = (φ ≫ pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) ≫ e.inv :=
              (Category.assoc ..).symm
        _ = (pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom) ≫ e.inv := by rw [hφf]
        _ = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (e.hom ≫ e.inv) :=
              Category.assoc ..
        _ = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ 𝟙 X := by rw [e.hom_inv_id]
        _ = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := Category.comp_id ..
        _ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)))
              ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := (Category.id_comp ..).symm
    · calc (φ ≫ ψ) ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
          = φ ≫ (ψ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = φ ≫ pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := by rw [hψs]
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := hφs
        _ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)))
              ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := (Category.id_comp _).symm
  have hψφ : ψ ≫ φ = 𝟙 (pullback (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := by
    apply pullback.hom_ext
    · calc (ψ ≫ φ) ≫ pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
          = ψ ≫ (φ ≫ pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = ψ ≫ (pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom) := by rw [hφf]
        _ = (ψ ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) ≫ e.hom :=
              (Category.assoc ..).symm
        _ = (pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.inv) ≫ e.hom := by rw [hψf]
        _ = pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (e.inv ≫ e.hom) :=
              Category.assoc ..
        _ = pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ 𝟙 X' := by rw [e.inv_hom_id]
        _ = pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := Category.comp_id ..
        _ = 𝟙 (pullback (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)))
              ≫ pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := (Category.id_comp ..).symm
    · calc (ψ ≫ φ) ≫ pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
          = ψ ≫ (φ ≫ pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = ψ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := by rw [hφs]
        _ = pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := hψs
        _ = 𝟙 (pullback (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)))
              ≫ pullback.snd (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := (Category.id_comp _).symm
  refine ⟨⟨φ, ψ, hφψ, hψφ⟩, ?_⟩
  rw [Hom.isOver_iff]
  show φ ≫ (pullback.fst (X' ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (X' ↘ Spec (.of 𝕜)))
    = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜))
  rw [← Category.assoc, hφf, Category.assoc, he']

/-- **Stable birationality is invariant under isomorphisms over the base.**

`Work.K3Inputs.StablyBirat 𝕜 X Y = ∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ` (Mathlib's `Scheme.Birational`, i.e.
existence of a partial isomorphism).  Isomorphisms `e : X ≅ X'`, `e' : Y ≅ Y'` over `Spec 𝕜` can be
pulled back along the products (`X × 𝔸ⁿ ≅ X' × 𝔸ⁿ`, `Y × 𝔸ᵐ ≅ Y' × 𝔸ᵐ`), so the relation is
unchanged.  Together with `Work.K3Inputs.stablyBirat_of_isoOver` this makes `StablyBirat` a
statement about birational classes, which is what allows the K3 link data to be compared between
different models of the same link. -/
theorem stablyBirat_congr (𝕜 : Type) [Field 𝕜] {X X' Y Y' : Scheme.{0}}
    [X.Over (Spec (.of 𝕜))] [X'.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    [Y'.Over (Spec (.of 𝕜))] (hX : Work.K3.IsoOver 𝕜 X X') (hY : Work.K3.IsoOver 𝕜 Y Y') :
    StablyBirat 𝕜 X Y ↔ StablyBirat 𝕜 X' Y' := by
  obtain ⟨e₁, he₁⟩ := hX
  obtain ⟨e₂, he₂⟩ := hY
  constructor
  · rintro ⟨n, m, hb⟩
    obtain ⟨E₁, -⟩ := prodOver_iso_of_left 𝕜 (AffineN 𝕜 n) e₁ he₁
    obtain ⟨E₂, -⟩ := prodOver_iso_of_left 𝕜 (AffineN 𝕜 m) e₂ he₂
    exact ⟨n, m, (Birational.trans ⟨PartialIso.ofIso E₁.symm⟩ hb).trans
      ⟨PartialIso.ofIso E₂⟩⟩
  · rintro ⟨n, m, hb⟩
    obtain ⟨E₁, -⟩ := prodOver_iso_of_left 𝕜 (AffineN 𝕜 n) e₁ he₁
    obtain ⟨E₂, -⟩ := prodOver_iso_of_left 𝕜 (AffineN 𝕜 m) e₂ he₂
    exact ⟨n, m, (Birational.trans ⟨PartialIso.ofIso E₁⟩ hb).trans
      ⟨PartialIso.ofIso E₂.symm⟩⟩

end

end Work.K3Inputs
