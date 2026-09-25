import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.exists_mulEquiv_Mfield_gal

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

theorem finrank_Ffield_eq_three {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    Module.finrank ℚ ↥(Ffield r hr hr3) = 3 := by
  haveI : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  -- `galMap : Gal(ℚ(ζ_D)/ℚ) → (ℤ/3)^ℓ` is surjective (independence of the characters).
  have hgsurj : Function.Surjective (galMap r hr hr3) :=
    (piChar_surjective_of_inj r hr hr3 hrinj).comp (galEquiv r).surjective
  -- Hence the product character `χ₁⋯χ_ℓ = sumHom ∘ galMap` is surjective onto `ℤ/3`.
  have hφsurj : Function.Surjective ((sumHom ℓ).comp (galMap r hr hr3)) :=
    (sumHom_surjective hℓ).comp hgsurj
  -- Its kernel therefore has index `3` in `Gal(ℚ(ζ_D)/ℚ)`.
  have hidx : ((sumHom ℓ).comp (galMap r hr hr3)).ker.index = 3 := by
    rw [Subgroup.index_eq_card]
    have e := QuotientGroup.quotientKerEquivOfSurjective _ hφsurj
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp
  -- The Galois correspondence: `[F : ℚ]` equals the index of the fixing subgroup.
  unfold Ffield
  rw [IntermediateField.finrank_eq_fixingSubgroup_index (Cyc r) _,
    IntermediateField.fixingSubgroup_fixedField, hidx]

end Work.Tower.CyclotomicBase
