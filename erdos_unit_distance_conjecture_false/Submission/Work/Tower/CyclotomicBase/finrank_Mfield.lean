import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.Mof_disc
import Submission.Work.Tower.CyclotomicBase.exists_mulEquiv_Mfield_gal

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

/-- The degree of the field `M` cut out by the `ℓ` independent cubic characters is `3 ^ ℓ`:
`M/ℚ` is Galois with Galois group `≃* (ℤ/3)^ℓ`, and a Galois extension's degree equals the
order of its Galois group. -/
theorem finrank_Mfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    Module.finrank ℚ ↥(Mfield r hr hr3) = 3 ^ ℓ := by
  haveI := isGalois_Mfield r hr hr3
  obtain ⟨e⟩ := exists_mulEquiv_Mfield_gal r hr hr3 hrinj
  rw [← IsGalois.card_aut_eq_finrank]
  rw [Nat.card_congr e.toEquiv]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_fun, Fintype.card_multiplicative, ZMod.card, Fintype.card_fin]

end Work.Tower.CyclotomicBase
