import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.exists_unitsMap_eq

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

/-- The coordinate characters can be prescribed independently: the product character
`piChar : (ℤ/D)ˣ → (ℤ/3)^ℓ` is surjective.  Each coordinate value is realised by a unit of
`ℤ/rᵢ` (surjectivity of the cubic character), and the Chinese remainder theorem
(`exists_unitsMap_eq`) lifts the tuple to a single unit of `ℤ/D`. -/
theorem piChar_surjective_of_inj {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) :
    Function.Surjective (piChar r hr hr3) := by
  intro a
  have hb : ∀ i, ∃ b : (ZMod (r i))ˣ, cubeChar (r i) (hr i) (hr3 i) b = a i :=
    fun i => cubeChar_surjective (r i) (hr i) (hr3 i) (a i)
  choose b hb using hb
  obtain ⟨v, hv⟩ := exists_unitsMap_eq r hr hrinj b
  refine ⟨v, ?_⟩
  funext i
  show coordChar r hr hr3 i v = a i
  rw [coordChar, MonoidHom.comp_apply, hv i]
  exact hb i

theorem exists_mulEquiv_Mfield_gal {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    Nonempty (Gal(↥(Mfield r hr hr3)/ℚ) ≃* (Fin ℓ → Multiplicative (ZMod 3))) := by
  haveI : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  -- `galMap : Gal(ℚ(ζ_D)/ℚ) → (ℤ/3)^ℓ` is surjective.
  have hgsurj : Function.Surjective (galMap r hr hr3) :=
    (piChar_surjective_of_inj r hr hr3 hrinj).comp (galEquiv r).surjective
  -- `Gal(ℚ(ζ_D)/ℚ) ⧸ ker galMap ≃* (ℤ/3)^ℓ` (first isomorphism theorem) and
  -- `Gal(ℚ(ζ_D)/ℚ) ⧸ ker galMap ≃* Gal(M/ℚ)`, where `M = (ℚ(ζ_D))^{ker galMap}`.
  exact ⟨(IsGalois.normalAutEquivQuotient (galMap r hr hr3).ker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (galMap r hr hr3) hgsurj)⟩

end Work.Tower.CyclotomicBase
