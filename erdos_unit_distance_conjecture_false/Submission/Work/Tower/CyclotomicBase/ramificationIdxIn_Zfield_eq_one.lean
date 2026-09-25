import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.isCyclotomicExtension_Zfield
import Submission.Work.Tower.CyclotomicBase.ramificationIdxIn_cyc

/-!
# The prime `rᵢ` is unramified in its own inertia field `Zfield r i`

The inertia field `Zfield r i` of the prime `rᵢ` in `ℚ(ζ_D)` is the cyclotomic field
`ℚ(ζ_{D/rᵢ})` (`isCyclotomicExtension_Zfield`).  Since the primes `r j` are pairwise distinct,
`rᵢ` does not divide `D / rᵢ` (`not_dvd_div_D`), so `rᵢ` is unramified in `ℚ(ζ_{D/rᵢ})` by
Mathlib's `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd`.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Tower.CyclotomicBase

theorem ramificationIdxIn_Zfield_eq_one {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ) :
    (Ideal.span {(r i : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers ↥(Zfield r i)) = 1 := by
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  haveI : NeZero (D r / r i) := ⟨by
    have h := Nat.div_mul_cancel (r_dvd_D r i)
    intro h0
    rw [h0, zero_mul] at h
    exact NeZero.ne (D r) h.symm⟩
  haveI : IsCyclotomicExtension {D r / r i} ℚ ↥(Zfield r i) :=
    isCyclotomicExtension_Zfield r hr i
  exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (K := ↥(Zfield r i))
    (m := D r / r i) (r i) (not_dvd_div_D r hr hrinj i)

end Work.Tower.CyclotomicBase
