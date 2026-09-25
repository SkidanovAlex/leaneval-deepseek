import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.splitSetOf_density

/-!
# Setup for `invChar_le_invCharSubmodule`

Given a finite Galois extension `L / K` of number fields of degree `p`, the Galois group `L ≃ₐ[K] L`
has order `p`, hence is abelian and a `p`-group.  This lets us feed the class fields supplied by
`CFTLib.PClassFieldArtin` into the maximality hypothesis `hmax` of the relative Shafarevich bound.
-/

namespace Work.CFTLib

open NumberField

variable {K : Type} [Field K] [NumberField K]

/-- A finite Galois extension of prime degree has abelian Galois group. -/
theorem comm_of_finrank_prime {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]
    (h : Module.finrank K L = p) (a b : L ≃ₐ[K] L) : a * b = b * a := by
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank, h]
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card hcard
  exact IsMulCommutative.is_comm.comm a b

/-- A finite Galois extension of prime degree has Galois group a `p`-group. -/
theorem isPGroup_of_finrank_prime {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]
    (h : Module.finrank K L = p) : IsPGroup p (L ≃ₐ[K] L) := by
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank, h]
  exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])

end Work.CFTLib
