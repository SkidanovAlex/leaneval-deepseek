import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- **`Gal(F/k)` is cyclic of prime order `p`** when `F/k` is finite Galois of degree `p`:
`Nat.card Gal(F/k) = finrank k F = p` (`IsGalois.card_aut_eq_finrank`), and a group of prime
order is cyclic (`isCyclic_of_prime_card`). Auxiliary for the general-level cyclic norm criterion. -/
theorem galF_cyclic_card (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (F : IntermediateField k L) [FiniteDimensional k F] [IsGalois k F]
    (hF : Module.finrank k F = p) :
    IsCyclic (F ≃ₐ[k] F) ∧ Nat.card (F ≃ₐ[k] F) = p := by
  have hcard : Nat.card (F ≃ₐ[k] F) = p := by
    rw [IsGalois.card_aut_eq_finrank, hF]
  exact ⟨isCyclic_of_prime_card hcard, hcard⟩

end Work.SSGRoute.Sha2Lib
