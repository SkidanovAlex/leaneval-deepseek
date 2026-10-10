import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- A finite module over `ZMod l`, for `l` prime, has cardinality a power of `l`.
Indeed `ZMod l` is a finite field and `M` is a finite-dimensional vector space
over it. -/
theorem natCard_eq_prime_pow_of_module_zmod {l : ℕ} (hl : l.Prime) (M : Type*)
    [AddCommGroup M] [Module (ZMod l) M] [Finite M] : ∃ k : ℕ, Nat.card M = l ^ k := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : Module.Finite (ZMod l) M := Module.Finite.of_finite
  exact ⟨Module.finrank (ZMod l) M, by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]⟩

end Work.SSGRoute
