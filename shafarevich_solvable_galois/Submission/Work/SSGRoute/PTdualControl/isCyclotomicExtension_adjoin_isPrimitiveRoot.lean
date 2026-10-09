import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

theorem isCyclotomicExtension_adjoin_isPrimitiveRoot (p : ℕ) [Fact p.Prime] {K Ω : Type} [Field K]
    [Field Ω] [Algebra K Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) :
    IsCyclotomicExtension {p} K ↥(IntermediateField.adjoin K {ζ} : IntermediateField K Ω) := by
  -- `p` is prime, hence nonzero, so `{p}` is a singleton of a nonzero natural number.
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `ζ` is a root of the monic polynomial `X ^ p - 1`, hence algebraic over `K`.
  have hζalg : IsAlgebraic K ζ := by
    have hint : IsIntegral K ζ := by
      refine IsIntegral.of_pow (Fact.out : p.Prime).pos ?_
      rw [hζ.pow_eq_one]
      exact isIntegral_one
    exact hint.isAlgebraic
  -- `K⟮ζ⟯` viewed as a subalgebra of `Ω` is `K[ζ]`, since `ζ` is algebraic over `K`.
  change IsCyclotomicExtension {p} K (IntermediateField.adjoin K {ζ}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
  -- Now this is exactly Mathlib's `IsPrimitiveRoot.adjoin_isCyclotomicExtension`.
  exact hζ.adjoin_isCyclotomicExtension K

end Work.SSGRoute.PTdualControl
