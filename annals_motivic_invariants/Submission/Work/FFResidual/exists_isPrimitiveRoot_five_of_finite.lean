import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FFResidual

/-- **A finite field whose cardinality satisfies `5 ∣ #𝔽 - 1` contains a primitive fifth root of
unity.**  The unit group of a finite field is cyclic of order `#𝔽 - 1`, so an element of order `5`
exists as soon as `5` divides that order.  This supplies the hypothesis `ζ₅ ∈ 𝔽` of the Kummer
route (`FunctionFieldPlace.nonempty_hasPointlessTwist_of_place`) for class (c) of Theorem 1.2 (1) of
Lin–Shinder, *Motivic invariants of birational maps*, Annals of Math. **199** (1), 2024. -/
theorem exists_isPrimitiveRoot_five_of_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (h : 5 ∣ Nat.card 𝔽 - 1) : ∃ ζ : 𝔽, IsPrimitiveRoot ζ 5 := by
  -- The unit group of a finite field has order `#𝔽 - 1`; since the prime `5` divides that order,
  -- Cauchy's theorem produces an element of order `5` in `𝔽ˣ`, i.e. a primitive fifth root of
  -- unity in `𝔽`.
  have h5 : 5 ∣ Nat.card 𝔽ˣ := by
    rw [Nat.card_units]
    exact h
  obtain ⟨u, hu⟩ := @exists_prime_orderOf_dvd_card' 𝔽ˣ inferInstance inferInstance 5
    ⟨Nat.prime_five⟩ h5
  exact ⟨(u : 𝔽), by rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]; exact hu⟩

end Work.FFResidual
