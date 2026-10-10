import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The residue characteristic of a nonarchimedean local field

Let `F` be a nonarchimedean local field (of characteristic `0`, say).  Its residue field
`𝓀[F] = 𝒪[F] ⧸ 𝔪[F]` is finite (`IsNonarchimedeanLocalField.Finite`), hence of prime
characteristic: there is a rational prime `p` with `(p : 𝓀[F]) = 0`.  Equivalently `p` reduces to
`0` modulo the maximal ideal, i.e. `p` is a non-unit of the ring of integers `𝒪[F]`, and therefore
`valuation F p < 1`, i.e. `(p : F) <ᵥ 1`.

This is the residue characteristic of `F`: the rational prime that the valuation of `F` extends,
and hence the prime `p` for which the `p`-adic valuation has valuation `< 1`.  It is the basic
input to every statement of local class field theory that is phrased in terms of `p`.

## Main result

* `NK.LocalReciprocityLubinTate.Unramified.exists_prime_vlt_one`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Unramified

/-- **A rational prime lies in the maximal ideal.** For a nonarchimedean local field `F`, some
rational prime `p` satisfies `(p : 𝒪[F]) ∈ 𝔪[F]`; that is, `p` is a non-unit of the ring of
integers. -/
theorem exists_prime_mem_maximalIdeal (F : Type*) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ p : ℕ, Nat.Prime p ∧ ((p : ℕ) : ↥𝒪[F]) ∈ 𝓂[F] := by
  -- The residue field is finite (an instance of `IsNonarchimedeanLocalField`), hence its
  -- characteristic is prime.
  refine ⟨ringChar 𝓀[F], CharP.prime_ringChar 𝓀[F], ?_⟩
  -- A natural number vanishes in the residue field iff it lies in the maximal ideal.
  have hz : ((ringChar 𝓀[F] : ℕ) : 𝓀[F]) = 0 := CharP.cast_eq_zero 𝓀[F] (ringChar 𝓀[F])
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast (IsLocalRing.residue ↥𝒪[F])]
  exact hz

/-- **The residue characteristic of a nonarchimedean local field.** If `F` is a nonarchimedean
local field then some rational prime `p` has `(p : F) <ᵥ 1`, i.e. the valuation of `p` is `< 1`:
`p` is a non-unit of the ring of integers. -/
theorem exists_prime_vlt_one (F : Type*) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ p : ℕ, Nat.Prime p ∧ ((p : F) <ᵥ 1) := by
  obtain ⟨p, hp, hmem⟩ := exists_prime_mem_maximalIdeal F
  refine ⟨p, hp, ?_⟩
  -- Membership in the maximal ideal says exactly that the element is a non-unit of `𝒪[F]`,
  -- and an element of the ring of integers is a non-unit iff its valuation is `< 1`.
  have hnu : ¬ IsUnit ((p : ℕ) : ↥𝒪[F]) :=
    mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal ((p : ℕ) : ↥𝒪[F])).mp hmem)
  have hlt : (ValuativeRel.valuation F) ((↑((p : ℕ) : ↥𝒪[F])) : F) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := ValuativeRel.valuation F)).mp hnu
  rw [Valuation.vlt_one_iff (v := ValuativeRel.valuation F)]
  simpa using hlt

end NK.LocalReciprocityLubinTate.Unramified
