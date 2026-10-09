/-
# `p`-divisibility of `Ωˣ` for the coefficient Kummer sequence

The coefficient Kummer sequence of `PT/kummerSES.lean`,

`0 → Hom_ℤ(ℤ/p, C) → C →^{p·} C → 0`,

is available for a `p`-divisible discrete `G`-module `C`; its input `hdiv` is
`∀ c : C, ∃ c', p • c' = c`.  For the local application the coefficient module is
`C = Additive (Units Ω)` (`Ω` an algebraic closure of the number field `k`), and this file supplies
`hdiv` there — the first input of the α²-base-case wiring of the coprime-index case of local Tate
duality in degrees 0/2 (see `PTUr/NOTE_E7_h02_frontier_measured.md` §5).

The mathematics is elementary Kummer theory: an algebraically closed field is `n`-divisible for
every `n ≠ 0`, and a `p`-th root of a unit is again a unit.  The root lemma itself is the proved
`Work.SSGRoute.PT.units_root_exists_aux` (`PT/exists_addHom_extend_addUnits.lean`); what is added
here is the transport from `IsAlgClosure k Ω` to `IsAlgClosed Ω` and the additive spelling that
`kummerSES` consumes.
-/
import Mathlib
import Submission.Work.SSGRoute.PT.exists_addHom_extend_addUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **Every unit of an algebraic closure of a field has a `p`-th root.** -/
theorem units_pow_surjective {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (p : ℕ) (hp : p ≠ 0) : ∀ u : Units Ω, ∃ v : Units Ω, v ^ p = u := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  exact fun u => units_root_exists_aux p hp u

/-- **`Additive Ωˣ` is `p`-divisible**, in the exact shape of the hypothesis `hdiv` of
`Work.SSGRoute.PT.kummerSES` at `C = Additive (Units Ω)`. -/
theorem hdiv_addUnits {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (p : ℕ) (hp : p ≠ 0) :
    ∀ c : Additive (Units Ω), ∃ c' : Additive (Units Ω), p • c' = c := by
  intro c
  obtain ⟨v, hv⟩ := units_pow_surjective (k := k) p hp (Additive.toMul c)
  refine ⟨Additive.ofMul v, Additive.toMul.injective ?_⟩
  simpa [toMul_nsmul] using hv

end Work.SSGRoute.PT
