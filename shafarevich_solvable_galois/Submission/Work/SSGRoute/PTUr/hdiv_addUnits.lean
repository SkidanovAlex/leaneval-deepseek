import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
