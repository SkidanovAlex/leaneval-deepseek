import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The ring of integers of a finite intermediate field lies in every finite place above `k`.**

Let `k` be a number field, `Ω / k` a field extension, `B` a valuation subring of `Ω` whose
restriction to `k` is proper (a finite place of `Ω` over `k`), and `M` a finite extension of `k`
inside `Ω`.  Then the image in `Ω` of every element of the ring of integers `𝓞 M` lies in `B`.

In fact no hypothesis on `B` is needed: by
`Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring` every valuation subring
of the number field `M` contains `𝓞 M`. -/
theorem ringOfIntegers_mem_of_isFinPlace_k (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (M : IntermediateField k Ω) [FiniteDimensional k M]
    (x : NumberField.RingOfIntegers ↥M) :
    algebraMap (NumberField.RingOfIntegers ↥M) Ω x ∈ B := by
  haveI : NumberField ↥M := NumberField.of_module_finite k ↥M
  have h1 := Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring
    (B.comap (algebraMap ↥M Ω)) x
  rw [ValuationSubring.mem_comap] at h1
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M Ω]
  exact h1

end Work.SSGRoute
