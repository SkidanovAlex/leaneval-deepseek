import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- If `z` is algebraic over `K` but does not lie in the image of `K` (i.e. `z ∉ ⊥` as an
intermediate field), then the simple extension `K⟮z⟯` has degree at least `2` over `K`.

Indeed `[K⟮z⟯ : K] = natDegree (minpoly K z)` (`IntermediateField.adjoin.finrank`), and
`2 ≤ natDegree (minpoly K z)` is equivalent to `z ∉ Set.range (algebraMap K Ω)`
(`minpoly.two_le_natDegree_iff`), which is exactly `z ∉ ⊥` (`IntermediateField.mem_bot`). -/
theorem two_le_finrank_adjoin_of_notMem_bot {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {z : Ω} (hz : IsAlgebraic K z) (hzbot : z ∉ (⊥ : IntermediateField K Ω)) :
    2 ≤ Module.finrank K ↥(IntermediateField.adjoin K ({z} : Set Ω)) := by
  have hzi : IsIntegral K z := isAlgebraic_iff_isIntegral.mp hz
  rw [IntermediateField.adjoin.finrank hzi]
  exact (minpoly.two_le_natDegree_iff hzi).mpr (by
    rwa [IntermediateField.mem_bot] at hzbot)

end Work.MotV5
