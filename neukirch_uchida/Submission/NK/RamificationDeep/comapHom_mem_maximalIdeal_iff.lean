import Mathlib
import Submission.NK.RamificationDeep.MonoDefs

namespace NK.RamificationDeep

/-- For a valuation subring `A` of `L` and a subfield `E ⊆ L`, the natural inclusion
`𝔬 = A ∩ E → A` (namely `comapHom A`) is a local homomorphism of local rings: an element of
`𝔬` is a nonunit in `𝔬` exactly when its image in `A` is a nonunit in `A`.

This is the defining property of the maximal ideals of the two valuation rings: both are cut out by
the same valuation, restricted to `E`. -/
theorem comapHom_mem_maximalIdeal_iff {E L : Type*} [Field E] [Field L] [Algebra E L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (x : ↥(A.comap (algebraMap E L))) :
    NK.RamificationDeep.comapHom A x ∈ IsLocalRing.maximalIdeal A ↔
      x ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap E L)) := by
  -- Both maximal ideals are described by membership of the coerced element in the
  -- corresponding `nonunits` set, and these agree because the valuation of `A` restricted
  -- to `E` is the valuation of `A ∩ E`.
  have key : ∀ y : E, algebraMap E L y ∈ A.nonunits ↔
      y ∈ (A.comap (algebraMap E L)).nonunits := by
    intro y
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
    constructor
    · rintro (h | h)
      · left; exact (algebraMap E L).injective (by simpa using h)
      · right; rw [ValuationSubring.mem_comap]; simpa only [map_inv₀] using h
    · rintro (h | h)
      · left; rw [h, map_zero]
      · right; rw [ValuationSubring.mem_comap] at h; simpa only [map_inv₀] using h
  rw [← ValuationSubring.coe_mem_nonunits_iff (A := A),
      ← ValuationSubring.coe_mem_nonunits_iff (A := A.comap (algebraMap E L))]
  rw [NK.RamificationDeep.comapHom_apply]
  exact key _

end NK.RamificationDeep
