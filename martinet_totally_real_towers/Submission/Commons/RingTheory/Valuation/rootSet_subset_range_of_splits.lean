import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.Valuation

/-- If a polynomial `h` over a field `F` splits (as a product of linear factors and
constants over `F`), then every root of `h` in any `F`-algebra `L` which is a domain
already lies in the image of the structure map `F → L`. -/
theorem rootSet_subset_range_of_splits {F L : Type*} [Field F] [Field L] [Algebra F L] {h : Polynomial F} (hh : h.Splits) : ∀ x ∈ h.rootSet L, ∃ a : F, algebraMap F L a = x := by
  intro x hx
  rw [Polynomial.mem_rootSet'] at hx
  obtain ⟨hmap0, haeval⟩ := hx
  have h0 : h ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.map_zero] at hmap0
    exact hmap0 rfl
  exact hh.mem_range_of_isRoot h0
    (by rw [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]; exact haeval)

end Commons.RingTheory.Valuation