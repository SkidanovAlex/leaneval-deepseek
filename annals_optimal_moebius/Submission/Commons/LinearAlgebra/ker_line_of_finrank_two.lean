import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# A nonzero linear map on a two-dimensional space with nonzero kernel has a
one-dimensional kernel

Let `K` be a field, `E` a finite-dimensional `K`-vector space of dimension
`2`, and `T : E →ₗ[K] F` (any codomain) with `T ≠ 0` and `ker T ≠ ⊥`.
Then the kernel of `T` is a line:

`∃ v : E, v ≠ 0 ∧ T.ker = Submodule.span K {v}`.

Proof: rank-nullity (`LinearMap.finrank_range_add_finrank_ker`) gives
`finrank (range T) + finrank (ker T) = 2`; `T ≠ 0` makes the range nonzero
so `finrank (range T) ≥ 1`, and `ker T ≠ ⊥` makes `finrank (ker T) ≥ 1`;
hence both are `1`.  A one-dimensional submodule equals the span of any of
its nonzero elements (`Submodule.finrank_eq_one`-style or
`Submodule.eq_of_le_of_finrank_eq` applied to `span {u} ≤ ker`).
-/

noncomputable section
namespace Commons.LinearAlgebra

/-- A nonzero map with nonzero kernel from a two-dimensional space has
one-dimensional kernel. -/
theorem ker_line_of_finrank_two {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F]
    {T : E →ₗ[K] F} (hfin : Module.finrank K E = 2)
    (hker : T.ker ≠ ⊥) (hT : T ≠ 0) :
    ∃ v : E, v ≠ 0 ∧ T.ker = Submodule.span K {v} := by
  -- rank-nullity on `T`
  have hsum : Module.finrank K (LinearMap.range T) + Module.finrank K T.ker = 2 := by
    simpa [hfin] using T.finrank_range_add_finrank_ker
  -- `T ≠ 0` gives a nonzero range
  have hrange_ne_bot : LinearMap.range T ≠ ⊥ := by
    intro h
    exact hT (LinearMap.range_eq_bot.mp h)
  have hrge : 1 ≤ Module.finrank K (LinearMap.range T) :=
    (Submodule.one_le_finrank_iff).mpr hrange_ne_bot
  -- `ker T ≠ ⊥` gives kernel dimension at least one
  have hker_ge : 1 ≤ Module.finrank K T.ker :=
    (Submodule.one_le_finrank_iff).mpr hker
  -- both bounds force the kernel to have dimension exactly one
  have hkerfin : Module.finrank K T.ker = 1 := by
    omega
  -- take a nonzero vector in the kernel; a one-dimensional submodule is the
  -- span of any of its nonzero elements
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hvne, ?_⟩
  exact eq_span_singleton_of_mem_of_finrank_eq_one hkerfin hvmem hvne

end Commons.LinearAlgebra