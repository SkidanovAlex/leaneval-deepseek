import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.ESL.detL_span_pair_sq

namespace Work.HP

/-- The determinant (covolume in its real span) of the rank-`2` lattice spanned by two
`ℤ`-linearly independent integer vectors `c, d` is the "wedge norm"
`wedgeNorm c d = √(‖c‖² ‖d‖² - ⟨c,d⟩²)`. -/
theorem detgam_span_pair_wedgeNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = wedgeNorm c d := by
  -- `detL` of the span is a square root, hence non-negative.
  have ha : 0 ≤ detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) := Real.sqrt_nonneg _
  -- Squared form, from the classical Gram determinant computation.
  have hsq : detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) ^ 2
      = eNorm c ^ 2 * eNorm d ^ 2 - (dotR (toR c) (toR d)) ^ 2 := by
    rw [ESL.detL_span_pair_sq c d h]
    congr 1
    simp only [dotR, toR, dotZ, Int.cast_sum, Int.cast_mul]
  calc detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))
      = √(detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) ^ 2) :=
        (Real.sqrt_sq ha).symm
    _ = √(eNorm c ^ 2 * eNorm d ^ 2 - (dotR (toR c) (toR d)) ^ 2) := by rw [hsq]
    _ = wedgeNorm c d := rfl

end Work.HP
