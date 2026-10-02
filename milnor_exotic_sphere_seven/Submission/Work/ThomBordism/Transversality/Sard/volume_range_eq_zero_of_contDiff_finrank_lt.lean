import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.volume_eq_zero_of_dimH_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism.Transversality.Sard

/-- **The low-dimensional case of Sard's theorem.**  If `a < b` then the image of a `C¹` map
`f : ℝ^a → ℝ^b` is Lebesgue-null.

Indeed the Hausdorff dimension of `range f` is at most `finrank ℝ (ℝ^a) = a` (Mathlib's
`ContDiff.dimH_range_le`), hence strictly less than the ambient dimension `b`, and a set of
Hausdorff dimension `< b` in `ℝ^b` is Lebesgue-null
(`volume_eq_zero_of_dimH_lt`). -/
theorem volume_range_eq_zero_of_contDiff_finrank_lt {a b : ℕ} (hab : a < b)
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b)) (hf : ContDiff ℝ 1 f) :
    MeasureTheory.volume (Set.range f) = 0 := by
  apply volume_eq_zero_of_dimH_lt
  have h := hf.dimH_range_le
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin a)) = a := by simp
  rw [hfr] at h
  exact lt_of_le_of_lt h (by exact_mod_cast hab)

end Work.ThomBordism.Transversality.Sard
