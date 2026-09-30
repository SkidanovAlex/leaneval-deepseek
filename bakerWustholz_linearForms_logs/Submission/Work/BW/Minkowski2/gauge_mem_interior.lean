import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Minkowski functional and the interior of a dilated body

For `K ⊆ ℝᵈ` convex with `0 ∈ interior K` and `a > 0`, a point `z` lies in the interior of the
dilation `a • K` exactly when its Minkowski functional `gauge K z` is smaller than `a`.

This is the bridge between the successive-minimum bodies `succMinBody Λ K j • K` (which are
analysed in terms of `interior` in `Work.BW.Minkowski2.succMinBody_interior`) and the flag
hypothesis `gauge K z < λ` used in the aligned form of Minkowski's second theorem.
-/

namespace Work.BW.Minkowski2

open MeasureTheory
open scoped Pointwise

/-- `z` lies in the interior of `a • K` if and only if `gauge K z < a`. -/
theorem mem_interior_smulSet_iff_gauge_lt {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (h0 : (0 : Fin d → ℝ) ∈ interior K) {a : ℝ} (ha : 0 < a) (z : Fin d → ℝ) :
    z ∈ interior (Work.BW.smulSet a K) ↔ gauge K z < a := by
  have hnhds : K ∈ nhds (0 : Fin d → ℝ) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds h0) interior_subset
  have hnhds' : (a • K) ∈ nhds (0 : Fin d → ℝ) := by
    have h := (smul_mem_nhds_smul_iff₀ (c := a) (s := K) (x := (0 : Fin d → ℝ)) ha.ne').mpr hnhds
    rwa [smul_zero] at h
  rw [Work.BW.smulSet_eq]
  rw [show z ∈ interior (a • K) ↔ gauge (a • K) z < 1 from
    (gauge_lt_one_iff_mem_interior (Convex.smul hKc a) hnhds').symm]
  rw [gauge_smul_left_of_nonneg (s := K) (a := a) ha.le]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [inv_mul_lt_iff₀ ha, mul_one]

end Work.BW.Minkowski2
