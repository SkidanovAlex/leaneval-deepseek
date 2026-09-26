import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Core.torusMap_eq_iff

namespace Work.CoreTopology

/-- The standard `(1,1)`-curve on the standard torus of revolution is simple (injective on a
fundamental period): `t ↦ torusMap t t` with `t ∈ [0, 2π)`.  This is the missing simplicity
witness for the `(1,1)`-curve, needed by any innermost-disc datum whose boundary curve is
`Work.CoreTopology.standardCurve 1 1`. -/
theorem standardCurve_one_one_simple :
    Work.CoreTopology.IsSimple Work.CoreTopology.standard
      (Work.CoreTopology.standardCurve 1 1) := by
  intro t ht t' ht' h
  -- Both parameters lie in the fundamental period `[0, 2π)`.
  rw [Set.mem_Ico] at ht ht'
  -- The curve is `t ↦ torusMap t t`; identify the equality of points.
  have htmap : Work.Core.torusMap t t = Work.Core.torusMap t' t' := by
    simpa [Work.CoreTopology.standardCurve] using h
  -- `torusMap` is injective modulo the two periods: `t = t' + k·2π`.
  obtain ⟨⟨k, hk⟩, _⟩ := (Work.Core.torusMap_eq_iff t t t' t').mp htmap
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- The difference `k·2π = t - t'` lies strictly between `-2π` and `2π`.
  have hlt : (k : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [ht.2, ht'.1]
  have hgt : -(2 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by linarith [ht.1, ht'.2]
  have hklt : (k : ℝ) < 1 := by nlinarith
  have hkgt : (-1 : ℝ) < k := by nlinarith
  -- Hence the integer `k` vanishes and `t = t'`.
  have hk0 : k = 0 := by
    have h1 : k < 1 := by exact_mod_cast hklt
    have h2 : (-1 : ℤ) < k := by exact_mod_cast hkgt
    omega
  rw [hk0] at hk
  simp at hk
  exact hk

end Work.CoreTopology
