import Mathlib
import Submission.Work.InnermostDisk.Defs

/-!
# Round spheres are embedded spheres

`Work.InnermostDisk.IsEmbeddedSphere S` records that `S` is the image of the unit sphere
under an injective continuous map.  Here we observe that the metric sphere `Metric.sphere c r`
of positive radius `r` in `ℝ³` has this property: the dilation-and-translation
`x ↦ c + r • x` restricts to a continuous bijection of the unit sphere onto it.

This is the trivial half of the sentence "Pardon works with PL spheres; this predicate only
records the topological shape": a round sphere is an embedded sphere.
-/

open Set Metric
open LeanEval.KnotTheory.PardonDistortion

namespace Work.InnermostDisk

/-- The map `x ↦ c + r • x` (for `r > 0`) sends the unit sphere of `ℝ³` onto the sphere of
radius `r` centred at `c`. -/
theorem range_add_smul_sphere (c : R3) {r : ℝ} (hr : 0 < r) :
    Set.range (fun x : Metric.sphere (0 : R3) 1 => c + r • (x : R3)) = Metric.sphere c r := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp only [Metric.mem_sphere, dist_eq_norm]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    have hx : ‖(x : R3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using x.2
    rw [hx, mul_one]
  · intro hy
    rw [Metric.mem_sphere, dist_eq_norm] at hy
    refine ⟨⟨r⁻¹ • (y - c), ?_⟩, ?_⟩
    · simp only [Metric.mem_sphere, dist_eq_norm, sub_zero]
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le, hy, inv_mul_cancel₀ (ne_of_gt hr)]
    · simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
      abel

/-- The map `x ↦ c + r • x` is injective on the unit sphere when `r ≠ 0`. -/
theorem injective_add_smul_sphere (c : R3) {r : ℝ} (hr : 0 < r) :
    Function.Injective
      (fun x : Metric.sphere (0 : R3) 1 => c + r • (x : R3)) := by
  intro x y h
  have h' : r • (x : R3) = r • (y : R3) := by
    simpa using add_left_cancel h
  exact Subtype.ext (smul_right_injective _ (ne_of_gt hr) h')

/-- **A round sphere is an embedded sphere.** -/
theorem isEmbeddedSphere_sphere (c : LeanEval.KnotTheory.PardonDistortion.R3) {r : ℝ}
    (hr : 0 < r) : Work.InnermostDisk.IsEmbeddedSphere (Metric.sphere c r) := by
  refine ⟨{ toFun := fun x : Metric.sphere (0 : R3) 1 => c + r • (x : R3)
            continuous_toFun := continuous_const.add (continuous_subtype_val.const_smul r) },
    injective_add_smul_sphere c hr, range_add_smul_sphere c hr⟩

end Work.InnermostDisk
