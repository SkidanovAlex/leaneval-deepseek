import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Set Metric

namespace Commons.Topology.Connected

/-- The complement of a closed ball in `ℂ` is preconnected.

For `r < 0` the set is all of `ℂ`; in general it is the image of the
(augmented) annulus `(r, ∞) ×ˢ S¹` under `(t, u) ↦ c + t • u`: every point
`z ≠ c` with `r < ‖z - c‖` is `c + ‖z - c‖ • ((z - c)/‖z - c‖)`, and the
remaining point `z = c` occurs only when `r < 0`, where it is the image of
`(0, 1)`.  The domain is a product of a preconnected interval and the
preconnected unit circle, and the map is continuous. -/
theorem isPreconnected_compl_closedBall (c : ℂ) (r : ℝ) :
    IsPreconnected {z : ℂ | r < ‖z - c‖} := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have himage : (fun p : ℝ × ℂ => c + p.1 • p.2) '' (Ioi r ×ˢ sphere (0 : ℂ) 1)
      = {z : ℂ | r < ‖z - c‖} := by
    ext z
    constructor
    · rintro ⟨p, ⟨ht, hu⟩, rfl⟩
      have hu1 : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      have hnorm : ‖(c + p.1 • p.2) - c‖ = |p.1| := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu1, mul_one]
      change r < ‖(c + p.1 • p.2) - c‖
      rw [hnorm]
      exact lt_of_lt_of_le ht (le_abs_self p.1)
    · intro hz
      change r < ‖z - c‖ at hz
      by_cases hc : z = c
      · refine ⟨(0, 1), ⟨?_, ?_⟩, ?_⟩
        · change r < (0 : ℝ); simpa [hc] using hz
        · exact mem_sphere_zero_iff_norm.mpr (by simp)
        · change c + (0 : ℝ) • (1 : ℂ) = z; rw [hc]; simp
      · have hd : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hc)
        refine ⟨(‖z - c‖, ‖z - c‖⁻¹ • (z - c)), ⟨?_, ?_⟩, ?_⟩
        · change r < ‖z - c‖; exact hz
        · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_pos hd, inv_mul_cancel₀ hd.ne']
        · change c + ‖z - c‖ • (‖z - c‖⁻¹ • (z - c)) = z
          rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul, add_sub_cancel]
  rw [← himage]
  exact IsPreconnected.image (isPreconnected_Ioi.prod (isPreconnected_sphere hrank 0 1)) _
    ((by fun_prop : Continuous (fun p : ℝ × ℂ => c + p.1 • p.2)).continuousOn)

end Commons.Topology.Connected