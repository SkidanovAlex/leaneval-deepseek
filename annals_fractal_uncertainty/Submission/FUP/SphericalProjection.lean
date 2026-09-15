import Submission.FUP.DyadicPartition
import Submission.Commons.MeasureTheory.Integral.interval_half_line_scaling

open MeasureTheory Metric
open scoped Real BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The weighted spherical projection of §4

Section 4 of the paper uses the weighted spherical projection

  `π_{S^{d-1}} f(v̂) = ∫_0^∞ f(t v̂) t^{-2} dt`

of a function on `ℝᵈ` (defined on unit vectors).  The weight `t^{-2}` is what makes the
translational derivative comparable to the rotational derivative (Lemma 4.1 of the paper).

Here we define `sphProj f v = ∫_{t>0} f(t v) t^{-2} dt` for an arbitrary vector `v`; it is
homogeneous of degree one in `v` (`sphProj_smul`), so that on unit vectors it is the projection
of the paper.
-/

/-- The weighted spherical projection: `π f v = ∫_{t>0} f(t v) t^{-2} dt`. -/
noncomputable def sphProj (f : ℝᵈ → ℝ) (v : ℝᵈ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), f (t • v) * (t ^ 2)⁻¹

/-- `sphProj` is homogeneous of degree one. -/
lemma sphProj_smul (f : ℝᵈ → ℝ) (v : ℝᵈ) {c : ℝ} (hc : 0 < c) :
    sphProj f (c • v) = c * sphProj f v :=
  Commons.MeasureTheory.Integral.interval_half_line_scaling f v hc

lemma sphProj_congr {f g : ℝᵈ → ℝ} (h : ∀ x, f x = g x) (v : ℝᵈ) :
    sphProj f v = sphProj g v := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [h]

/-- For a radial function the projection is an integral against `t^{-2}` along the ray. -/
lemma sphProj_radial (ψ : ℝ → ℝ) (v : ℝᵈ) :
    sphProj (fun x : ℝᵈ => ψ ‖x‖) v
      = ∫ t in Set.Ioi (0 : ℝ), ψ (t * ‖v‖) * (t ^ 2)⁻¹ := by
  rw [sphProj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Set.mem_Ioi.mp ht)]

end Submission.FUP
