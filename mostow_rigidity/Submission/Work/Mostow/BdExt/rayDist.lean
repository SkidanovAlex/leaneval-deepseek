import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BaryBase

/-!
# The geodesic rays `ray ξ ·` are parametrised by hyperbolic arclength

For a boundary point `ξ ∈ Sph n` the ray `t ↦ ray ξ t = sinh t • ξ` is a genuine geodesic
issued from the chart origin `0`: hyperbolic arc length along it is exactly `t`.  Concretely,

* `hdist (ray ξ s) (ray ξ t) = |s - t|`, and
* `hdist 0 (ray ξ t) = t` for `t ≥ 0`,

which is the "unit speed" property used throughout the boundary-extension argument.

Both follow from the elementary hyperboloid computation
`cosh (hdist (ray ξ s) (ray ξ t)) = cosh (s - t)`, which is the addition theorem for `cosh`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- The hyperbolic law of cosines on the ray: for `ξ ∈ Sph n` the cosine of the hyperbolic
distance between `ray ξ s` and `ray ξ t` is `cosh (s - t)`. -/
theorem cosh_hdist_ray {n : ℕ} (ξ : E n) (hξ : ξ ∈ Sph n) (s t : ℝ) :
    tpart (ray ξ s) * tpart (ray ξ t) - inner ℝ (ray ξ s) (ray ξ t) = Real.cosh (s - t) := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  rw [ray, ray, tpart_sinh_smul ξ s hξn, tpart_sinh_smul ξ t hξn]
  rw [inner_smul_left, starRingEnd_apply, inner_smul_right, real_inner_self_eq_norm_sq, hξn]
  simp only [star_trivial, mul_one, pow_two]
  rw [Real.cosh_sub]

/-- The ray `ray ξ ·` is parametrised by hyperbolic arc length: the distance between two of its
points is the difference of the parameters. -/
theorem hdist_ray_ray {n : ℕ} (ξ : E n) (hξ : ξ ∈ Sph n) (s t : ℝ) :
    hdist (ray ξ s) (ray ξ t) = |s - t| := by
  rw [hdist, cosh_hdist_ray ξ hξ s t, ← Real.cosh_abs (s - t)]
  exact Real.arcosh_cosh (abs_nonneg _)

/-- The ray `ray ξ ·` is issued from the origin at unit speed: `hdist 0 (ray ξ t) = t` for `t ≥ 0`. -/
theorem hdist_zero_ray {n : ℕ} (ξ : E n) (hξ : ξ ∈ Sph n) (t : ℝ) (ht : 0 ≤ t) :
    hdist 0 (ray ξ t) = t := by
  have h0 : (0 : E n) = ray ξ 0 := by rw [ray, Real.sinh_zero, zero_smul]
  rw [h0, hdist_ray_ray ξ hξ 0 t, zero_sub, abs_neg, abs_of_nonneg ht]

theorem rayDist (n : ℕ) :
    (∀ (ξ : Submission.Mostow.E n) (s t : ℝ), ξ ∈ Submission.Mostow.Sph n →
        Submission.Mostow.hdist (Work.Mostow.BdExt.ray ξ s) (Work.Mostow.BdExt.ray ξ t) = |s - t|) ∧
    (∀ (ξ : Submission.Mostow.E n) (t : ℝ), ξ ∈ Submission.Mostow.Sph n → 0 ≤ t →
        Submission.Mostow.hdist 0 (Work.Mostow.BdExt.ray ξ t) = t) :=
  ⟨fun ξ s t hξ => hdist_ray_ray ξ hξ s t, fun ξ t hξ ht => hdist_zero_ray ξ hξ t ht⟩

end Work.Mostow.BdExt
