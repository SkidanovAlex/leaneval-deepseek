import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.norm_sq_cos_sin_smul

/-!
# The model (space-form of curvature 1) metric in geodesic polar coordinates

This file contains the algebraic core of the "model bound" route to Toponogov's hinge comparison:
the comparison of the Riemannian metric of `M` with the model metric
`dr² + sin²r dθ²` of the unit sphere, transported to `T_pM` by the polar-coordinate map
`(r, e) ↦ r • e`.

The scheme (see `Submission/Roadmap.lean` §28.4, route (M)) is the classical one:

* the pointwise Rauch bound (`ExpBound2.exists_expMap_mfderiv_norm_bound` for the normal part,
  Gauss's lemma for the radial part) gives, for `v ∈ T_pM` with `‖v‖` below the conjugate radius,
  `‖(d exp_p)_v x‖² ≤ ‖x_∥‖² + (sin r/r)² ‖x_⊥‖²`, `r = ‖v‖`;
* the model distance from the point at radius `r₁` and azimuth `e₁` to the point at radius `r₂` and
  azimuth `e₂` is `arccos (cos r₁ cos r₂ + sin r₁ sin r₂ cos θ)`, i.e. the spherical law of cosines
  (`Commons.Geometry.Sphere.modelDist_cos`).

The two ingredients in this file are

* `modelLenSq` and **`norm_sq_greatCircle`**: the model metric norm of a vector with radial
  component `r'` and orthogonal component of norm `s` at radius `r` is the Euclidean norm of the
  corresponding great-circle velocity `-(sin r · r') • N + (cos r · r') • e + sin r • f`;
* **`hasDerivAt_greatCircle`**: the derivative of the great-circle curve
  `u ↦ cos (r u) • N + sin (r u) • e u`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Submission.SphereCoord

/-- The squared **model metric** in geodesic polar coordinates, applied to a vector whose radial
component is `r'` and whose component orthogonal to the radial direction has norm `s`, at radius
`r`.  For curvature `1` this is the metric `dr² + sin²r dθ²`. -/
noncomputable def modelLenSq (r r' s : ℝ) : ℝ := r' ^ 2 + (Real.sin r) ^ 2 * s ^ 2

/-- **The model norm is the Euclidean norm of the corresponding great-circle velocity.**  If
`N, e, f` are orthonormal (`N, e` unit, pairwise orthogonal), then the norm of
`-(sin r · r') • N + (cos r · r') • e + sin r • f` is the model norm `√(r'² + sin²r ‖f‖²)`. -/
theorem norm_sq_greatCircle {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (N e f : F) (r r' : ℝ)
    (hN : norm N = 1) (hNe : inner ℝ N e = 0) (hNf : inner ℝ N f = 0)
    (he : norm e = 1) (hef : inner ℝ e f = 0) :
    norm (-(Real.sin r * r') • N + (Real.cos r * r') • e + Real.sin r • f) ^ 2
      = modelLenSq r r' (norm f) := by
  rw [modelLenSq]
  exact Commons.Analysis.InnerProductSpace.norm_sq_cos_sin_smul N e f r r' hN hNe hNf he hef

/-- **Derivative of the great-circle curve** `u ↦ cos (g u) • N + sin (g u) • e u`. -/
theorem hasDerivAt_greatCircle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : F} {g : ℝ → ℝ} {g' : ℝ} {e : ℝ → F} {e' : F} {u : ℝ}
    (hg : HasDerivAt g g' u) (he : HasDerivAt e e' u) :
    HasDerivAt (fun s : ℝ => Real.cos (g s) • N + Real.sin (g s) • e s)
      (-(Real.sin (g u) * g') • N + (Real.cos (g u) * g') • e u + Real.sin (g u) • e') u := by
  have h1 : HasDerivAt (fun s : ℝ => Real.cos (g s)) (-(Real.sin (g u)) * g') u := hg.cos
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (g s)) (Real.cos (g u) * g') u := hg.sin
  have h3 : HasDerivAt (fun s : ℝ => Real.cos (g s) • N) ((-(Real.sin (g u)) * g') • N) u :=
    h1.smul_const N
  have h4 : HasDerivAt (fun s : ℝ => Real.sin (g s) • e s)
      ((Real.cos (g u) * g') • e u + Real.sin (g u) • e') u := by
    have h := h2.smul he
    rw [show ((fun s : ℝ => Real.sin (g s)) • e) = fun s : ℝ => Real.sin (g s) • e s from rfl] at h
    rwa [show Real.sin (g u) • e' + (Real.cos (g u) * g') • e u
        = (Real.cos (g u) * g') • e u + Real.sin (g u) • e' from by rw [add_comm]] at h
  have h5 := h3.add h4
  have hval : (-(Real.sin (g u)) * g') • N
        + ((Real.cos (g u) * g') • e u + Real.sin (g u) • e')
      = (-(Real.sin (g u) * g') • N + (Real.cos (g u) * g') • e u + Real.sin (g u) • e') := by
    rw [neg_mul]
    module
  rw [hval] at h5
  exact h5

/-- The value of the great-circle derivative expressed through the model norm: for a unit-speed
great circle the squared speed is the model norm of the corresponding polar velocity. -/
theorem norm_sq_greatCircle_deriv {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {N e f : F} {r r' : ℝ}
    (hN : norm N = 1) (hNe : inner ℝ N e = 0) (hNf : inner ℝ N f = 0)
    (he : norm e = 1) (hef : inner ℝ e f = 0) :
    modelLenSq r r' (norm f)
      = norm (-(Real.sin r * r') • N + (Real.cos r * r') • e + Real.sin r • f) ^ 2 :=
  (norm_sq_greatCircle N e f r r' hN hNe hNf he hef).symm

end Submission.SphereCoord
