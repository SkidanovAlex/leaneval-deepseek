import Mathlib
import Submission.Work.Diff.Dim2.Ambient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-!
# The ambient map lands in the unit sphere

`sphereAmb (r, z) = (sin r * z 0, sin r * z 1, cos r)` for `z ∈ ℝ²` with `‖z‖ = 1` has norm `1`:
its squared norm is `sin²r * (z₀² + z₁²) + cos²r = sin²r + cos²r = 1`.

The identification `EuclideanSpace ℝ (Fin 3) ≃ (Fin 3 → ℝ)` used in the definition of
`sphereAmb` is `PiLp.continuousLinearEquiv 2 ℝ` (i.e. `WithLp.toLp 2`), and the norm on
`EuclideanSpace` is computed componentwise by `EuclideanSpace.norm_sq_eq`.
-/

/-- Value of the `0`-th component of `sphereAmbComp`. -/
private lemma sphereAmbNorm_comp_zero (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (0 : Fin 3) (r, z) = Real.sin r * z.ofLp 0 := by
  rw [sphereAmbComp, Fin.cases_zero]

/-- Value of the `1`-st component of `sphereAmbComp`. -/
private lemma sphereAmbNorm_comp_one (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (1 : Fin 3) (r, z) = Real.sin r * z.ofLp 1 := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    Fin.cases_zero]

/-- Value of the `2`-nd component of `sphereAmbComp`. -/
private lemma sphereAmbNorm_comp_two (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (2 : Fin 3) (r, z) = Real.cos r := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

/-- `sphereAmb` unfolds to `WithLp.toLp 2` applied to the components. -/
private lemma sphereAmb_eq_toLp (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    sphereAmb (r, z) = WithLp.toLp 2 (fun i : Fin 3 => sphereAmbComp i (r, z)) := by
  rw [sphereAmb, EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply]

theorem sphereAmbNorm (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    ‖Work.Diff.Dim2.sphereAmb (r, z)‖ = 1 := by
  -- the squared components of `z` sum to `1`
  have hz2 : (z.ofLp 0) ^ 2 + (z.ofLp 1) ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq z
    rw [hz, Fin.sum_univ_two] at h
    simp only [Real.norm_eq_abs, sq_abs, one_pow] at h
    linarith
  have h0 := sphereAmbNorm_comp_zero r z
  have h1 := sphereAmbNorm_comp_one r z
  have h2 := sphereAmbNorm_comp_two r z
  -- the squared norm, computed componentwise
  have hsq : ‖sphereAmb (r, z)‖ ^ 2 = 1 := by
    rw [sphereAmb_eq_toLp, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    show ‖sphereAmbComp 0 (r, z)‖ ^ 2 + ‖sphereAmbComp 1 (r, z)‖ ^ 2 +
        ‖sphereAmbComp 2 (r, z)‖ ^ 2 = 1
    rw [h0, h1, h2]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [hz2, Real.sin_sq_add_cos_sq r]
  -- a nonnegative real whose square is `1` equals `1`
  have hsp := Real.sqrt_sq (norm_nonneg (sphereAmb (r, z)))
  rw [hsq, Real.sqrt_one] at hsp
  exact hsp.symm

end Work.Diff.Dim2
