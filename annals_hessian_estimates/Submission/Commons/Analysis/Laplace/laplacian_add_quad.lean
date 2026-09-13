import Mathlib
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq

namespace Commons.Analysis.Laplace

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
/-- The Laplacian of a function perturbed by a negative multiple of a squared distance to a
point `c`:
`Δ (h + δ * (R ^ 2 - ‖· - c‖ ^ 2)) = Δ h - 2 * n * δ` in dimension `n`.
This is the standard "Laplacian of a paraboloid" computation, used to add a strictly concave
quadratic correction to a function. -/
theorem laplacian_add_quad {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {c x : EuclideanSpace ℝ (Fin n)} (hh : ContDiffAt ℝ 2 h x) (δ R : ℝ) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) x
      = Laplacian.laplacian h x - 2 * (n : ℝ) * δ := by
  have hwcd : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => R ^ 2 - ‖y - c‖ ^ 2) x :=
    contDiffAt_const.sub (((contDiffAt_id (x := x)).sub contDiffAt_const).norm_sq ℝ)
  have hqcd : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => δ * (R ^ 2 - ‖y - c‖ ^ 2)) x :=
    ContDiffAt.const_smul δ hwcd
  -- Laplacian of `y ↦ R ^ 2 - ‖y - c‖ ^ 2`.
  have hlapw : Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => R ^ 2 - ‖y - c‖ ^ 2) x
      = -2 * (n : ℝ) := by
    have hsub := ContDiffAt.laplacian_sub (f₁ := fun _ : EuclideanSpace ℝ (Fin n) => R ^ 2)
      (f₂ := fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖ ^ 2) (x := x)
      contDiffAt_const (((contDiffAt_id (x := x)).sub contDiffAt_const).norm_sq ℝ)
    have h2 : Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖ ^ 2) x
        = 2 * (n : ℝ) := by
      rw [Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq c]
      simp [finrank_euclideanSpace]
    have h1 : Laplacian.laplacian (fun _ : EuclideanSpace ℝ (Fin n) => R ^ 2) x = 0 := by simp
    change Laplacian.laplacian ((fun _ : EuclideanSpace ℝ (Fin n) => R ^ 2)
      - (fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖ ^ 2)) x = -2 * (n : ℝ)
    rw [hsub, h1, h2]
    ring
  -- Laplacian of the scaled correction term.
  have hqval : Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => δ * (R ^ 2 - ‖y - c‖ ^ 2)) x
      = -2 * (n : ℝ) * δ := by
    have hsmul : (fun y : EuclideanSpace ℝ (Fin n) => δ * (R ^ 2 - ‖y - c‖ ^ 2))
        = δ • (fun y : EuclideanSpace ℝ (Fin n) => R ^ 2 - ‖y - c‖ ^ 2) := rfl
    rw [hsmul, InnerProductSpace.laplacian_smul (𝕜 := ℝ) δ hwcd, hlapw]
    simp [smul_eq_mul]
    ring
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2))
      = h + (fun y : EuclideanSpace ℝ (Fin n) => δ * (R ^ 2 - ‖y - c‖ ^ 2)) from rfl,
    ContDiffAt.laplacian_add hh hqcd, hqval]
  ring

end Commons.Analysis.Laplace
