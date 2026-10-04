import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.rot_invariance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared glue for the assembly of `Work.Diff.L.flow_end_conn`

Small, elementary bridges that the assembly of `Work.Diff.L.flow_end_conn` (and its delegated
sub-lemmas) use:

* `conn_scalAlg_rmFrame_eq`: the scalar curvature traced in an orthonormal frame does not depend on
  the frame (`rot_invariance` + `onFrame_orthogonal_change` + `rmFrame_eq_rot`);
* `conn_abs_apply_le_sqrt_frobSq`: every curvature component is bounded by `√|R|²`;
* `conn_kappa_arith`: the elementary arithmetic converting the scalar-curvature bounds `ρ ≤ S ≤ SA`
  and `SA < (1+η)δ²ρ` into a pinching constant `κ` for `δ`-pinched curvature.
-/

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The scalar curvature `scalAlg (rmFrame g x e)` traced in an orthonormal frame does not depend on
the frame `e`: it equals `scalAt g x`. -/
theorem conn_scalAlg_rmFrame_eq (g : SMet I M) (hLC : LCSmooth I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    scalAlg (rmFrame g x e) = scalAt g x := by
  have he0 : IsONFrame g x (onFrame g x) := onFrame_isONFrame g x
  obtain ⟨A, hA, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change g x (onFrame g x) e he0 he
  rw [Work.Diff.GE.rmFrame_eq_rot hLC g x (onFrame g x) e A hAe,
    (Work.Diff.GE.rot_invariance A hA (rmFrame g x (onFrame g x))).1]
  rfl

/-- **The pinching arithmetic.**  For `n ≥ 2`, `δ > 0`, `ρ > 0`, `SA > 0` and
`SA < (1+η) δ² ρ`, the number `κ = (U/(1+η) + L)/2` with `L = δ ρ /(n(n-1))` and
`U = SA/(δ n(n-1))` satisfies `0 < κ < L` and `U < (1+η)κ`.  Since `δ`-pinching puts every
sectional curvature of a curvature tensor whose scalar curvature lies in `[ρ, SA]` into `[L, U]`,
this converts the data of a pinching set into a two-sided pinching constant. -/
theorem conn_kappa_arith {n : ℕ} (hn : 2 ≤ n) {δ ρ SA η : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hSA : 0 < SA) (hη : 0 < η) (hcond : SA < (1 + η) * δ ^ 2 * ρ) :
    0 < (SA / (δ * ((n : ℝ) * ((n : ℝ) - 1))) / (1 + η) + δ * ρ / ((n : ℝ) * ((n : ℝ) - 1))) / 2 ∧
    (SA / (δ * ((n : ℝ) * ((n : ℝ) - 1))) / (1 + η) + δ * ρ / ((n : ℝ) * ((n : ℝ) - 1))) / 2
        < δ * ρ / ((n : ℝ) * ((n : ℝ) - 1)) ∧
    SA / (δ * ((n : ℝ) * ((n : ℝ) - 1)))
      < (1 + η) * ((SA / (δ * ((n : ℝ) * ((n : ℝ) - 1))) / (1 + η)
          + δ * ρ / ((n : ℝ) * ((n : ℝ) - 1))) / 2) := by
  set D : ℝ := (n : ℝ) * ((n : ℝ) - 1) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hL : 0 < δ * ρ / D := div_pos (mul_pos hδ hρ) hD
  have hU : 0 < SA / (δ * D) := div_pos hSA (mul_pos hδ hD)
  have hη1 : 0 < 1 + η := by linarith
  have hUL : SA / (δ * D) < (1 + η) * (δ * ρ / D) := by
    rw [div_lt_iff₀ (mul_pos hδ hD)]
    have h2 : (1 + η) * (δ * ρ / D) * (δ * D) = (1 + η) * δ ^ 2 * ρ := by
      field_simp
    rw [h2]
    exact hcond
  have hkey : SA / (δ * D) / (1 + η) < δ * ρ / D := by
    rw [div_lt_iff₀ hη1]
    calc SA / (δ * D) < (1 + η) * (δ * ρ / D) := hUL
      _ = (δ * ρ / D) * (1 + η) := by ring
  refine ⟨?_, ?_, ?_⟩
  · have := div_pos hU hη1
    linarith
  · linarith
  · have hx : (1 + η) * (SA / (δ * D) / (1 + η)) = SA / (δ * D) := by
      field_simp
    nlinarith [hx, hUL, hU]

end Work.Diff.L
