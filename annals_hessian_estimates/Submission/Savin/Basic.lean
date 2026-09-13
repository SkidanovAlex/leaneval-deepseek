/-
# Foundations for Savin's small perturbation theorem (classical case)

Savin, *Small perturbation solutions for elliptic equations*, CPDE 32 (2007) 557--578.

* `hessCLM u x` -- the Hessian of `u` at `x` as a self-adjoint operator,
* `parab a y c` -- the *concave* paraboloid of opening `a` and vertex `y` used by Savin's sliding
  paraboloid argument.

The first and second derivatives of `parab` are proved in the commons
(`Commons.Analysis.Savin.fderiv_concave_paraboloid`, `...hessian_concave_paraboloid`).
-/
import Mathlib

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The Hessian of `u` at `x` as a self-adjoint operator on `ℝ⁴`, characterised by
`⟪hessCLM u x v, w⟫ = D²u(x)(v, w)`. -/
noncomputable def hessCLM (u : ℝ⁴ → ℝ) (x : ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x)

/-- Evaluation of the Hessian operator: `⟪hessCLM u x v, w⟫ = D²u(x)(v, w)`. -/
theorem inner_hessCLM (u : ℝ⁴ → ℝ) (x v w : ℝ⁴) :
    ⟪hessCLM u x v, w⟫ = fderiv ℝ (fderiv ℝ u) x v w := by
  unfold hessCLM
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]

/-- The Hessian of a `C²` function is symmetric. -/
theorem hessCLM_symm (u : ℝ⁴ → ℝ) {x : ℝ⁴} (hu : ContDiffAt ℝ 2 u x) (v w : ℝ⁴) :
    ⟪hessCLM u x v, w⟫ = ⟪hessCLM u x w, v⟫ := by
  have h : IsSymmSndFDerivAt ℝ u x := hu.isSymmSndFDerivAt (by simp)
  rw [inner_hessCLM, inner_hessCLM]
  exact h v w

/-- The concave paraboloid of opening `a` with vertex `y` and vertical offset `c`:
`x ↦ -(a/2)‖x - y‖² + c`.  This is the paraboloid which is *slid from below* in Savin's
Lemma 2.1; its Hessian is `-a • 1`. -/
noncomputable def parab (a : ℝ) (y : ℝ⁴) (c : ℝ) : ℝ⁴ → ℝ :=
  fun x => (-(a / 2)) * ‖x - y‖ ^ 2 + c

theorem parab_apply (a c : ℝ) (y x : ℝ⁴) :
    parab a y c x = (-(a / 2)) * ‖x - y‖ ^ 2 + c := rfl

theorem contDiff_parab (a c : ℝ) (y : ℝ⁴) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (parab a y c) := by
  unfold parab
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ⁴ => ‖x - y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ⁴ => (-(a / 2) : ℝ)) :=
    contDiff_const
  simpa using ((hc.mul h1).add contDiff_const)

end Submission
