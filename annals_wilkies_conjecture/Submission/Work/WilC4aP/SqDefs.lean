/-
  Work.WilC4aP — vocabulary for the complex Puiseux theorem (square-free case).

  The root space `RootSpace P r R` is the set of pairs `(z, Y)` with `‖z‖ ≤ r`, `‖Y‖ ≤ R` and
  `Y` a root of the fibre `Pz P z`; it is the total space of the (degree `m`) covering of the
  punctured disk that carries the roots of `P`.  `rootProj` is its projection to the base.
-/
import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.analytic_bivariate_Pz_eval

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- The punctured disk of radius `r` in the base (the `z`-plane). -/
def puncDisk (r : ℝ) : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}

@[simp] lemma mem_puncDisk {r : ℝ} {z : ℂ} : z ∈ puncDisk r ↔ 0 < ‖z‖ ∧ ‖z‖ < r := Iff.rfl

/-- The **root space** over the closed disk of radius `r`: pairs `(z, Y)` with `‖z‖ ≤ r`,
`‖Y‖ ≤ R` and `Y` a root of the fibre `Pz P z`. -/
def RootSpace (P : Polynomial (ℂ → ℂ)) (r R : ℝ) : Set (ℂ × ℂ) :=
  (Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) R) ∩
    {q : ℂ × ℂ | (Pz P q.1).eval q.2 = 0}

/-- The projection of the root space onto the base. -/
def rootProj (P : Polynomial (ℂ → ℂ)) (r R : ℝ) : ↥(RootSpace P r R) → ℂ := fun q => q.1.1

@[simp] lemma rootProj_apply (P : Polynomial (ℂ → ℂ)) {r R : ℝ} (q : ↥(RootSpace P r R)) :
    rootProj P r R q = q.1.1 := rfl

lemma rootProj_bound (P : Polynomial (ℂ → ℂ)) {r R : ℝ} (q : ↥(RootSpace P r R)) :
    ‖q.1.1‖ ≤ r := by
  have h : q.1.1 ∈ Metric.closedBall (0 : ℂ) r := q.2.1.1
  simpa [Metric.mem_closedBall, dist_eq_norm] using h

lemma rootSnd_bound (P : Polynomial (ℂ → ℂ)) {r R : ℝ} (q : ↥(RootSpace P r R)) :
    ‖q.1.2‖ ≤ R := by
  have h : q.1.2 ∈ Metric.closedBall (0 : ℂ) R := q.2.1.2
  simpa [Metric.mem_closedBall, dist_eq_norm] using h

lemma rootEval_zero (P : Polynomial (ℂ → ℂ)) {r R : ℝ} (q : ↥(RootSpace P r R)) :
    (Pz P q.1.1).eval q.1.2 = 0 := q.2.2

/-- `(z, Y) ↦ (Pz P z).eval Y` is continuous at points where all coefficients are analytic. -/
lemma continuousAt_pzEval (P : Polynomial (ℂ → ℂ)) {z₀ : ℂ} (han : HolCoeffs P z₀) (Y : ℂ) :
    ContinuousAt (fun q : ℂ × ℂ => (Pz P q.1).eval q.2) (z₀, Y) :=
  (analytic_bivariate_Pz_eval P z₀ Y han).continuousAt

/-- The projection of the root space is continuous. -/
lemma continuous_rootProj (P : Polynomial (ℂ → ℂ)) (r R : ℝ) :
    Continuous (rootProj P r R) := continuous_subtype_val.fst

end Work.WilC4aP
