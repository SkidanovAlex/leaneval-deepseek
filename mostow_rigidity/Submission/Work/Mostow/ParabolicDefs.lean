/-
Shared base module for the parabolic-fixed-point development
(`Work.Mostow.geomFiniteParabolicClass` and its delegated chapters).

It only re-exports the driver interfaces `Submission.Mostow.Interfaces` (together with
Mathlib) and opens the namespaces used by those interfaces, and records a few elementary
definitions/lemmas about them.
-/
import Mathlib
import Submission.Mostow.Interfaces

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

/-- The Busemann level `plev ξ u = tpart u - ⟪u,ξ⟫ = exp (busemann ξ u)`. (Local copy of the
content of `Work.Mostow.lev` from `QIDefs`, under a name that does not clash with it.) -/
def plev (ξ u : E n) : ℝ := tpart u - inner ℝ u ξ

theorem plev_pos (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) : 0 < plev ξ u := by
  have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have h2 : inner ℝ u ξ ≤ ‖u‖ * ‖ξ‖ := real_inner_le_norm u ξ
  have h3 : tpart u = Real.sqrt (1 + ‖u‖ ^ 2) := rfl
  have h4 : Real.sqrt (1 + ‖u‖ ^ 2) > ‖u‖ := by
    have : (1:ℝ) + ‖u‖ ^ 2 > ‖u‖ ^ 2 := by linarith
    calc Real.sqrt (1 + ‖u‖ ^ 2) > Real.sqrt (‖u‖ ^ 2) := Real.sqrt_lt_sqrt (by positivity) this
      _ = ‖u‖ := Real.sqrt_sq (norm_nonneg u)
  rw [plev, h3, h1] at *
  nlinarith [h2, h4, norm_nonneg u]

/-- `plev` is `exp` of the Busemann function. -/
theorem plev_eq_exp {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    plev ξ u = Real.exp (busemann ξ u) := by
  have h : 0 < plev ξ u := plev_pos ξ hξ u
  simp only [plev, busemann]
  exact (Real.exp_log h).symm

end

end Work.Mostow
