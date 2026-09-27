import Mathlib
import Submission.Work.Mostow.geomFiniteDefs

/-! # Area C1 (geomFinite) — basic `busemann` / `horoball` analysis

The Busemann function `busemann ξ u = log (tpart u − ⟪u,ξ⟫)` at a boundary point `ξ ∈ Sph n`
has strictly positive argument, hence is continuous, and the horoballs are open. -/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- `tpart` is positive. -/
lemma tpart_pos (u : E n) : 0 < tpart u := by
  rw [tpart]; exact Real.sqrt_pos.2 (by positivity)

/-- `‖u‖ < tpart u`. -/
lemma norm_lt_tpart_geomFiniteBusemann (u : E n) : ‖u‖ < tpart u := by
  have ht : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by rw [tpart, Real.sq_sqrt (by positivity)]
  have h1 : 0 ≤ ‖u‖ := norm_nonneg u
  have h2 : 0 ≤ tpart u := le_of_lt (tpart_pos u)
  nlinarith [ht, sq_nonneg ‖u‖, h1, h2]

/-- For `ξ` on the boundary sphere the argument of the logarithm defining `busemann ξ ·`
is strictly positive. -/
lemma tpart_sub_inner_pos (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    0 < tpart u - inner ℝ u ξ := by
  have hnorm : ‖ξ‖ = 1 := by
    have := hξ
    simp only [Sph, Metric.mem_sphere, dist_eq_norm] at this
    simpa using this
  have h1 : inner ℝ u ξ ≤ ‖u‖ * ‖ξ‖ := real_inner_le_norm u ξ
  rw [hnorm, mul_one] at h1
  have h2 : ‖u‖ < tpart u := norm_lt_tpart_geomFiniteBusemann u
  linarith

/-- The Busemann function at a boundary point is continuous. -/
lemma busemann_continuous (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun u : E n => busemann ξ u) := by
  have hf : Continuous (fun v : E n => tpart v - inner ℝ v ξ) := by
    apply Continuous.sub
    · change Continuous (fun v : E n => Real.sqrt (1 + ‖v‖ ^ 2)); fun_prop
    · fun_prop
  have hne : ∀ v : E n, tpart v - inner ℝ v ξ ≠ 0 :=
    fun v => ne_of_gt (tpart_sub_inner_pos ξ hξ v)
  change Continuous (fun v : E n => Real.log (tpart v - inner ℝ v ξ))
  exact hf.log hne

/-- Horoballs at a boundary point are open. -/
lemma isOpen_horoball (ξ : E n) (hξ : ξ ∈ Sph n) (t : ℝ) : IsOpen (horoball ξ t) :=
  isOpen_lt (busemann_continuous ξ hξ) (continuous_const : Continuous (fun _ : E n => t))

/-- `busemann ξ 0 = 0`. -/
lemma busemann_zero (ξ : E n) : busemann ξ (0 : E n) = 0 := by
  simp [busemann, tpart]

end

end Work.Mostow
