import Mathlib
import ChallengeDeps
import Submission.Work.Interfaces.Basic
import Submission.Work.Param.Basic
import Submission.Work.Normal.Basic
import Submission.Work.Param.vitali
import Submission.Work.Param.false_of_critical_orbit_tendsto

/-!
# PARAM: the main cardioid boundary is not in the interior of `M`

For `‖l‖ = 1` the parameter `cOfLam l = l/2 - l²/4` lies on the boundary of the main cardioid.
This file assembles the proof that it is not in the interior of the Mandelbrot set: if a whole
disc around `cOfLam l` were contained in `M`, then (writing `t` for the parameter of the cardioid,
`cOfLam t` for the corresponding `c`) the critical orbits `t ↦ (Tc (cOfLam t))^[n] 0` would be
locally bounded, hence normal; on the attracting side `‖t‖ < 1` they converge to the continued
fixed point `t/2`, and Montel + the identity theorem (`Work.Param.vitali`) propagate this to the
whole disc; on the repelling side `‖t‖ > 1` a repelling fixed point can only be a limit of an
orbit which eventually equals it, and Baire + a degree count finish the contradiction.
-/

namespace Work.Param

open MandelDim Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- The `n`-th iterate of the critical point `0` of `Tc (cOfLam t)`, as a function of the
parameter `t` of the cardioid. -/
def gCrit (n : ℕ) (t : ℂ) : ℂ := (Tc (cOfLam t))^[n] 0

/-- `cOfLam` is entire. -/
theorem differentiable_cOfLam : Differentiable ℂ cOfLam := by
  have h : cOfLam = fun t : ℂ => t / 2 - t ^ 2 / 4 := by
    funext t; simp only [cOfLam]
  rw [h]
  exact (differentiable_id.div_const 2).sub ((differentiable_id.pow 2).div_const 4)

/-- `gCrit n` is a polynomial in `t`, hence entire. -/
theorem differentiable_gCrit (n : ℕ) : Differentiable ℂ (gCrit n) := by
  induction n with
  | zero =>
    have h0 : gCrit 0 = fun _ : ℂ => 0 := by
      funext t; simp only [gCrit, Function.iterate_zero_apply]
    rw [h0]; exact differentiable_const (0 : ℂ)
  | succ n ih =>
    have h : gCrit (n + 1) = fun t => (gCrit n t) ^ 2 + cOfLam t := by
      funext t
      simp only [gCrit, Function.iterate_succ_apply', Tc]
    rw [h]
    exact (ih.pow 2).add differentiable_cOfLam

/-- The functional equation of `gCrit` as a recursion. -/
theorem gCrit_succ (n : ℕ) : gCrit (n + 1) = fun t => (gCrit n t) ^ 2 + cOfLam t := by
  funext t
  simp only [gCrit, Function.iterate_succ_apply', Tc]

/-- The critical orbit is the `Q t`-orbit of `-t/2`, shifted by `t/2`. -/
theorem gCrit_eq (n : ℕ) (t : ℂ) : gCrit n t = (Q t)^[n] (-(t / 2)) + t / 2 :=
  Tc_cOfLam_iterate_zero t n

/-- On the attracting side the critical orbit converges to the continued fixed point. -/
theorem tendsto_gCrit (hA : ∀ l : ℂ, ‖l‖ < 1 →
      Tendsto (fun n : ℕ => (Q l)^[n] (-(l / 2))) atTop (𝓝 0))
    {t : ℂ} (ht : ‖t‖ < 1) : Tendsto (fun n : ℕ => gCrit n t) atTop (𝓝 (t / 2)) := by
  have h := hA t ht
  rw [show (fun n : ℕ => gCrit n t) = fun n : ℕ => (Q t)^[n] (-(t / 2)) + t / 2 from
    funext fun n => gCrit_eq n t]
  simpa using h.add_const (t / 2)

/-- If the whole disc of parameters maps into `M`, the critical-orbit family is locally bounded
by `2` (MSET). -/
theorem isLocallyBoundedOn_gCrit (hM : MsetStatement) {l : ℂ} {δ : ℝ}
    (hsub : ∀ t ∈ Metric.ball l δ, cOfLam t ∈ Mandelbrot) :
    Work.Normal.IsLocallyBoundedOn (Set.range gCrit) (Metric.ball l δ) := by
  intro K hK _hKc
  exact ⟨2, fun f hf t ht => by
    obtain ⟨n, rfl⟩ := hf
    exact hM.2.2.1 (cOfLam t) (hsub t (hK ht)) n⟩

/-- The attracting region `{t ∈ ball l δ | ‖t‖ < 1}` is open. -/
theorem isOpen_attracting (l : ℂ) (δ : ℝ) :
    IsOpen {t : ℂ | t ∈ Metric.ball l δ ∧ ‖t‖ < 1} :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_norm continuous_const)

/-- For `‖l‖ = 1` and `δ > 0` the attracting region is nonempty. -/
theorem nonempty_attracting {l : ℂ} (hl : ‖l‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ({t : ℂ | t ∈ Metric.ball l δ ∧ ‖t‖ < 1}).Nonempty := by
  set ρ : ℝ := min δ 1 / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρδ : ρ < δ := by
    rw [hρ]; have := min_le_left δ 1; linarith
  have hρ1 : ρ ≤ 1 / 2 := by
    rw [hρ]; have := min_le_right δ 1; linarith
  refine ⟨((1 - ρ : ℝ) : ℂ) * l, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm,
      show ((1 - ρ : ℝ) : ℂ) * l - l = ((-ρ : ℝ) : ℂ) * l by push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hρpos, hl, mul_one]
    exact hρδ
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hl, mul_one,
      abs_of_pos (by linarith : (0:ℝ) < 1 - ρ)]
    linarith

/-- For `‖l‖ = 1` and `δ > 0` the repelling region `{t ∈ ball l δ | 1 < ‖t‖}` is open and
nonempty. -/
theorem isOpen_repelling (l : ℂ) (δ : ℝ) :
    IsOpen {t : ℂ | t ∈ Metric.ball l δ ∧ 1 < ‖t‖} :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)

theorem nonempty_repelling {l : ℂ} (hl : ‖l‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ({t : ℂ | t ∈ Metric.ball l δ ∧ 1 < ‖t‖}).Nonempty := by
  set ρ : ℝ := min δ 1 / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρδ : ρ < δ := by
    rw [hρ]; have := min_le_left δ 1; linarith
  have hρ1 : ρ ≤ 1 / 2 := by
    rw [hρ]; have := min_le_right δ 1; linarith
  refine ⟨((1 + ρ : ℝ) : ℂ) * l, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm,
      show ((1 + ρ : ℝ) : ℂ) * l - l = ((ρ : ℝ) : ℂ) * l by push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, hl, mul_one]
    exact hρδ
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hl, mul_one,
      abs_of_pos (by linarith : (0:ℝ) < 1 + ρ)]
    linarith

/-- **The main cardioid boundary is not in the interior of `M`.**  If `‖l‖ = 1` and (Lemma A, the
attracting case) `(Q t)^[n] (-(t/2)) → 0` for every `‖t‖ < 1`, then `cOfLam l ∉ interior M`. -/
theorem not_mem_interior_of_unit (hM : MsetStatement)
    (hA : ∀ l : ℂ, ‖l‖ < 1 → Tendsto (fun n : ℕ => (Q l)^[n] (-(l / 2))) atTop (𝓝 0))
    {l : ℂ} (hl : ‖l‖ = 1) : cOfLam l ∉ interior Mandelbrot := by
  intro hmem
  rw [mem_interior_iff_mem_nhds] at hmem
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.continuousAt_iff.mp (differentiable_cOfLam.continuous.continuousAt) ε hε
  have hsub : ∀ t ∈ Metric.ball l δ, cOfLam t ∈ Mandelbrot := fun t ht =>
    hεsub (hδsub (Metric.mem_ball.mp ht))
  have htot : ∀ t ∈ Metric.ball l δ, Tendsto (fun n : ℕ => gCrit n t) atTop (𝓝 (t / 2)) :=
    vitali Metric.isOpen_ball (convex_ball l δ).isPreconnected
      (fun n => (differentiable_gCrit n).differentiableOn)
      (isLocallyBoundedOn_gCrit hM hsub)
      (differentiable_id.div_const 2).differentiableOn
      (isOpen_attracting l δ) (nonempty_attracting hl hδ)
      (fun t ht => ht.1)
      (fun t ht => tendsto_gCrit hA ht.2)
  exact false_of_critical_orbit_tendsto hl hδ (fun t ht => htot t ht)

end

end Work.Param
