import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germCHelpers

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

/-- The successive differences of the stable germ `h` at the scales `u`, `λu`, `λ²u`
(`λ = eqLam a`) do not vanish for `u ≠ 0` close to `0`: `h(λu) ≠ h(u)` and `h(λ²u) ≠ h(λu)`.
This is the non-degeneracy that lets `Work.EQ.germC_apply_ne` write `germC a h u` and
`germC a h (λu)` as honest difference quotients, and that `Work.EQ.germC_step_algebra` needs as
`B - A ≠ 0`, `C - B ≠ 0`.  Proof: `h(w) = w · dslope h 0 w` with `dslope h 0 w → h'(0) = -1 ≠ 0`,
so `h(λu) - h(u) = u·(λ·dslope h 0 (λu) - dslope h 0 u)` and the bracket tends to `1 - λ ≠ 0`. -/
theorem germC_diff_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ → u ≠ 0 →
      h ((eqLam a : ℂ) * u) - h u ≠ 0 ∧
      h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u) ≠ 0 := by
  obtain ⟨hr, hAn, h0, hderiv, hreal, hFE⟩ := hh
  have hl0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hl1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hlne : (eqLam a : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hl0
  have hAn0 : AnalyticAt ℂ h 0 := hAn 0 (by simpa using hr)
  -- The bracket `F u = λ·dslope h 0 (λu) - dslope h 0 u` is continuous at `0` with value `1-λ ≠ 0`.
  have hFcont : ContinuousAt
      (fun u : ℂ => (eqLam a : ℂ) * dslope h 0 ((eqLam a : ℂ) * u) - dslope h 0 u) 0 := by
    have hc0 : ContinuousAt (dslope h 0) 0 := (analyticAt_dslope hAn0).continuousAt
    have hc0' : ContinuousAt (dslope h 0) ((eqLam a : ℂ) * 0) := by simpa using hc0
    have hlin : ContinuousAt (fun u : ℂ => (eqLam a : ℂ) * u) 0 :=
      continuousAt_id.const_mul (eqLam a : ℂ)
    have hcomp : ContinuousAt (fun u : ℂ => dslope h 0 ((eqLam a : ℂ) * u)) 0 := by
      have h := hc0'.comp hlin
      simpa [Function.comp_def] using h
    exact (continuousAt_const.mul hcomp).sub hc0
  have hF0 : (eqLam a : ℂ) * dslope h 0 ((eqLam a : ℂ) * 0) - dslope h 0 0
      = 1 - (eqLam a : ℂ) := by
    rw [mul_zero, dslope_same h 0, hderiv]
    ring
  have hF0ne : (eqLam a : ℂ) * dslope h 0 ((eqLam a : ℂ) * 0) - dslope h 0 0 ≠ 0 := by
    rw [hF0]
    intro hcon
    have hcast : (1 : ℝ) = eqLam a := by exact_mod_cast (sub_eq_zero.mp hcon)
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := exists_ball_of_eventually (hFcont.eventually_ne hF0ne)
  -- Exact factorisation `h(λv) - h v = v · F v`.
  have key : ∀ v : ℂ, h ((eqLam a : ℂ) * v) - h v
      = v * ((eqLam a : ℂ) * dslope h 0 ((eqLam a : ℂ) * v) - dslope h 0 v) := by
    intro v
    rw [← mul_dslope_eq (f := h) (v := (eqLam a : ℂ) * v) h0,
      ← mul_dslope_eq (f := h) (v := v) h0]
    ring
  refine ⟨δ, hδpos, ?_⟩
  intro u hu hu0
  have hun : ‖u‖ < δ := by
    have h := hu; rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h; exact h
  have hwmem : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact norm_mul_lt_of_lt hl0 hl1 hδpos hun
  have hwne : (eqLam a : ℂ) * u ≠ 0 := mul_ne_zero hlne hu0
  refine ⟨?_, ?_⟩
  · rw [key u]
    exact mul_ne_zero hu0 (hδ u hu)
  · rw [key ((eqLam a : ℂ) * u)]
    exact mul_ne_zero hwne (hδ ((eqLam a : ℂ) * u) hwmem)

end Work.EQ
