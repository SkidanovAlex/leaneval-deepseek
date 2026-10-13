/-
# `Work.CoreResiduals.BiotSavart.continuousAt_bsDerivCLM_param`

Continuity of the *parametrised* `x`-derivative of the Biot–Savart field,

`(x,t) ↦ bsDerivCLM (ω(·,t)) ρ x`,

at `(x₀,t₀)`, for a spacetime vorticity `ω` that is Hölder in `x` with a constant uniform on the
time window, jointly continuous at `(x₀,t₀)` and continuous in `t` at `t₀` for every fixed `x`.

The proof peels off the singularity with a *fixed* centre `x₀`: it splits the defining integral
over `B(0,ρ)` into the parts over `B(0,ρ) ∩ B(x₀,Δ)` and `B(0,ρ) \ B(x₀,Δ)`
(`integral_split`).  On the first part the per-slice estimate `norm_setIntegral_le_inner` bounds
the integral by `4C(4π/c)(3Δ/2)^c`, uniformly in `x ∈ B(x₀,Δ/2)` and in `t`; the second part is
continuous at `(x₀,t₀)` by dominated convergence (`continuousAt_bsIntegrand_outer`); and the
algebraic shape term `(4π/3) • crossL (ω x t)` is continuous at `(x₀,t₀)` by joint continuity of
`ω`.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsIntegrand_param
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsIntegrand_outer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- **Continuity of the parametrised `x`-derivative of the Biot–Savart field.**

For a spacetime vorticity `ω` that is `c`-Hölder in `x` with a constant `C ≥ 0` uniform over the
time window `|t - t₀| < δ`, jointly continuous at `(x₀,t₀)` and continuous in `t` at `t₀` for every
fixed `x`, the map `(x,t) ↦ bsDerivCLM (ω(·,t)) ρ x` is continuous at `(x₀,t₀)`.
-/
theorem continuousAt_bsDerivCLM_param {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ c C ρ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ t : ℝ, |t - t₀| < δ →
      ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ C * ‖a - b‖ ^ c)
    (hjoint : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀))
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      Work.CoreResiduals.BiotSavart.bsDerivCLM (fun y => ω y q.2) ρ q.1) (x₀, t₀) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  -- The modulus of the inner piece tends to `0` as `Δ → 0⁺`.
  have hlim : ContinuousAt (fun Δ : ℝ => 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c) 0 := by
    have hlin : ContinuousAt (fun Δ : ℝ => 3 * Δ / 2) 0 := by fun_prop
    have hrpow : ContinuousAt (fun t : ℝ => t ^ c) (3 * 0 / 2) := by
      simpa using Real.continuousAt_rpow_const (0 : ℝ) c (Or.inr hc.le)
    have h1 : ContinuousAt (fun Δ : ℝ => (3 * Δ / 2) ^ c) 0 :=
      (ContinuousAt.comp (x := (0 : ℝ)) (f := fun Δ : ℝ => 3 * Δ / 2)
        (g := fun t : ℝ => t ^ c) hrpow hlin)
    exact h1.const_mul _
  obtain ⟨r, hrpos, hr⟩ := Metric.continuousAt_iff.mp hlim (ε / 4) hε4
  set Δ : ℝ := min 1 (r / 2) with hΔdef
  have hΔpos : 0 < Δ := lt_min one_pos (by linarith)
  have hΔle1 : Δ ≤ 1 := min_le_left _ _
  have hΔle2 : Δ ≤ 2 := by linarith
  have hLnn : 0 ≤ 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hΔsmall : 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c < ε / 4 := by
    have hdist : dist Δ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hΔpos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h0 : 4 * C * (4 * Real.pi / c) * (3 * 0 / 2) ^ c = 0 := by
      rw [show (3 * 0 / 2 : ℝ) = 0 from by norm_num, Real.zero_rpow hc.ne']
      ring
    have h := hr hdist
    rw [Real.dist_eq, h0, sub_zero, abs_of_nonneg hLnn] at h
    exact h
  -- The outer piece is continuous at `(x₀,t₀)`.
  have hOutCont := continuousAt_bsIntegrand_outer (ω := ω) (ρ := ρ) (Δ := Δ)
    hδ hc hC hhold hjoint htcont hΔpos hΔle2
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.continuousAt_iff.mp hOutCont (ε / 4) hε4
  -- The algebraic shape term is continuous at `(x₀,t₀)`.
  have hShapeCont : ContinuousAt
      (fun q : Work.LWP.R3 × ℝ => (4 * Real.pi / 3) • crossL (ω q.1 q.2)) (x₀, t₀) :=
    (continuous_crossL.continuousAt.comp hjoint).const_smul (4 * Real.pi / 3)
  obtain ⟨r₃, hr₃pos, hr₃⟩ := Metric.continuousAt_iff.mp hShapeCont (ε / 4) hε4
  refine ⟨min (min (Δ / 2) δ) (min r₂ r₃), ?_, fun q hq => ?_⟩
  · exact lt_min (lt_min (by linarith) hδ) (lt_min hr₂pos hr₃pos)
  · have hd1 : dist q.1 x₀ ≤ dist q (x₀, t₀) := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd2 : dist q.2 t₀ ≤ dist q (x₀, t₀) := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hmin1 : min (min (Δ / 2) δ) (min r₂ r₃) ≤ min (Δ / 2) δ := min_le_left _ _
    have hmin2 : min (min (Δ / 2) δ) (min r₂ r₃) ≤ min r₂ r₃ := min_le_right _ _
    have hxq : ‖q.1 - x₀‖ ≤ Δ / 2 := by
      have h1 : dist q.1 x₀ < Δ / 2 :=
        lt_of_le_of_lt hd1 (lt_of_lt_of_le hq (le_trans hmin1 (min_le_left _ _)))
      rw [dist_eq_norm] at h1
      exact le_of_lt h1
    have hwq : |q.2 - t₀| < δ := by
      have h1 : dist q.2 t₀ < δ :=
        lt_of_le_of_lt hd2 (lt_of_lt_of_le hq (le_trans hmin1 (min_le_right _ _)))
      rwa [Real.dist_eq] at h1
    have hqr₂ : dist q (x₀, t₀) < r₂ := lt_of_lt_of_le hq (le_trans hmin2 (min_le_left _ _))
    have hqr₃ : dist q (x₀, t₀) < r₃ := lt_of_lt_of_le hq (le_trans hmin2 (min_le_right _ _))
    have htcont0 : |t₀ - t₀| < δ := by rw [sub_self, abs_zero]; exact hδ
    have hx0 : ‖x₀ - x₀‖ ≤ Δ / 2 := by rw [sub_self, norm_zero]; positivity
    -- Split the defining integral at the fixed centre `x₀` at both points.
    have hsplit_q : bsDerivCLM (fun y => ω y q.2) ρ q.1
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y q.2) q.1 a)
          + ((∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y q.2) q.1 a)
            + (4 * Real.pi / 3) • crossL (ω q.1 q.2)) := by
      show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand (fun y => ω y q.2) q.1 a)
            + (4 * Real.pi / 3) • crossL (ω q.1 q.2) = _
      rw [integral_split (C := C) hc hC (hhold q.2 hwq) x₀ hΔpos hΔle2 hxq]
      abel
    have hsplit_q0 : bsDerivCLM (fun y => ω y t₀) ρ x₀
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y t₀) x₀ a)
          + ((∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y t₀) x₀ a)
            + (4 * Real.pi / 3) • crossL (ω x₀ t₀)) := by
      show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand (fun y => ω y t₀) x₀ a)
            + (4 * Real.pi / 3) • crossL (ω x₀ t₀) = _
      rw [integral_split (C := C) hc hC (hhold t₀ htcont0) x₀ hΔpos hΔle2 hx0]
      abel
    -- The two inner pieces are small, uniformly in `(x,t)`.
    have hIq_lt : ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y q.2) q.1 a‖ < ε / 4 :=
      lt_of_le_of_lt (norm_setIntegral_le_inner (C := C) (c := c) (ρ := ρ) hc hC
        (hhold q.2 hwq) x₀ hΔpos hxq) hΔsmall
    have hIq0_lt : ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y t₀) x₀ a‖ < ε / 4 :=
      lt_of_le_of_lt (norm_setIntegral_le_inner (C := C) (c := c) (ρ := ρ) (x := x₀) hc hC
        (hhold t₀ htcont0) x₀ hΔpos hx0) hΔsmall
    have hA : ‖(∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y q.2) q.1 a)
        - (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y t₀) x₀ a)‖ ≤ _
        := norm_sub_le _ _
    have hB : ‖(∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y q.2) q.1 a)
        - (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y t₀) x₀ a)‖ < ε / 4 := by
      have h := hr₂ hqr₂
      rw [dist_eq_norm] at h
      simpa using h
    have hC' : ‖(4 * Real.pi / 3) • crossL (ω q.1 q.2)
        - (4 * Real.pi / 3) • crossL (ω x₀ t₀)‖ < ε / 4 := by
      have h := hr₃ hqr₃
      rw [dist_eq_norm] at h
      simpa using h
    change dist (bsDerivCLM (fun y => ω y q.2) ρ q.1)
        (bsDerivCLM (fun y => ω y t₀) ρ x₀) < ε
    rw [hsplit_q, hsplit_q0]
    have htri : ∀ (a1 a2 b1 b2 c1 c2 : Work.LWP.R3 →L[ℝ] Work.LWP.R3),
        dist (a1 + (b1 + c1)) (a2 + (b2 + c2))
          ≤ ‖a1 - a2‖ + ‖b1 - b2‖ + ‖c1 - c2‖ := by
      intro a1 a2 b1 b2 c1 c2
      rw [dist_eq_norm]
      have h : (a1 + (b1 + c1)) - (a2 + (b2 + c2))
          = (a1 - a2) + (b1 - b2) + (c1 - c2) := by abel
      rw [h]
      calc ‖(a1 - a2) + (b1 - b2) + (c1 - c2)‖
          ≤ ‖(a1 - a2) + (b1 - b2)‖ + ‖c1 - c2‖ := norm_add_le _ _
        _ ≤ (‖a1 - a2‖ + ‖b1 - b2‖) + ‖c1 - c2‖ := by
            gcongr; exact norm_add_le _ _
    refine lt_of_le_of_lt (htri _ _ _ _ _ _) ?_
    linarith [hA, hIq_lt, hIq0_lt, hB, hC']

end Work.CoreResiduals.BiotSavart
