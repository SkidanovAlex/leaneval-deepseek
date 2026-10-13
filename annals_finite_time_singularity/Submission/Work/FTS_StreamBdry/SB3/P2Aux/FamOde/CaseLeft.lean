import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.Ode
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.exists_anchor_left

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.CaseLeft` — the first-order bound on the left half `(0, π/4]`

The left half of `Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved`: with the
mean-value anchor `P2Aux.exists_anchor_left` at scale `θ²` one finds `ξ ∈ (θ²/8, θ²/4)` with
`|F' ξ| ≤ 16K₀/θ²`; since `W = m·F'` is Lipschitz with constant `≤ (A/2)θ + Cθ²` on `[ξ,θ]`
and `m(θ) ≥ θ²/(2π²)`, this gives `|F' θ| ≤ 2π²(K₀ + A/2 + Cπ/4)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde

theorem case_left {F Hz : ℝ → ℝ} {K₀ A C θ : ℝ} (hK₀ : 0 ≤ K₀) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hu : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ F x)
    (hode : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv F) (Hz x - coco x * deriv F x) x)
    (hub : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), |F x| ≤ K₀)
    (hH : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), |Hz x| ≤ A / Real.sin (2 * x) + C)
    (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 4) :
    |deriv F θ| ≤ 2 * Real.pi ^ 2 * (K₀ + A / 2 + C * Real.pi / 4) := by
  set M : ℝ := K₀ + A / 2 + C * Real.pi / 4 with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    have h2 : 0 ≤ A / 2 := by linarith
    have h3 : 0 ≤ C * (Real.pi / 4) := mul_nonneg hC (by positivity)
    linarith
  have hWderiv : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun x' => wfn x' * deriv F x') (wfn x * Hz x) x :=
    fun x hx => hasDerivAt_W hx (hode x hx)
  have ha0 : 0 < θ ^ 2 := pow_pos hθ0 2
  have hapi : θ ^ 2 < Real.pi / 2 := by
    have h1 : θ ^ 2 ≤ (Real.pi / 4) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hθ0) hθle 2
    have h2 : (Real.pi / 4) ^ 2 < Real.pi / 2 := by
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    linarith
  obtain ⟨ξ, hξmem, hξb⟩ :=
    Work.FTS_StreamBdry.SB3.P2Aux.exists_anchor_left hK₀ ha0 hapi hu hub (k := 4) (by norm_num)
  have hξ0 : 0 < ξ := by
    have : (0 : ℝ) < θ ^ 2 / (2 * 4) := by positivity
    linarith [hξmem.1]
  have hξθ : ξ < θ := by
    have h2 : θ ^ 2 / 4 < θ := by nlinarith [hθle, hθ0, Real.pi_lt_four]
    linarith [hξmem.2, h2]
  have hξpi : ξ < Real.pi / 2 := lt_trans hξθ (by linarith [hθle, Real.pi_pos])
  have hWξ : |wfn ξ * deriv F ξ| ≤ K₀ * θ ^ 2 := by
    have h1 : |wfn ξ * deriv F ξ| = wfn ξ * |deriv F ξ| := by
      rw [abs_mul, abs_of_nonneg (wfn_nonneg_of_mem ⟨hξ0, hξpi⟩)]
    have h2 : wfn ξ ≤ ξ ^ 2 := wfn_le_sq ξ
    have h3 : ξ ^ 2 ≤ (θ ^ 2 / 4) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hξ0) (le_of_lt hξmem.2) 2
    have h4 : 0 ≤ 4 * K₀ * 4 / θ ^ 2 := by positivity
    have h5 : (θ ^ 2 / 4) ^ 2 * (4 * K₀ * 4 / θ ^ 2) = K₀ * θ ^ 2 := by
      field_simp
      try ring
    calc |wfn ξ * deriv F ξ| = wfn ξ * |deriv F ξ| := h1
      _ ≤ ξ ^ 2 * (4 * K₀ * 4 / θ ^ 2) := mul_le_mul h2 hξb (abs_nonneg _) (sq_nonneg ξ)
      _ ≤ (θ ^ 2 / 4) ^ 2 * (4 * K₀ * 4 / θ ^ 2) := mul_le_mul_of_nonneg_right h3 h4
      _ = K₀ * θ ^ 2 := h5
  -- Lipschitz comparison on `[ξ, θ]`
  have hcontW : ContinuousOn (fun x => wfn x * deriv F x) (Icc ξ θ) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le hξ0 hx.1, lt_of_le_of_lt hx.2 (by linarith [hθle, Real.pi_pos])⟩
    exact (hWderiv x hx').continuousAt.continuousWithinAt
  have hdiffW : DifferentiableOn ℝ (fun x => wfn x * deriv F x) (Ioo ξ θ) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans hξ0 hx.1, lt_trans hx.2 (by linarith [hθle, Real.pi_pos])⟩
    exact (hWderiv x hx').differentiableAt.differentiableWithinAt
  have hbndW : ∀ x ∈ Ioo ξ θ,
      |deriv (fun x => wfn x * deriv F x) x| ≤ A / 2 * θ + C * θ ^ 2 := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans hξ0 hx.1, lt_trans hx.2 (by linarith [hθle, Real.pi_pos])⟩
    rw [(hWderiv x hx').deriv]
    exact le_trans (abs_wfn_mul_le hx' (hH x hx'))
      (phfn_le_left hA hC (le_of_lt (lt_trans hξ0 hx.1)) (le_of_lt hx.2)
        (by linarith [hθle, Real.pi_pos]))
  have hlip := abs_sub_le_mul_of_deriv_le (le_of_lt hξθ) hcontW hdiffW hbndW
  have htri : |wfn θ * deriv F θ|
      ≤ |wfn ξ * deriv F ξ| + |wfn θ * deriv F θ - wfn ξ * deriv F ξ| := by
    have h := abs_sub_abs_le_abs_sub (wfn θ * deriv F θ) (wfn ξ * deriv F ξ)
    linarith
  have hcoef0 : 0 ≤ A / 2 * θ + C * θ ^ 2 := by
    have h1 : 0 ≤ A / 2 * θ := by positivity
    have h2 : 0 ≤ C * θ ^ 2 := by positivity
    linarith
  have hmain : |wfn θ * deriv F θ| ≤ θ ^ 2 * M := by
    have hstep : (A / 2 * θ + C * θ ^ 2) * (θ - ξ) ≤ (A / 2 * θ + C * θ ^ 2) * θ :=
      mul_le_mul_of_nonneg_left (by linarith) hcoef0
    have hquad : K₀ * θ ^ 2 + (A / 2 * θ + C * θ ^ 2) * θ
        = θ ^ 2 * (K₀ + A / 2 + C * θ) := by ring
    have hlast : θ ^ 2 * (K₀ + A / 2 + C * θ) ≤ θ ^ 2 * M := by
      rw [hM]
      have hC1 : C * θ ≤ C * (Real.pi / 4) := mul_le_mul_of_nonneg_left hθle hC
      have h4 : K₀ + A / 2 + C * θ ≤ K₀ + A / 2 + C * Real.pi / 4 := by linarith
      exact mul_le_mul_of_nonneg_left h4 (sq_nonneg θ)
    calc |wfn θ * deriv F θ|
        ≤ |wfn ξ * deriv F ξ| + (A / 2 * θ + C * θ ^ 2) * (θ - ξ) := by linarith
      _ ≤ K₀ * θ ^ 2 + (A / 2 * θ + C * θ ^ 2) * θ := by linarith [hstep, hWξ]
      _ = θ ^ 2 * (K₀ + A / 2 + C * θ) := hquad
      _ ≤ θ ^ 2 * M := hlast
  -- divide by `wfn θ`
  have hposw : 0 < wfn θ := wfn_pos_of_mem ⟨hθ0, by linarith [hθle, Real.pi_pos]⟩
  have hge : 1 / (2 * Real.pi ^ 2) * θ ^ 2 ≤ wfn θ := wfn_ge_left hθ0 hθle
  have hc0 : 0 < 1 / (2 * Real.pi ^ 2) := by positivity
  have habs : |deriv F θ| = |wfn θ * deriv F θ| / wfn θ := by
    rw [abs_mul, abs_of_pos hposw, mul_div_cancel_left₀ _ (ne_of_gt hposw)]
  rw [habs]
  have hs1 : |wfn θ * deriv F θ| / wfn θ ≤ (θ ^ 2 * M) / wfn θ :=
    div_le_div_of_nonneg_right hmain (le_of_lt hposw)
  have hs2 : (θ ^ 2 * M) / wfn θ ≤ (θ ^ 2 * M) / (1 / (2 * Real.pi ^ 2) * θ ^ 2) :=
    div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg θ) hMnn)
      (mul_pos hc0 (pow_pos hθ0 2)) hge
  have hs3 : (θ ^ 2 * M) / (1 / (2 * Real.pi ^ 2) * θ ^ 2) = 2 * Real.pi ^ 2 * M := by
    field_simp
    try ring
  rw [hs3] at hs2
  linarith [hs1, hs2]

end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
