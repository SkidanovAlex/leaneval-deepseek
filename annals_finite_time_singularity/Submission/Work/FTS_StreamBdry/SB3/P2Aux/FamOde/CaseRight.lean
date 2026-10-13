import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.Ode
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.exists_anchor_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.CaseRight` — the first-order bound on the right half `[π/4, π/2)`

The right half of `Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved`.  Writing
`δ = π/2 - θ`, the mean-value anchor `P2Aux.exists_anchor_right` at scale `a = δ²` gives
`ξ ∈ (π/2 - δ²/2, π/2 - δ²/4)` with `|F' ξ| ≤ 8K₀/δ²`, whence `|W ξ| ≤ (δ²/2)³·8K₀/δ² = K₀δ⁴`
(as `m ≤ cos³`); `W` is Lipschitz with constant `≤ (A/2)δ² + Cδ³` on `[θ,ξ]` and
`m(θ) ≥ 2δ³/π³`, giving `|F' θ| ≤ (π³/2)(K₀ + A/2 + Cπ/4)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde

theorem case_right {F Hz : ℝ → ℝ} {K₀ A C θ : ℝ} (hK₀ : 0 ≤ K₀) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hu : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ F x)
    (hode : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv F) (Hz x - coco x * deriv F x) x)
    (hub : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), |F x| ≤ K₀)
    (hH : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), |Hz x| ≤ A / Real.sin (2 * x) + C)
    (hθle : Real.pi / 4 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    |deriv F θ| ≤ Real.pi ^ 3 / 2 * (K₀ + A / 2 + C * Real.pi / 4) := by
  set M : ℝ := K₀ + A / 2 + C * Real.pi / 4 with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    have h2 : 0 ≤ A / 2 := by linarith
    have h3 : 0 ≤ C * (Real.pi / 4) := mul_nonneg hC (by positivity)
    linarith
  have hWderiv : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun x' => wfn x' * deriv F x') (wfn x * Hz x) x :=
    fun x hx => hasDerivAt_W hx (hode x hx)
  have hδ0 : 0 < Real.pi / 2 - θ := by linarith
  have hδle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have hpi2 : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
  set a : ℝ := (Real.pi / 2 - θ) ^ 2 with ha
  have ha0 : 0 < a := by rw [ha]; exact pow_pos hδ0 2
  have hapi : a < Real.pi / 2 := by
    rw [ha]
    have h1 : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 4) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hδ0) hδle 2
    have h2 : (Real.pi / 4) ^ 2 < Real.pi / 2 := by
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    linarith
  have hδa0 : 0 < Real.pi / 2 - a := by linarith
  obtain ⟨ξ, hξmem, hξb⟩ :=
    Work.FTS_StreamBdry.SB3.P2Aux.exists_anchor_right hK₀ hδa0 (by linarith) hu hub
      (k := 4) (by norm_num)
  have haeq : Real.pi / 2 - (Real.pi / 2 - a) = a := by ring
  rw [haeq] at hξmem hξb
  have hξ0 : 0 < ξ := by
    have h1 : (0 : ℝ) < Real.pi / 2 - 2 * a / 4 := by linarith [hapi, Real.pi_pos]
    linarith [hξmem.1]
  have hξpi : ξ < Real.pi / 2 := by
    have h1 : Real.pi / 2 - a / 4 < Real.pi / 2 := by linarith [ha0]
    linarith [hξmem.2]
  have hθξ : θ < ξ := by
    have h3 : θ < Real.pi / 2 - 2 * a / 4 := by
      rw [ha]
      nlinarith [hδ0, hδle, hpi2]
    linarith [hξmem.1]
  -- `|W ξ| ≤ K₀ δ⁴`
  have hwξnn : 0 ≤ wfn ξ := wfn_nonneg_of_mem ⟨hξ0, hξpi⟩
  have hcosnn : 0 ≤ Real.cos ξ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hξ0], le_of_lt hξpi⟩
  have hWξ : |wfn ξ * deriv F ξ| ≤ K₀ * (Real.pi / 2 - θ) ^ 4 := by
    have h1 : |wfn ξ * deriv F ξ| = wfn ξ * |deriv F ξ| := by
      rw [abs_mul, abs_of_nonneg hwξnn]
    have hcosξ : Real.cos ξ = Real.sin (Real.pi / 2 - ξ) := by
      conv_lhs => rw [show ξ = Real.pi / 2 - (Real.pi / 2 - ξ) from by ring]
      rw [Real.cos_pi_div_two_sub]
    have hsξnn : 0 ≤ Real.sin (Real.pi / 2 - ξ) := by rw [← hcosξ]; exact hcosnn
    have h2 : wfn ξ ≤ Real.cos ξ ^ 3 := by
      rw [wfn]
      calc Real.sin ξ ^ 2 * Real.cos ξ ^ 3 ≤ 1 * Real.cos ξ ^ 3 :=
            mul_le_mul_of_nonneg_right (Real.sin_sq_le_one ξ) (pow_nonneg hcosnn 3)
        _ = Real.cos ξ ^ 3 := by ring
    have h3 : Real.cos ξ ^ 3 ≤ (a / 2) ^ 3 := by
      rw [hcosξ]
      have h4 : Real.pi / 2 - ξ ≤ a / 2 := by linarith [hξmem.1]
      exact pow_le_pow_left₀ hsξnn (le_trans (Real.sin_le (by linarith)) h4) 3
    have h4 : 0 ≤ 2 * K₀ * 4 / a := by positivity
    have h5 : (a / 2) ^ 3 * (2 * K₀ * 4 / a) = K₀ * (Real.pi / 2 - θ) ^ 4 := by
      rw [ha]
      field_simp
      try ring
    calc |wfn ξ * deriv F ξ| = wfn ξ * |deriv F ξ| := h1
      _ ≤ wfn ξ * (2 * K₀ * 4 / a) := mul_le_mul_of_nonneg_left hξb hwξnn
      _ ≤ (a / 2) ^ 3 * (2 * K₀ * 4 / a) :=
            mul_le_mul_of_nonneg_right (le_trans h2 h3) h4
      _ = K₀ * (Real.pi / 2 - θ) ^ 4 := h5
  -- Lipschitz comparison on `[θ, ξ]`
  have hcontW : ContinuousOn (fun x => wfn x * deriv F x) (Icc θ ξ) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le (by linarith [Real.pi_pos, hθle]) hx.1, lt_of_le_of_lt hx.2 hξpi⟩
    exact (hWderiv x hx').continuousAt.continuousWithinAt
  have hdiffW : DifferentiableOn ℝ (fun x => wfn x * deriv F x) (Ioo θ ξ) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans (by linarith [Real.pi_pos, hθle]) hx.1, lt_trans hx.2 hξpi⟩
    exact (hWderiv x hx').differentiableAt.differentiableWithinAt
  have hbndW : ∀ x ∈ Ioo θ ξ,
      |deriv (fun x => wfn x * deriv F x) x|
        ≤ A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3 := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans (by linarith [Real.pi_pos, hθle]) hx.1, lt_trans hx.2 hξpi⟩
    rw [(hWderiv x hx').deriv]
    exact le_trans (abs_wfn_mul_le hx' (hH x hx'))
      (phfn_le_right hA hC (le_of_lt (lt_trans (by linarith [Real.pi_pos, hθle]) hx.1))
        (le_of_lt hx.1) (le_trans (le_of_lt hx.2) (le_of_lt hξpi)))
  have hlip := abs_sub_le_mul_of_deriv_le (le_of_lt hθξ) hcontW hdiffW hbndW
  have hlip' : |wfn θ * deriv F θ - wfn ξ * deriv F ξ|
      ≤ (A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3) * (ξ - θ) := by
    rw [abs_sub_comm]
    exact hlip
  have htri : |wfn θ * deriv F θ|
      ≤ |wfn ξ * deriv F ξ| + |wfn θ * deriv F θ - wfn ξ * deriv F ξ| := by
    have h := abs_sub_abs_le_abs_sub (wfn θ * deriv F θ) (wfn ξ * deriv F ξ)
    linarith
  have hcoef0 : 0 ≤ A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3 :=
    add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg hC (pow_nonneg (by linarith) 3))
  have hmain : |wfn θ * deriv F θ| ≤ (Real.pi / 2 - θ) ^ 3 * M := by
    have hstep : (A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3) * (ξ - θ)
        ≤ (A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3) * (Real.pi / 2 - θ) :=
      mul_le_mul_of_nonneg_left (by linarith) hcoef0
    have hquad : K₀ * (Real.pi / 2 - θ) ^ 4
          + (A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3) * (Real.pi / 2 - θ)
        = (Real.pi / 2 - θ) ^ 3 * (K₀ * (Real.pi / 2 - θ) + A / 2 + C * (Real.pi / 2 - θ)) := by
      ring
    have hlast : (Real.pi / 2 - θ) ^ 3
          * (K₀ * (Real.pi / 2 - θ) + A / 2 + C * (Real.pi / 2 - θ))
        ≤ (Real.pi / 2 - θ) ^ 3 * M := by
      rw [hM]
      have h1 : K₀ * (Real.pi / 2 - θ) ≤ K₀ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [hδle, hpi2]) hK₀
      have h2 : C * (Real.pi / 2 - θ) ≤ C * (Real.pi / 4) :=
        mul_le_mul_of_nonneg_left hδle hC
      have h3 : 0 ≤ (Real.pi / 2 - θ) ^ 3 := pow_nonneg (by linarith) 3
      have h4 : K₀ * (Real.pi / 2 - θ) + A / 2 + C * (Real.pi / 2 - θ)
          ≤ K₀ + A / 2 + C * Real.pi / 4 := by linarith
      exact mul_le_mul_of_nonneg_left h4 h3
    calc |wfn θ * deriv F θ|
        ≤ |wfn ξ * deriv F ξ|
          + (A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3) * (ξ - θ) := by
          linarith [htri, hlip']
      _ ≤ K₀ * (Real.pi / 2 - θ) ^ 4
          + (A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3)
            * (Real.pi / 2 - θ) := by linarith [hstep, hWξ]
      _ = (Real.pi / 2 - θ) ^ 3
          * (K₀ * (Real.pi / 2 - θ) + A / 2 + C * (Real.pi / 2 - θ)) := hquad
      _ ≤ (Real.pi / 2 - θ) ^ 3 * M := hlast
  -- divide by `wfn θ`
  have hposw : 0 < wfn θ := wfn_pos_of_mem ⟨by linarith [Real.pi_pos, hθle], hθ1⟩
  have hge : 2 / Real.pi ^ 3 * (Real.pi / 2 - θ) ^ 3 ≤ wfn θ := wfn_ge_right hθle hθ1
  have hc0 : 0 < 2 / Real.pi ^ 3 := by positivity
  have habs : |deriv F θ| = |wfn θ * deriv F θ| / wfn θ := by
    rw [abs_mul, abs_of_pos hposw, mul_div_cancel_left₀ _ (ne_of_gt hposw)]
  rw [habs]
  have hs1 : |wfn θ * deriv F θ| / wfn θ ≤ ((Real.pi / 2 - θ) ^ 3 * M) / wfn θ :=
    div_le_div_of_nonneg_right hmain (le_of_lt hposw)
  have hs2 : ((Real.pi / 2 - θ) ^ 3 * M) / wfn θ
      ≤ ((Real.pi / 2 - θ) ^ 3 * M) / (2 / Real.pi ^ 3 * (Real.pi / 2 - θ) ^ 3) :=
    div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (by linarith) 3) hMnn)
      (mul_pos hc0 (pow_pos hδ0 3)) hge
  have hs3 : ((Real.pi / 2 - θ) ^ 3 * M) / (2 / Real.pi ^ 3 * (Real.pi / 2 - θ) ^ 3)
      = Real.pi ^ 3 / 2 * M := by
    have hd : (Real.pi / 2 - θ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hδ0)
    have h1 : ((Real.pi / 2 - θ) ^ 3 * M) / (2 / Real.pi ^ 3 * (Real.pi / 2 - θ) ^ 3)
        = M / (2 / Real.pi ^ 3) := by
      rw [mul_comm ((Real.pi / 2 - θ) ^ 3) M, mul_div_mul_right _ _ hd]
    have h2 : M / (2 / Real.pi ^ 3) = Real.pi ^ 3 / 2 * M := by
      rw [div_eq_mul_inv, inv_div]
      ring
    rw [h1, h2]
  rw [hs3] at hs2
  linarith [hs1, hs2]

end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
