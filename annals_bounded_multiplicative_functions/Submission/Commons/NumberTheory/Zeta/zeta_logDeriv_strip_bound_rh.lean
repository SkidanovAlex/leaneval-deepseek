import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_ne_zero_of_rh_gt_half
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.NumberTheory.Zeta.zeta1_growth_ball
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Metric Set
open scoped Topology Real BigOperators
noncomputable section
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Zeta

/-! zeta₁ has no zeros on Re > 1/2 under RH -/
lemma zeta1_ne_zero_of_rh_gt_half (h : RiemannHypothesis) {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · intro hz
    have hzζ : riemannZeta s = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hs1, hz]
      simp
    exact zeta_ne_zero_of_rh_gt_half h hs hzζ

/-! ‖ζ'/ζ (s)‖ ≤ ‖ζ₁'/ζ₁ (s)‖ + 1/‖s−1‖ -/
lemma zeta_logDeriv_norm_le (s : ℂ) (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by
  have hid : deriv riemannZeta s / riemannZeta s =
      - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hs, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs]
    field_simp [hz1, sub_ne_zero.mpr hs]
  rw [hid]
  calc
    ‖- (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
        ‖- (s - 1)⁻¹‖ + ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ := norm_add_le _ _
    _ = ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by
      have hnorm : ‖- (s - 1)⁻¹‖ = 1 / ‖s - 1‖ := by
        simp [norm_inv]
      simp [hnorm, add_comm]

/-! ===== real arithmetic helpers ===== -/
lemma one_le_one_add_inv (δ : ℝ) (hδ0 : 0 < δ) : (1 : ℝ) ≤ 1 + 1 / δ := by
  have h : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδ0)
  linarith
lemma inv_le_one_add_inv (δ : ℝ) (hδ0 : 0 < δ) : (1 / δ : ℝ) ≤ 1 + 1 / δ := by linarith
lemma invsq_le_inv (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : (1 : ℝ) ≤ 1 / δ := by
  exact (one_le_div hδ0).2 hδ1
lemma invsq_le_pow3 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := by
  calc
    (1 / δ) ^ 2 ≤ (1 / δ) ^ 3 := by
      have h1 : (1 : ℝ) ≤ 1 / δ := invsq_le_inv δ hδ0 hδ1
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (1 / δ))
      simpa [pow_succ, pow_two, mul_assoc] using h2
    _ ≤ (1 + 1 / δ) ^ 3 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / δ) (inv_le_one_add_inv δ hδ0) 3
lemma log_lepoly (δ : ℝ) (hδ0 : 0 < δ) : Real.log (1 + 1 / δ) ≤ 1 + 1 / δ := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / δ)
  linarith
lemma log1p_div_sq_le (δ : ℝ) (hδ0 : 0 < δ) :
    Real.log (1 + 1 / δ) / δ ^ 2 ≤ (1 + 1 / δ) ^ 3 := by
  calc
    Real.log (1 + 1 / δ) / δ ^ 2 = Real.log (1 + 1 / δ) * (1 / δ) ^ 2 := by
      field_simp [hδ0.ne']
    _ ≤ (1 + 1 / δ) * (1 / δ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (log_lepoly δ hδ0) (sq_nonneg _)
    _ ≤ (1 + 1 / δ) * (1 + 1 / δ) ^ 2 := by
      have hsq : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 / δ) (inv_le_one_add_inv δ hδ0) 2
      exact mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 1 + 1 / δ)
    _ = (1 + 1 / δ) ^ 3 := by ring
lemma logxadd6_le (t : ℝ) : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
  have h : |t| + 6 ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
  have h1 : Real.log (|t| + 6) ≤ Real.log ((|t| + 3) ^ 2) := Real.log_le_log (by nlinarith [abs_nonneg t]) h
  calc
    Real.log (|t| + 6) ≤ Real.log ((|t| + 3) ^ 2) := h1
    _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; ring
lemma LL_ge_one (t : ℝ) : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
  have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by nlinarith [abs_nonneg t])
  linarith
lemma logx6_div_sq_le_two (δ t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (|t| + 6) / δ ^ 2 ≤
      2 * ((1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3) := by
  let L : ℝ := Real.log (|t| + 3) + 1
  have hL1 : (1 : ℝ) ≤ L := LL_ge_one t
  have hLpos : 0 ≤ L := by linarith
  have hlg2 : Real.log (|t| + 6) ≤ 2 * L := by
    have h := logxadd6_le t
    dsimp [L]
    nlinarith
  have hD : L * (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := by
    have hs : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := invsq_le_pow3 δ hδ0 hδ1
    have h1 : L * (1 / δ) ^ 2 ≤ L * (1 + 1 / δ) ^ 3 := mul_le_mul_of_nonneg_left hs hLpos
    have hLpow : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0)
    have h2 : L * (1 + 1 / δ) ^ 3 ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hLpow (by positivity : 0 ≤ (1 + 1 / δ) ^ 3)
    exact le_trans h1 h2
  calc
    Real.log (|t| + 6) / δ ^ 2 = Real.log (|t| + 6) * (1 / δ) ^ 2 := by
      field_simp [hδ0.ne']
    _ ≤ (2 * L) * (1 / δ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hlg2 (sq_nonneg _)
    _ = 2 * (L * (1 / δ) ^ 2) := by ring
    _ ≤ 2 * ((1 + 1 / δ) ^ 3 * L ^ 3) := mul_le_mul_of_nonneg_left hD (by norm_num)
    _ = 2 * ((1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3) := by dsimp [L]
lemma final_arith {C1 : ℝ} (hC1 : 0 ≤ C1) {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 + 4 ≤
      (48 * (Real.log 8 + C1 + 1) + 480 + 4) * (1 + 1 / δ) ^ 3 *
        (Real.log (|t| + 3) + 1) ^ 3 := by
  let L : ℝ := Real.log (|t| + 3) + 1
  let D : ℝ := (1 + 1 / δ) ^ 3 * L ^ 3
  have hL1 : (1 : ℝ) ≤ L := LL_ge_one t
  have qinv : (1 / δ) ^ 2 ≤ D := by
    have hs : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := invsq_le_pow3 δ hδ0 hδ1
    have hL3 : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 (le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0))
    have hb : 0 ≤ (1 + 1 / δ) ^ 3 := by positivity
    calc
      (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := hs
      _ ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := le_mul_of_one_le_right hb hL3
      _ = D := by rfl
  have qlog1p : Real.log (1 + 1 / δ) / δ ^ 2 ≤ D := by
    have h := log1p_div_sq_le δ hδ0
    have hL3 : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 (le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0))
    have hb : 0 ≤ (1 + 1 / δ) ^ 3 := by positivity
    calc
      Real.log (1 + 1 / δ) / δ ^ 2 ≤ (1 + 1 / δ) ^ 3 := h
      _ ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := le_mul_of_one_le_right hb hL3
      _ = D := by rfl
  have qlogx6 : Real.log (|t| + 6) / δ ^ 2 ≤ 2 * D := by
    have h := logx6_div_sq_le_two δ t hδ0 hδ1
    simpa [D] using h
  have hDge1 : (1 : ℝ) ≤ D := by
    have h1a : (1 : ℝ) ≤ (1 + 1 / δ) ^ 3 :=
      le_trans (one_le_one_add_inv δ hδ0) (le_self_pow₀ (one_le_one_add_inv δ hδ0) (by norm_num : (3 : ℕ) ≠ 0))
    have h1b : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 (le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0))
    have hstep : (1 + 1 / δ) ^ 3 ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := by
      exact le_mul_of_one_le_right (by positivity : 0 ≤ (1 + 1 / δ) ^ 3) h1b
    calc
      (1 : ℝ) ≤ (1 + 1 / δ) ^ 3 := h1a
      _ ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := hstep
      _ = D := by rfl
  have B1 : 48 * Real.log 8 * (1 / δ) ^ 2 ≤ 48 * Real.log 8 * D := by
    exact mul_le_mul_of_nonneg_left qinv (by positivity : 0 ≤ 48 * Real.log 8)
  have B2 : 48 * C1 * (1 / δ) ^ 2 ≤ 48 * C1 * D := by
    exact mul_le_mul_of_nonneg_left qinv (mul_nonneg (by norm_num) hC1)
  have B3 : 48 * (Real.log (1 + 1 / δ) / δ ^ 2) ≤ 48 * D := by
    exact mul_le_mul_of_nonneg_left qlog1p (by norm_num : (0 : ℝ) ≤ 48)
  have B4 : 240 * (Real.log (|t| + 6) / δ ^ 2) ≤ 480 * D := by
    have h := mul_le_mul_of_nonneg_left qlogx6 (by norm_num : (0 : ℝ) ≤ 240)
    linarith
  have B5 : (4 : ℝ) ≤ 4 * D := by nlinarith
  calc
    48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 + 4
        = 48 * Real.log 8 * (1 / δ) ^ 2 + 48 * C1 * (1 / δ) ^ 2 +
            48 * (Real.log (1 + 1 / δ) / δ ^ 2) + 240 * (Real.log (|t| + 6) / δ ^ 2) + 4 := by
          have hδsq : δ ^ 2 ≠ 0 := by positivity
          field_simp [hδsq]
          ring
    _ ≤ 48 * Real.log 8 * D + 48 * C1 * D + 48 * D + 480 * D + 4 * D := by
          nlinarith
    _ = (48 * (Real.log 8 + C1 + 1) + 480 + 4) * D := by ring
    _ = (48 * (Real.log 8 + C1 + 1) + 480 + 4) * (1 + 1 / δ) ^ 3 *
        (Real.log (|t| + 3) + 1) ^ 3 := by
          simp [D, L]
          ring


theorem zeta_logDeriv_strip_bound_rh :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : RiemannHypothesis) (δ σ t : ℝ),
      0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
        (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by
  rcases zeta1_growth_ball with ⟨Cg, hCg0, hCg⟩
  let C1 : ℝ := Real.log (max Cg 1)
  let C : ℝ := (48 * (Real.log 8 + C1 + 1) + 480 + 4)
  refine ⟨C, ?_, ?_⟩
  · have hC1ge0 : 0 ≤ C1 := Real.log_nonneg (le_max_right Cg 1)
    have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num : (1 : ℝ) < 8)
    dsimp [C]
    nlinarith
  · intro h δ σ t hδ0 hδ1 hσlo hσhi hdist
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
    let R : ℝ := 3 / 2 - δ / 2
    let d : ℝ := ‖s - c‖
    let M : ℝ := Cg * (1 + 1 / δ) * (|t| + 6) ^ 5
    let A : ℝ := Real.log (2 * M) - Real.log (1 / 4)
    have hCgpos : 0 < Cg := hCg0
    have hC1ge0 : 0 ≤ C1 := Real.log_nonneg (le_max_right Cg 1)
    have hg : Differentiable ℂ riemannZeta₁ := by fun_prop
    -- geometry
    have hRpos : 0 < R := by
      dsimp [R]
      linarith
    have hdnorm : ‖s - c‖ = |σ - 2| := by
      dsimp [s, c]
      have h : ((σ : ℂ) + Complex.I * (t : ℂ)) - ((2 : ℂ) + Complex.I * (t : ℂ)) = ((σ - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [h]
      simpa [Real.norm_eq_abs] using (Complex.norm_real (σ - 2))
    have hσ2 : σ - 2 ≤ 0 := by linarith
    have hd_eq : d = 2 - σ := by
      dsimp [d]
      rw [hdnorm]
      have ha : |σ - 2| = 2 - σ := by
        rw [abs_of_nonpos hσ2]
        ring
      rw [ha]
    have hds : ‖s - c‖ < R := by
      change d < R
      rw [hd_eq]
      dsimp [R]
      have h1 : 2 - σ ≤ 3 / 2 - δ := by linarith
      have h2 : 3 / 2 - δ < 3 / 2 - δ / 2 := by linarith
      linarith
    have hs_ball : s ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hds
    -- nonzero on the ball under RH
    have hgne : ∀ w : ℂ, w ∈ Metric.ball c R → riemannZeta₁ w ≠ 0 := by
      intro w hw
      have hw1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hwre : (1 / 2 : ℝ) < w.re := by
        have hre2 : |(w - c).re| ≤ ‖w - c‖ := Complex.abs_re_le_norm (w - c)
        have hre2' : |w.re - 2| ≤ ‖w - c‖ := by simpa [c] using hre2
        have hneg : -(‖w - c‖) ≤ w.re - 2 := by
          have h0 : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs (w.re - 2)
          linarith
        dsimp [R] at hw1
        linarith
      exact zeta1_ne_zero_of_rh_gt_half h hwre
    -- upper growth bound on the ball
    have hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖riemannZeta₁ w‖ ≤ M := by
      intro w hw
      have hw1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hb := hCg δ t hδ0 hδ1 w (by simpa [c, R] using hw1)
      dsimp [M]
      exact hb
    -- lower bound at the centre c
    have hgm : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
      dsimp [c]
      exact zeta1_re_two_lower t
    have hMm : (1 / 4 : ℝ) ≤ M := by
      have hc_in : c ∈ Metric.ball c R := mem_ball_self hRpos
      exact le_trans hgm (hgM c hc_in)
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hMm
    -- apply the core lemma at s with radius δ/4
    have hρ0 : 0 < δ / 4 := by positivity
    have hρ_lt : δ / 4 < R - d := by
      dsimp [R]
      rw [hd_eq]
      linarith
    have hgcore : ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
        2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) := by
      have hh := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound hg (c := c) (R := R) (m := 1 / 4) (M := M)
        hRpos (by norm_num) hMm hgne hgM hgm (z₀ := s) hs_ball (ρ := δ / 4) hρ0 hρ_lt
      dsimp [A] at hh ⊢
      simpa [d] using hh
    -- relate to ζ'/ζ
    have hs_ne1 : s ≠ 1 := by
      intro h1
      have : ‖s - 1‖ = 0 := by simp [h1]
      linarith
    have hz1s : riemannZeta₁ s ≠ 0 := hgne s hs_ball
    have hlogd := zeta_logDeriv_norm_le s hs_ne1 hz1s
    have hdist4 : 1 / ‖s - 1‖ ≤ 4 := by
      have hs1pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne1)
      rw [div_le_iff₀ hs1pos]
      nlinarith
    -- bound on A
    have hA0 : 0 ≤ A := by
      dsimp [A]
      have h2M : (1 / 4 : ℝ) ≤ 2 * M := by nlinarith
      have h1 : Real.log (1 / 4) ≤ Real.log (2 * M) := Real.log_le_log (by norm_num) h2M
      linarith
    have hMlog : Real.log M = Real.log Cg + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6) := by
      have hpos1 : 0 < Cg := hCg0
      have hpos2 : 0 < 1 + 1 / δ := by positivity
      have hpos3 : 0 < (|t| + 6) ^ 5 := by positivity
      calc
        Real.log M = Real.log (Cg * ((1 + 1 / δ) * (|t| + 6) ^ 5)) := by
          congr 1
          dsimp [M]
          ring
        _ = Real.log Cg + Real.log ((1 + 1 / δ) * (|t| + 6) ^ 5) := by
          rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt (mul_pos hpos2 hpos3))]
        _ = Real.log Cg + (Real.log (1 + 1 / δ) + Real.log ((|t| + 6) ^ 5)) := by
          rw [Real.log_mul (ne_of_gt hpos2) (ne_of_gt hpos3)]
        _ = Real.log Cg + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6) := by
          rw [Real.log_pow]
          ring
    have hlogCg : Real.log Cg ≤ C1 := by
      dsimp [C1]
      exact Real.log_le_log (by positivity : 0 < Cg) (le_max_left Cg 1)
    have hA_le : A ≤ Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6) := by
      dsimp [A]
      have hlog : Real.log (2 * M) - Real.log (1 / 4) =
          Real.log 8 + Real.log M := by
        have h1 : Real.log (2 * M) - Real.log (1 / 4) = Real.log ((2 * M) / (1 / 4)) := by
          rw [Real.log_div (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hMpos)) (by norm_num)]
        have h2 : (2 * M) / (1 / 4) = 8 * M := by ring
        rw [h1, h2, Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hMpos)]
      rw [hlog, hMlog]
      nlinarith
    -- geometric bound: 2A(d+δ/4)/((R-d-δ/4)*(δ/4)) ≤ 48A/δ²
    have hgeom : 2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) ≤ 48 * A / δ ^ 2 := by
      have hd2pos : 0 < (R - d - δ / 4) * (δ / 4) := by
        have h1 : 0 < R - d - δ / 4 := by
          dsimp [R]
          rw [hd_eq]
          linarith
        positivity
      have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδ0
      have hcross : (d + δ / 4) * δ ^ 2 ≤ 24 * ((R - d - δ / 4) * (δ / 4)) := by
        dsimp [R]
        rw [hd_eq]
        have hδsq : 0 ≤ δ ^ 2 := sq_nonneg δ
        have h1 : (2 - σ + δ / 4) ≤ 3 / 2 := by nlinarith
        have h2 : (3 / 2 : ℝ) * δ ^ 2 ≤ 24 * ((3 / 2 - δ / 2 - (2 - σ) - δ / 4) * (δ / 4)) := by
          have hR : (3 / 2 - δ / 2 - (2 - σ) - δ / 4) = σ - 1 / 2 - 3 * δ / 4 := by ring
          rw [hR]
          have hsub : (1 / 4 : ℝ) * δ ≤ σ - 1 / 2 - 3 * δ / 4 := by nlinarith
          nlinarith
        calc
          (2 - σ + δ / 4) * δ ^ 2 ≤ (3 / 2) * δ ^ 2 := by
            exact mul_le_mul_of_nonneg_right h1 hδsq
          _ ≤ 24 * ((3 / 2 - δ / 2 - (2 - σ) - δ / 4) * (δ / 4)) := h2
      have hdiv : (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) ≤ 24 / δ ^ 2 := by
        rw [div_le_div_iff₀ hd2pos hδ2pos]
        exact hcross
      calc
        2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4))
            = 2 * A * ((d + δ / 4) / ((R - d - δ / 4) * (δ / 4))) := by ring
        _ ≤ 2 * A * (24 / δ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 * A)
        _ = 48 * A / δ ^ 2 := by ring
    -- final assembly
    have hB := final_arith (C1 := C1) hC1ge0 (δ := δ) (t := t) hδ0 hδ1
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by simpa [s] using hlogd
      _ ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 4 := by linarith
      _ ≤ 2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) + 4 := by linarith
      _ ≤ 48 * A / δ ^ 2 + 4 := by linarith
      _ ≤ 48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 + 4 := by
        have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδ0
        have hmul : 48 * A ≤ 48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) := by
          nlinarith
        have hdiv : 48 * A / δ ^ 2 ≤
            48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 :=
          div_le_div_of_nonneg_right hmul (le_of_lt hδ2pos)
        linarith
      _ ≤ (48 * (Real.log 8 + C1 + 1) + 480 + 4) * (1 + 1 / δ) ^ 3 *
          (Real.log (|t| + 3) + 1) ^ 3 := hB
      _ = C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by rfl
end Commons.NumberTheory.Zeta
