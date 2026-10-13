import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.Weight` — the integrating factor and the dominating function

Setting of `Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved`: the singular
first-order equation `w' + c(θ)w = H` with `c(θ) = 4 cos 2θ / sin 2θ - tan θ`.  We record the
integrating factor `m(θ) = sin²θ cos³θ` (`wfn`; `m' = m·c`), the dominating function
`Φ(θ) = (A/2) sin θ cos²θ + C sin²θ cos³θ` (`phfn`; `m·(A/sin 2θ + C) = Φ`) and the
elementary size bounds for both, in particular the endpoint behaviour
`m(θ) ≥ θ²/(2π²)` on `(0, π/4]` and `m(θ) ≥ 2(π/2-θ)³/π³` on `[π/4, π/2)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde

/-- The coefficient `c(θ) = 4 cos(2θ)/sin(2θ) - tan θ` of the ODE. -/
def coco (θ : ℝ) : ℝ := 4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ

/-- The integrating factor `m(θ) = sin²θ cos³θ`; `m' = m·c`. -/
def wfn (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Real.cos θ ^ 3

/-- The dominating function `Φ(θ) = (A/2) sin θ cos²θ + C sin²θ cos³θ`. -/
def phfn (A C θ : ℝ) : ℝ := A / 2 * Real.sin θ * Real.cos θ ^ 2
  + C * Real.sin θ ^ 2 * Real.cos θ ^ 3

lemma wfn_nonneg_of_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ wfn x := by
  rw [wfn]
  exact mul_nonneg
    (pow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx.1
      (by linarith [Real.pi_pos, hx.2]))) 2)
    (pow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩)) 3)

lemma wfn_pos_of_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (Real.pi / 2)) : 0 < wfn x := by
  rw [wfn]
  exact mul_pos
    (pow_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos, hx.2])) 2)
    (pow_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩) 3)

lemma wfn_le_sq (x : ℝ) : wfn x ≤ x ^ 2 := by
  have hcos3 : Real.cos x ^ 3 ≤ 1 := by
    nlinarith [Real.cos_le_one x, sq_nonneg (Real.cos x + 1 / 2)]
  have h1 : wfn x ≤ Real.sin x ^ 2 * 1 := by
    rw [wfn]
    exact mul_le_mul_of_nonneg_left hcos3 (sq_nonneg (Real.sin x))
  have h2 : Real.sin x ^ 2 ≤ x ^ 2 := Real.sin_sq_le_sq
  linarith

/-- Left-half lower bound: on `(0, π/4]`, `m(θ) ≥ θ²/(2π²)`. -/
lemma wfn_ge_left {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 4) :
    1 / (2 * Real.pi ^ 2) * θ ^ 2 ≤ wfn θ := by
  have hj : 2 / Real.pi * θ ≤ Real.sin θ :=
    Real.mul_le_sin (le_of_lt h0) (by linarith [h1, Real.pi_pos])
  have hj0 : 0 ≤ 2 / Real.pi * θ := by positivity
  have hsin2 : (2 / Real.pi * θ) ^ 2 ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hc : (1 : ℝ) / 2 ≤ Real.cos θ := by
    have hθmem : θ ∈ Icc 0 Real.pi := ⟨le_of_lt h0, by linarith [h1, Real.pi_pos]⟩
    have h3mem : Real.pi / 3 ∈ Icc 0 Real.pi :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hle : θ ≤ Real.pi / 3 := by linarith [h1, Real.pi_pos]
    have h := Real.strictAntiOn_cos.antitoneOn hθmem h3mem hle
    rwa [Real.cos_pi_div_three] at h
  have hcos3 : ((1 : ℝ) / 2) ^ 3 ≤ Real.cos θ ^ 3 := pow_le_pow_left₀ (by norm_num) hc 3
  have hmul := mul_le_mul hsin2 hcos3 (by positivity) (sq_nonneg (Real.sin θ))
  have harith : (2 / Real.pi * θ) ^ 2 * ((1 : ℝ) / 2) ^ 3 = 1 / (2 * Real.pi ^ 2) * θ ^ 2 := by
    field_simp
    try ring
  rw [wfn]
  linarith [hmul, harith]

/-- Right-half lower bound: with `δ = π/2 - θ` on `[π/4, π/2)`, `m(θ) ≥ 2δ³/π³`. -/
lemma wfn_ge_right {θ : ℝ} (h0 : Real.pi / 4 ≤ θ) (h1 : θ < Real.pi / 2) :
    2 / Real.pi ^ 3 * (Real.pi / 2 - θ) ^ 3 ≤ wfn θ := by
  have hδ0 : 0 < Real.pi / 2 - θ := by linarith
  have hs : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have hθmem : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos, h0], le_of_lt h1⟩
    have h6mem : Real.pi / 6 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hle : Real.pi / 6 ≤ θ := by linarith [h0, Real.pi_pos]
    have h := Real.strictMonoOn_sin.monotoneOn h6mem hθmem hle
    rwa [Real.sin_pi_div_six] at h
  have hsin2 : ((1 : ℝ) / 2) ^ 2 ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ (by norm_num) hs 2
  have hcos : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have hj : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.sin (Real.pi / 2 - θ) :=
      Real.mul_le_sin (le_of_lt hδ0) (by linarith)
    have hc : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
      conv_lhs => rw [show θ = Real.pi / 2 - (Real.pi / 2 - θ) from by ring]
      rw [Real.cos_pi_div_two_sub]
    rwa [hc]
  have hcos3 : (2 / Real.pi * (Real.pi / 2 - θ)) ^ 3 ≤ Real.cos θ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcos 3
  have hmul := mul_le_mul hsin2 hcos3 (by positivity) (sq_nonneg (Real.sin θ))
  have harith : ((1 : ℝ) / 2) ^ 2 * (2 / Real.pi * (Real.pi / 2 - θ)) ^ 3
      = 2 / Real.pi ^ 3 * (Real.pi / 2 - θ) ^ 3 := by
    field_simp
    try ring
  rw [wfn]
  linarith [hmul, harith]

/-- `Φ ≥ 0` on `[0, π/2]`. -/
lemma phfn_nonneg {A C θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) : 0 ≤ phfn A C θ := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos, h1])
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  rw [phfn]
  have h1' : 0 ≤ A / 2 * Real.sin θ * Real.cos θ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) hsin) (pow_nonneg hcos 2)
  have h2' : 0 ≤ C * Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hsin 2)) (pow_nonneg hcos 3)
  linarith

/-- `Φ(t) ≤ (A/2)·sin t + C·sin²t ≤ (A/2)t + Ct²` for `t ∈ [0, π/2]`. -/
lemma phfn_le_quad {A C θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) : phfn A C θ ≤ A / 2 * θ + C * θ ^ 2 := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos, h1])
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hsinle : Real.sin θ ≤ θ := Real.sin_le h0
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := pow_le_one₀ hcos (Real.cos_le_one θ)
  have hcos3 : Real.cos θ ^ 3 ≤ 1 := pow_le_one₀ hcos (Real.cos_le_one θ)
  have hsin2 : Real.sin θ ^ 2 ≤ θ ^ 2 := by nlinarith
  rw [phfn]
  have h1' : A / 2 * Real.sin θ * Real.cos θ ^ 2 ≤ A / 2 * θ := by
    calc A / 2 * Real.sin θ * Real.cos θ ^ 2 ≤ A / 2 * Real.sin θ * 1 :=
          mul_le_mul_of_nonneg_left hcos2 (mul_nonneg (by linarith) hsin)
      _ = A / 2 * Real.sin θ := by ring
      _ ≤ A / 2 * θ := mul_le_mul_of_nonneg_left hsinle (by linarith)
  have h2' : C * Real.sin θ ^ 2 * Real.cos θ ^ 3 ≤ C * θ ^ 2 := by
    calc C * Real.sin θ ^ 2 * Real.cos θ ^ 3 ≤ C * Real.sin θ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hcos3 (mul_nonneg hC (pow_nonneg hsin 2))
      _ = C * Real.sin θ ^ 2 := by ring
      _ ≤ C * θ ^ 2 := mul_le_mul_of_nonneg_left hsin2 hC
  linarith

/-- Left-end local bound: for `0 ≤ t ≤ θ ≤ π/2`, `Φ(t) ≤ (A/2)θ + Cθ²`. -/
lemma phfn_le_left {A C t θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ht0 : 0 ≤ t) (htθ : t ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    phfn A C t ≤ A / 2 * θ + C * θ ^ 2 := by
  have h1 : phfn A C t ≤ A / 2 * t + C * t ^ 2 := phfn_le_quad hA hC ht0 (le_trans htθ hθ)
  have h2 : A / 2 * t + C * t ^ 2 ≤ A / 2 * θ + C * θ ^ 2 := by
    have ht2 : t ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ ht0 htθ 2
    have h3 : C * t ^ 2 ≤ C * θ ^ 2 := mul_le_mul_of_nonneg_left ht2 hC
    have h4 : A / 2 * t ≤ A / 2 * θ := mul_le_mul_of_nonneg_left htθ (by linarith)
    linarith
  linarith

/-- Right-end local bound: for `0 ≤ θ ≤ t ≤ π/2`,
`Φ(t) ≤ (A/2)(π/2-θ)² + C(π/2-θ)³`. -/
lemma phfn_le_right {A C t θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ht0 : 0 ≤ t) (hθt : θ ≤ t) (ht : t ≤ Real.pi / 2) :
    phfn A C t ≤ A / 2 * (Real.pi / 2 - θ) ^ 2 + C * (Real.pi / 2 - θ) ^ 3 := by
  have hs : 0 ≤ Real.pi / 2 - t := by linarith
  have hsd : Real.pi / 2 - t ≤ Real.pi / 2 - θ := by linarith
  have hspi : Real.pi / 2 - t ≤ Real.pi := by linarith [Real.pi_pos, hs]
  have hcos_t : Real.cos t = Real.sin (Real.pi / 2 - t) := by
    conv_lhs => rw [show t = Real.pi / 2 - (Real.pi / 2 - t) from by ring]
    rw [Real.cos_pi_div_two_sub]
  have hcos_t_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ht⟩
  have hcos_t_sq : Real.cos t ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := by
    rw [hcos_t]
    exact le_trans Real.sin_sq_le_sq (pow_le_pow_left₀ hs hsd 2)
  have hcos_t_cu : Real.cos t ^ 3 ≤ (Real.pi / 2 - θ) ^ 3 := by
    rw [hcos_t]
    calc Real.sin (Real.pi / 2 - t) ^ 3 ≤ (Real.pi / 2 - t) ^ 3 :=
          pow_le_pow_left₀ (Real.sin_nonneg_of_nonneg_of_le_pi hs hspi) (Real.sin_le hs) 3
      _ ≤ (Real.pi / 2 - θ) ^ 3 := pow_le_pow_left₀ hs hsd 3
  have hsin_t_le : Real.sin t ≤ 1 := Real.sin_le_one t
  have hsin_t_nn : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos, ht])
  have hA2 : 0 ≤ A / 2 := by linarith
  have h1 : A / 2 * Real.sin t * Real.cos t ^ 2 ≤ A / 2 * (Real.pi / 2 - θ) ^ 2 := by
    calc A / 2 * Real.sin t * Real.cos t ^ 2 ≤ A / 2 * 1 * (Real.pi / 2 - θ) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsin_t_le hA2) hcos_t_sq (sq_nonneg _)
            (by nlinarith [hsin_t_nn, hA2])
      _ = A / 2 * (Real.pi / 2 - θ) ^ 2 := by ring
  have h2 : C * Real.sin t ^ 2 * Real.cos t ^ 3 ≤ C * (Real.pi / 2 - θ) ^ 3 := by
    calc C * Real.sin t ^ 2 * Real.cos t ^ 3 ≤ C * 1 * (Real.pi / 2 - θ) ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hsin_t_nn hsin_t_le) hC)
            hcos_t_cu (pow_nonneg hcos_t_nn 3) (by nlinarith [hC])
      _ = C * (Real.pi / 2 - θ) ^ 3 := by ring
  rw [phfn]
  linarith

end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
