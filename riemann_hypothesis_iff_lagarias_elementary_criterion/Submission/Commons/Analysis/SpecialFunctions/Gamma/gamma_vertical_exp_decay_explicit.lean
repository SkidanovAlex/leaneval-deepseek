import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay

open Complex Filter MeasureTheory Set
open scoped Real Topology Interval

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

noncomputable section

/-- Jordan-type bound: for `0 < σ` and `0 < d ≤ 1`,
`(sin d)^{-σ} ≤ (π/2)^σ · (1/d)^σ`. -/
lemma sin_pow_neg_le_explicit (σ : ℝ) (hσ : 0 < σ) {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1) :
    (Real.sin d) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 / d) ^ σ := by
  have hdpi : d ≤ Real.pi / 2 := by linarith [hd', Real.two_le_pi]
  have hdpi' : d < Real.pi := by linarith [hd', Real.two_le_pi]
  have hsinpos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd hdpi'
  let a : ℝ := (2 / Real.pi) * d
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_sin : a ≤ Real.sin d := by
    dsimp [a]
    exact Real.mul_le_sin hd.le hdpi
  have hsininv_le : (Real.sin d)⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hsinpos ha).2 ha_sin
  have ha_inv : a⁻¹ = (Real.pi / 2) * (1 / d) := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, hd.ne']
  calc
    (Real.sin d) ^ (-σ) = (Real.sin d)⁻¹ ^ σ := by rw [Real.rpow_neg_eq_inv_rpow]
    _ ≤ a⁻¹ ^ σ := Real.rpow_le_rpow (inv_nonneg.mpr hsinpos.le) hsininv_le (le_of_lt hσ)
    _ = (Real.pi / 2 * (1 / d)) ^ σ := by rw [ha_inv]
    _ = (Real.pi / 2) ^ σ * (1 / d) ^ σ := Real.mul_rpow (le_of_lt Real.pi_div_two_pos) (by positivity)

/-- The case `0 ≤ t`: choose `θ = -π/2 + 1/(1+t)`. -/
lemma bound_nonneg_explicit (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rw [abs_of_nonneg ht]
  let θ : ℝ := -(Real.pi / 2) + 1 / (1 + t)
  have h1pt : 0 < 1 + t := by linarith
  have hu0 : 0 < 1 / (1 + t) := by exact div_pos zero_lt_one h1pt
  have hu1 : 1 / (1 + t) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + t)) := by
    dsimp [θ]
    rw [show -(Real.pi / 2) + 1 / (1 + t) = -(Real.pi / 2 - 1 / (1 + t)) by ring]
    rw [Real.cos_neg, Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + t))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := sin_pow_neg_le_explicit σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + t)) = 1 + t := by
    field_simp [h1pt.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + t) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + t))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + t) ^ σ := by rw [hrec]
  have hut : (1 / (1 + t)) * t ≤ 1 := by
    field_simp [h1pt.ne']
    linarith
  have hθt : θ * t ≤ -(Real.pi / 2) * t + 1 := by
    dsimp [θ]
    calc
      (-(Real.pi / 2) + 1 / (1 + t)) * t
          = -(Real.pi / 2) * t + (1 / (1 + t)) * t := by ring
      _ ≤ -(Real.pi / 2) * t + 1 := add_le_add_right hut (-(Real.pi / 2) * t)
  have hA : Real.exp (θ * t) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by
    calc
      Real.exp (θ * t) ≤ Real.exp (-(Real.pi / 2) * t + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * t) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * t))).le
  have hcomb : Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + t) ^ σ * Real.exp (-(Real.pi / 2) * t) := by ring⟩

/-- The case `t ≤ 0`: choose `θ = π/2 - 1/(1-t)`. -/
lemma bound_nonpos_explicit (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : t ≤ 0) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  let s : ℝ := -t
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hts : t = -s := by dsimp [s]; ring
  have habs : |t| = s := by
    dsimp [s]
    rw [abs_of_nonpos ht]
  rw [habs, hts]
  let θ : ℝ := Real.pi / 2 - 1 / (1 + s)
  have h1ps : 0 < 1 + s := by linarith
  have hu0 : 0 < 1 / (1 + s) := by exact div_pos zero_lt_one h1ps
  have hu1 : 1 / (1 + s) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
    · dsimp [θ]; linarith
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + s)) := by
    dsimp [θ]
    rw [Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + s))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := sin_pow_neg_le_explicit σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + s)) = 1 + s := by
    field_simp [h1ps.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + s) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + s))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + s) ^ σ := by rw [hrec]
  have hus : (1 / (1 + s)) * s ≤ 1 := by
    field_simp [h1ps.ne']
    linarith
  have hθt : θ * (-s) ≤ -(Real.pi / 2) * s + 1 := by
    dsimp [θ]
    calc
      (Real.pi / 2 - 1 / (1 + s)) * (-s)
          = -(Real.pi / 2) * s + (1 / (1 + s)) * s := by ring
      _ ≤ -(Real.pi / 2) * s + 1 := add_le_add_right hus (-(Real.pi / 2) * s)
  have hA : Real.exp (θ * (-s)) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by
    calc
      Real.exp (θ * (-s)) ≤ Real.exp (-(Real.pi / 2) * s + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * s) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * s))).le
  have hcomb : Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + s) ^ σ * Real.exp (-(Real.pi / 2) * s) := by ring⟩

/-- For every real `t` there is an admissible rotation angle `θ` (`|θ| < π/2`, `cos θ > 0`)
with the explicit bound `e^{θt}·(cos θ)^{-σ} ≤ e·(π/2)^σ·(1+|t|)^σ·e^{-π|t|/2}`. -/
lemma angle_choice_explicit (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rcases le_total 0 t with ht | ht
  · exact bound_nonneg_explicit σ hσ ht
  · exact bound_nonpos_explicit σ hσ ht

/-- Explicit Stirling-type vertical bound for the Gamma function, valid uniformly in the real
part `σ > 0` with the constant shown explicitly (the existential constant of
`gamma_vertical_exp_decay` is in fact `Real.Gamma σ · exp 1 · (Real.pi / 2) ^ σ`):
`‖Γ(σ + i t)‖ ≤ Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ * (1 + |t|) ^ σ * exp (-(π/2)·|t|)`
for all real `σ > 0` and `t`. -/
theorem gamma_vertical_exp_decay_explicit (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ ≤
      Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ * (1 + |t|) ^ σ *
        Real.exp (-(Real.pi / 2) * |t|) := by
  rcases angle_choice_explicit σ hσ t with ⟨θ, hθabs, hθcos, hθb⟩
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs0 : 0 < s.re := by
    dsimp [s]
    simp [hσ]
  have hest := GRRect.rot_estimate s hs0 hθabs
  have h₁ : ‖Complex.Gamma s‖ ≤
      (Real.Gamma σ) * (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) := by
    have hre : s.re = σ := by simp [s]
    have him : s.im = t := by simp [s]
    rw [hre, him] at hest
    rw [← mul_assoc]
    exact hest
  have h₂ : Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
    simpa [mul_assoc] using hθb
  calc
    ‖Complex.Gamma s‖ ≤ (Real.Gamma σ) * (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) := h₁
    _ ≤ (Real.Gamma σ) * ((Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ *
          Real.exp (-(Real.pi / 2) * |t|)) := by
      exact mul_le_mul_of_nonneg_left h₂ (le_of_lt (Real.Gamma_pos_of_pos hσ))
    _ = Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ * (1 + |t|) ^ σ *
          Real.exp (-(Real.pi / 2) * |t|) := by
      ring

end
end Commons.Analysis.SpecialFunctions.Gamma
