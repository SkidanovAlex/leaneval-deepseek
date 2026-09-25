import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs

/-!
# Estimates for the boundary layer `bb` of the lacunary multiplier

This file collects the elementary real-variable estimates used to prove
`Work.BourgainPlan.Oscillation.Lacunary.boundary_tsum_sq_le`.
-/

open scoped BigOperators

namespace Work.BourgainPlan.Oscillation.Lacunary

noncomputable section

/-- A constant dominating `‖bb ρ i θ‖ ^ 2` for all `ρ > 1`, `i`, `θ ∈ [0,1]`. -/
def Cpt : ℝ := (Real.exp (4*Real.pi))^2 + (Real.pi^2*Real.exp (2*Real.pi)/4)^2 + 16 + 1

lemma Cpt_pos : 0 < Cpt := by unfold Cpt; positivity

lemma Cpt_ge_A1 : (Real.exp (4*Real.pi))^2 ≤ Cpt := by
  unfold Cpt
  linarith [sq_nonneg (Real.pi^2*Real.exp (2*Real.pi)/4), (show (0:ℝ) ≤ 16 by norm_num), (show (0:ℝ) ≤ 1 by norm_num)]

lemma Cpt_ge_A2 : (Real.pi^2*Real.exp (2*Real.pi)/4)^2 ≤ Cpt := by
  unfold Cpt
  linarith [sq_nonneg (Real.exp (4*Real.pi)), (show (0:ℝ) ≤ 16 by norm_num), (show (0:ℝ) ≤ 1 by norm_num)]

lemma Cpt_ge_16 : (16:ℝ) ≤ Cpt := by
  unfold Cpt
  nlinarith [sq_nonneg (Real.exp (4*Real.pi)), sq_nonneg (Real.pi^2*Real.exp (2*Real.pi)/4)]

/-! ## The Poisson-kernel identity -/

lemma mmClosed_denom_eq {ρ : ℝ} (i : ℕ) (θ : ℝ) :
    1 - 2 * lam ρ i * Real.cos (2*Real.pi*θ) + (lam ρ i)^2
      = (1 - lam ρ i)^2 + 4*lam ρ i*(Real.sin (Real.pi*θ))^2 := by
  have h : Real.cos (2*Real.pi*θ) = 1 - 2*(Real.sin (Real.pi*θ))^2 := by
    rw [show 2*Real.pi*θ = 2*(Real.pi*θ) by ring, Real.cos_two_mul]
    have hs := Real.sin_sq (Real.pi*θ); linarith [hs]
  rw [h]; ring

lemma mmClosed_eq {ρ : ℝ} (i : ℕ) (θ : ℝ) :
    mmClosed ρ i θ = (1-lam ρ i)^2 / ((1-lam ρ i)^2 + 4*lam ρ i*(Real.sin (Real.pi*θ))^2) := by
  unfold mmClosed
  rw [mmClosed_denom_eq]

lemma mmClosed_denom_pos' {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) :
    0 < (1-lam ρ i)^2 + 4*lam ρ i*(Real.sin (Real.pi*θ))^2 := by
  rw [← mmClosed_denom_eq]; exact mmClosed_denom_pos hρ i θ

lemma one_sub_mmClosed_eq {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) :
    1 - mmClosed ρ i θ
      = 4*lam ρ i*(Real.sin (Real.pi*θ))^2 / ((1-lam ρ i)^2 + 4*lam ρ i*(Real.sin (Real.pi*θ))^2) := by
  have hD := mmClosed_denom_pos' hρ i θ
  rw [mmClosed_eq, one_sub_div (ne_of_gt hD)]
  ring_nf

/-! ## Elementary estimates for `sin (πθ)` and `lam` -/

lemma sin_pi_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 ≤ Real.sin (Real.pi*θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  constructor <;> nlinarith [Real.pi_pos]

lemma two_mul_le_sin_pi {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) : 2*θ ≤ Real.sin (Real.pi*θ) := by
  have h := Real.mul_le_sin (show 0 ≤ Real.pi*θ by positivity)
    (show Real.pi*θ ≤ Real.pi/2 by nlinarith [Real.pi_pos])
  have heq : (2:ℝ)/Real.pi*(Real.pi*θ) = 2*θ := by field_simp
  linarith [h, heq]

lemma sin_pi_le {θ : ℝ} (hθ0 : 0 ≤ θ) : Real.sin (Real.pi*θ) ≤ Real.pi*θ :=
  Real.sin_le (by positivity)

lemma lam_ge {ρ : ℝ} (hρ : 1 ≤ ρ) (i : ℕ) : Real.exp (-(2*Real.pi)) ≤ lam ρ i := by
  have hcc : cc ρ i ≤ 1 := cc_le_one hρ i
  rw [lam, Real.exp_le_exp]; nlinarith [Real.pi_pos, hcc]

lemma one_sub_lam_ge {ρ : ℝ} (hρ : 1 ≤ ρ) (i : ℕ) :
    2*Real.pi*cc ρ i * Real.exp (-(2*Real.pi)) ≤ 1 - lam ρ i := by
  have hcc : cc ρ i ≤ 1 := cc_le_one hρ i
  have hcc0 : 0 < cc ρ i := cc_pos (by linarith) i
  have hx0 : 0 ≤ 2*Real.pi*cc ρ i := by positivity
  have hx2 : 2*Real.pi*cc ρ i ≤ 2*Real.pi := by nlinarith [Real.pi_pos, hcc]
  have hexp : Real.exp (-(2*Real.pi)) ≤ Real.exp (-(2*Real.pi*cc ρ i)) := by
    rw [Real.exp_le_exp]; linarith
  have h1 : 2*Real.pi*cc ρ i ≤ Real.exp (2*Real.pi*cc ρ i) - 1 := by
    linarith [Real.add_one_le_exp (2*Real.pi*cc ρ i)]
  have key : (Real.exp (2*Real.pi*cc ρ i) - 1) * Real.exp (-(2*Real.pi*cc ρ i)) = 1 - lam ρ i := by
    rw [lam, Real.exp_neg]; field_simp
  calc 2*Real.pi*cc ρ i * Real.exp (-(2*Real.pi))
      ≤ 2*Real.pi*cc ρ i * Real.exp (-(2*Real.pi*cc ρ i)) := mul_le_mul_of_nonneg_left hexp hx0
    _ ≤ (Real.exp (2*Real.pi*cc ρ i) - 1) * Real.exp (-(2*Real.pi*cc ρ i)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 - lam ρ i := key

lemma one_sub_lam_le (ρ : ℝ) (i : ℕ) : 1 - lam ρ i ≤ 2*Real.pi*cc ρ i := by
  have := Real.one_sub_le_exp_neg (2*Real.pi*cc ρ i)
  rw [lam]; linarith [this]

/-! ## Bridging `cc` with powers of `ρ` -/

lemma cc_eq_inv_pow (ρ : ℝ) (i : ℕ) : cc ρ i = (ρ⁻¹)^i := by
  unfold cc
  rw [zpow_neg, zpow_natCast, inv_pow]

lemma cc_pow_eq (ρ : ℝ) (i : ℕ) : (cc ρ i)^4 = ((ρ^4)⁻¹)^i := by
  rw [cc_eq_inv_pow, show (ρ^4)⁻¹ = (ρ⁻¹)^4 by rw [inv_pow], ← pow_mul, ← pow_mul, mul_comm]

lemma min_cc_eq (ρ : ℝ) (i : ℕ) (θ : ℝ) :
    min (θ^4/(cc ρ i)^4) ((cc ρ i)^4/θ^4)
      = min (θ^4*(ρ^4)^i) ((θ^4)⁻¹*((ρ^4)⁻¹)^i) := by
  have h1 : θ^4/(cc ρ i)^4 = θ^4*(ρ^4)^i := by
    rw [cc_pow_eq, div_eq_mul_inv, inv_pow, inv_inv]
  have h2 : (cc ρ i)^4/θ^4 = (θ^4)⁻¹*((ρ^4)⁻¹)^i := by
    rw [cc_pow_eq, div_eq_mul_inv, mul_comm]
  rw [h1, h2]

/-! ## The boundary layer in terms of `mmClosed` -/

lemma bb_eq_one {ρ : ℝ} {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hcc : θ ≤ cc ρ i) : bb ρ i θ = ((1 - mmClosed ρ i θ : ℝ) : ℂ) := by
  unfold bb phi piCut
  rw [if_pos (by rw [abs_of_nonneg hθ0]; exact hcc), if_pos hθ1]
  push_cast; ring

lemma bb_eq_zero {ρ : ℝ} {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hcc : ¬ θ ≤ cc ρ i) : bb ρ i θ = ((- mmClosed ρ i θ : ℝ) : ℂ) := by
  unfold bb phi piCut
  rw [if_neg (by rw [abs_of_nonneg hθ0]; exact hcc), if_pos hθ1]
  push_cast; ring

lemma bb_eq_ind {ρ : ℝ} {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 1/2 < θ) :
    bb ρ i θ = (if θ ≤ cc ρ i then (1:ℂ) else 0) := by
  unfold bb phi piCut
  rw [if_neg (by linarith : ¬ θ ≤ 1/2), zero_mul, sub_zero, abs_of_nonneg hθ0]

/-! ## Norm bounds for the two regimes -/

lemma bb_norm_le_A1 {ρ : ℝ} (hρ : 1 < ρ) {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hcc : θ ≤ cc ρ i) : ‖bb ρ i θ‖ ≤ Real.exp (4*Real.pi) * θ^2 / (cc ρ i)^2 := by
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : 1 ≤ ρ := le_of_lt hρ
  have hcc0 : 0 < cc ρ i := cc_pos hρ0 i
  have hσ0 : 0 ≤ Real.sin (Real.pi*θ) := sin_pi_nonneg hθ0 (by linarith)
  have hσle : Real.sin (Real.pi*θ) ≤ Real.pi*θ := sin_pi_le hθ0
  have hlamle1 : lam ρ i ≤ 1 := le_of_lt (lam_lt_one hρ0 i)
  have hmble : mmClosed ρ i θ ≤ 1 := mmClosed_le_one hρ0 i θ
  have hexp : Real.exp (4*Real.pi)*Real.exp (-(4*Real.pi)) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have key1 : 4*Real.pi^2*(cc ρ i)^2*lam ρ i ≤ Real.exp (4*Real.pi)*(1-lam ρ i)^2 := by
    have h1lam := one_sub_lam_ge hρ1 i
    have h2c : 0 ≤ 2*Real.pi*cc ρ i*Real.exp (-(2*Real.pi)) := by positivity
    have hsq := pow_le_pow_left₀ h2c h1lam 2
    have hsq' : 4*Real.pi^2*(cc ρ i)^2*Real.exp (-(4*Real.pi)) ≤ (1-lam ρ i)^2 := by
      have he2 : Real.exp (-(4*Real.pi)) = (Real.exp (-(2*Real.pi)))^2 := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have h : (2*Real.pi*cc ρ i*Real.exp (-(2*Real.pi)))^2
          = 4*Real.pi^2*(cc ρ i)^2*Real.exp (-(4*Real.pi)) := by
        rw [he2]; ring
      rwa [h] at hsq
    have h4 : 4*Real.pi^2*(cc ρ i)^2*lam ρ i ≤ 4*Real.pi^2*(cc ρ i)^2 :=
      mul_le_of_le_one_right (by positivity) hlamle1
    have h5 : 4*Real.pi^2*(cc ρ i)^2 ≤ Real.exp (4*Real.pi)*(1-lam ρ i)^2 := by
      have hm := mul_le_mul_of_nonneg_left hsq' (Real.exp_pos (4*Real.pi)).le
      have heq : Real.exp (4*Real.pi)*(4*Real.pi^2*(cc ρ i)^2*Real.exp (-(4*Real.pi)))
          = 4*Real.pi^2*(cc ρ i)^2 := by
        rw [show Real.exp (4*Real.pi)*(4*Real.pi^2*(cc ρ i)^2*Real.exp (-(4*Real.pi)))
            = 4*Real.pi^2*(cc ρ i)^2*(Real.exp (4*Real.pi)*Real.exp (-(4*Real.pi))) by ring,
            hexp, mul_one]
      rw [heq] at hm; exact hm
    linarith
  have hDpos := mmClosed_denom_pos' hρ0 i θ
  rw [bb_eq_one hθ0 hθ1 hcc]
  rw [norm_ofReal_complex]
  rw [abs_of_nonneg (show (0:ℝ) ≤ 1 - mmClosed ρ i θ by linarith)]
  rw [one_sub_mmClosed_eq hρ0 i θ]
  rw [div_le_div_iff₀ hDpos (pow_pos hcc0 2)]
  have hσ2 : (Real.sin (Real.pi*θ))^2 ≤ Real.pi^2*θ^2 := by
    calc (Real.sin (Real.pi*θ))^2 ≤ (Real.pi*θ)^2 := pow_le_pow_left₀ hσ0 hσle 2
      _ = Real.pi^2*θ^2 := by ring
  calc 4*lam ρ i*(Real.sin (Real.pi*θ))^2*(cc ρ i)^2
      = 4*lam ρ i*(cc ρ i)^2*(Real.sin (Real.pi*θ))^2 := by ring
    _ ≤ 4*lam ρ i*(cc ρ i)^2*(Real.pi^2*θ^2) :=
        mul_le_mul_of_nonneg_left hσ2
          (mul_nonneg (mul_nonneg (by norm_num) (lam_pos hρ0 i).le) (sq_nonneg _))
    _ = 4*Real.pi^2*(cc ρ i)^2*lam ρ i*θ^2 := by ring
    _ ≤ Real.exp (4*Real.pi)*(1-lam ρ i)^2*θ^2 := by
        exact mul_le_mul_of_nonneg_right key1 (sq_nonneg θ)
    _ = Real.exp (4*Real.pi)*θ^2*(1-lam ρ i)^2 := by ring
    _ ≤ Real.exp (4*Real.pi)*θ^2*((1-lam ρ i)^2 + 4*lam ρ i*(Real.sin (Real.pi*θ))^2) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) (lam_pos hρ0 i).le) (sq_nonneg _)))
          (mul_nonneg (Real.exp_pos _).le (sq_nonneg θ))

lemma bb_norm_le_A2 {ρ : ℝ} (hρ : 1 < ρ) {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hcc : ¬ θ ≤ cc ρ i) :
    ‖bb ρ i θ‖ ≤ Real.pi^2*(cc ρ i)^2*Real.exp (2*Real.pi) / (4*θ^2) := by
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : 1 ≤ ρ := le_of_lt hρ
  have hcc0 : 0 < cc ρ i := cc_pos hρ0 i
  have hθpos : 0 < θ := lt_trans hcc0 (not_le.mp hcc)
  have hDpos := mmClosed_denom_pos' hρ0 i θ
  have hσ2 : 4*θ^2 ≤ (Real.sin (Real.pi*θ))^2 := by
    have h1 : (2*θ)^2 ≤ (Real.sin (Real.pi*θ))^2 :=
      pow_le_pow_left₀ (by positivity) (two_mul_le_sin_pi hθ0 hθ1) 2
    nlinarith [h1]
  have h1lamle : (1 - lam ρ i)^2 ≤ 4*Real.pi^2*(cc ρ i)^2 := by
    have h := one_sub_lam_le ρ i
    have h0 : 0 ≤ 1 - lam ρ i := (one_sub_lam_pos hρ0 i).le
    have h2 : (1-lam ρ i)^2 ≤ (2*Real.pi*cc ρ i)^2 := pow_le_pow_left₀ h0 h 2
    nlinarith [h2]
  have hlamE : 1 ≤ lam ρ i*Real.exp (2*Real.pi) := by
    have h := mul_le_mul_of_nonneg_right (lam_ge hρ1 i) (Real.exp_pos (2*Real.pi)).le
    rwa [show Real.exp (-(2*Real.pi))*Real.exp (2*Real.pi) = 1 by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]] at h
  have key2 : 16*Real.pi^2*(cc ρ i)^2*θ^2
      ≤ 4*Real.pi^2*(cc ρ i)^2*lam ρ i*(Real.sin (Real.pi*θ))^2*Real.exp (2*Real.pi) := by
    have hA : 16*Real.pi^2*(cc ρ i)^2*θ^2
        ≤ 4*Real.pi^2*(cc ρ i)^2*(Real.sin (Real.pi*θ))^2 := by
      have h4 : 16*Real.pi^2*(cc ρ i)^2*θ^2 = 4*Real.pi^2*(cc ρ i)^2*(4*θ^2) := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left hσ2 (by positivity)
    have hB : 4*Real.pi^2*(cc ρ i)^2*(Real.sin (Real.pi*θ))^2
        ≤ 4*Real.pi^2*(cc ρ i)^2*(Real.sin (Real.pi*θ))^2*(lam ρ i*Real.exp (2*Real.pi)) :=
      le_mul_of_one_le_right (by positivity) hlamE
    calc 16*Real.pi^2*(cc ρ i)^2*θ^2
        ≤ 4*Real.pi^2*(cc ρ i)^2*(Real.sin (Real.pi*θ))^2 := hA
      _ ≤ 4*Real.pi^2*(cc ρ i)^2*(Real.sin (Real.pi*θ))^2*(lam ρ i*Real.exp (2*Real.pi)) := hB
      _ = 4*Real.pi^2*(cc ρ i)^2*lam ρ i*(Real.sin (Real.pi*θ))^2*Real.exp (2*Real.pi) := by ring
  rw [bb_eq_zero hθ0 hθ1 hcc]
  rw [norm_ofReal_complex]
  rw [abs_neg, abs_of_nonneg (mmClosed_nonneg hρ0 i θ)]
  rw [mmClosed_eq]
  rw [div_le_div_iff₀ hDpos (by positivity : 0 < 4*θ^2)]
  calc (1 - lam ρ i)^2*(4*θ^2)
      ≤ 4*Real.pi^2*(cc ρ i)^2*(4*θ^2) := mul_le_mul_of_nonneg_right h1lamle (by positivity)
    _ = 16*Real.pi^2*(cc ρ i)^2*θ^2 := by ring
    _ ≤ 4*Real.pi^2*(cc ρ i)^2*lam ρ i*(Real.sin (Real.pi*θ))^2*Real.exp (2*Real.pi) := key2
    _ = Real.pi^2*(cc ρ i)^2*Real.exp (2*Real.pi)*(4*lam ρ i*(Real.sin (Real.pi*θ))^2) := by ring
    _ ≤ Real.pi^2*(cc ρ i)^2*Real.exp (2*Real.pi)
          *((1-lam ρ i)^2 + 4*lam ρ i*(Real.sin (Real.pi*θ))^2) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (sq_nonneg _))
          (by positivity)

/-! ## The minimum comparison and the pointwise bound -/

lemma min_cc_left {ρ : ℝ} (hρ : 0 < ρ) {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (h : θ ≤ cc ρ i) :
    min (θ^4/(cc ρ i)^4) ((cc ρ i)^4/θ^4) = θ^4/(cc ρ i)^4 := by
  apply min_eq_left
  have hc0 : 0 < cc ρ i := cc_pos hρ i
  by_cases hθ : θ = 0
  · subst hθ; simp
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ)
    rw [div_le_div_iff₀ (pow_pos hc0 4) (pow_pos hθpos 4)]
    have h8 : θ^8 ≤ (cc ρ i)^8 := pow_le_pow_left₀ hθ0 h 8
    calc θ^4 * θ^4 = θ^8 := by ring
      _ ≤ (cc ρ i)^8 := h8
      _ = (cc ρ i)^4 * (cc ρ i)^4 := by ring

lemma min_cc_right {ρ : ℝ} (hρ : 0 < ρ) {i : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h : ¬ θ ≤ cc ρ i) :
    min (θ^4/(cc ρ i)^4) ((cc ρ i)^4/θ^4) = (cc ρ i)^4/θ^4 := by
  apply min_eq_right
  have hc0 : 0 < cc ρ i := cc_pos hρ i
  have hθpos : 0 < θ := lt_trans hc0 (not_le.mp h)
  rw [div_le_div_iff₀ (pow_pos hθpos 4) (pow_pos hc0 4)]
  have h8 : (cc ρ i)^8 ≤ θ^8 := pow_le_pow_left₀ hc0.le (le_of_lt (not_le.mp h)) 8
  calc (cc ρ i)^4 * (cc ρ i)^4 = (cc ρ i)^8 := by ring
    _ ≤ θ^8 := h8
    _ = θ^4 * θ^4 := by ring

theorem bb_sq_le_cc (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖bb ρ i θ‖^2 ≤ Cpt * min (θ^4/(cc ρ i)^4) ((cc ρ i)^4/θ^4) := by
  have hρ0 : 0 < ρ := by linarith
  have hc0 : 0 < cc ρ i := cc_pos hρ0 i
  have hc1 : cc ρ i ≤ 1 := cc_le_one (le_of_lt hρ) i
  have hmin0 : 0 ≤ min (θ^4/(cc ρ i)^4) ((cc ρ i)^4/θ^4) :=
    le_min (by positivity) (by positivity)
  by_cases hθ : θ ≤ 1/2
  · by_cases hcc : θ ≤ cc ρ i
    · have h := bb_norm_le_A1 hρ hθ0 hθ hcc
      have h2 : ‖bb ρ i θ‖^2 ≤ (Real.exp (4*Real.pi) * θ^2 / (cc ρ i)^2)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      have heq : (Real.exp (4*Real.pi) * θ^2 / (cc ρ i)^2)^2
          = (Real.exp (4*Real.pi))^2 * (θ^4/(cc ρ i)^4) := by ring
      rw [min_cc_left hρ0 hθ0 hcc]
      calc ‖bb ρ i θ‖^2 ≤ (Real.exp (4*Real.pi) * θ^2 / (cc ρ i)^2)^2 := h2
        _ = (Real.exp (4*Real.pi))^2 * (θ^4/(cc ρ i)^4) := heq
        _ ≤ Cpt * (θ^4/(cc ρ i)^4) :=
            mul_le_mul_of_nonneg_right Cpt_ge_A1 (by positivity)
    · have h := bb_norm_le_A2 hρ hθ0 hθ hcc
      have h2 : ‖bb ρ i θ‖^2
          ≤ (Real.pi^2*(cc ρ i)^2*Real.exp (2*Real.pi) / (4*θ^2))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      have heq : (Real.pi^2*(cc ρ i)^2*Real.exp (2*Real.pi) / (4*θ^2))^2
          = (Real.pi^2*Real.exp (2*Real.pi)/4)^2 * ((cc ρ i)^4/θ^4) := by ring
      rw [min_cc_right hρ0 hθ0 hcc]
      calc ‖bb ρ i θ‖^2
            ≤ (Real.pi^2*(cc ρ i)^2*Real.exp (2*Real.pi) / (4*θ^2))^2 := h2
        _ = (Real.pi^2*Real.exp (2*Real.pi)/4)^2 * ((cc ρ i)^4/θ^4) := heq
        _ ≤ Cpt * ((cc ρ i)^4/θ^4) :=
            mul_le_mul_of_nonneg_right Cpt_ge_A2 (by positivity)
  · have hhalf : (1:ℝ)/2 < θ := not_le.mp hθ
    by_cases hcc : θ ≤ cc ρ i
    · rw [bb_eq_ind hθ0 hhalf]
      have hge : (1:ℝ)/16 ≤ θ^4/(cc ρ i)^4 := by
        rw [le_div_iff₀ (pow_pos hc0 4)]
        have hc4 : (cc ρ i)^4 ≤ 1 := pow_le_one₀ hc0.le hc1
        have hθ4 : (1:ℝ)/16 ≤ θ^4 := by
          have h1 : ((1:ℝ)/2)^4 ≤ θ^4 := pow_le_pow_left₀ (by norm_num) hhalf.le 4
          linarith [h1]
        nlinarith [hc4, hθ4]
      rw [min_cc_left hρ0 hθ0 hcc]
      have : (1:ℝ) ≤ 16 * (θ^4/(cc ρ i)^4) := by linarith
      calc ‖(if θ ≤ cc ρ i then (1:ℂ) else 0)‖^2 = 1 := by
            rw [if_pos hcc]; norm_num
        _ ≤ 16 * (θ^4/(cc ρ i)^4) := this
        _ ≤ Cpt * (θ^4/(cc ρ i)^4) :=
            mul_le_mul_of_nonneg_right Cpt_ge_16 (by positivity)
    · rw [bb_eq_ind hθ0 hhalf]
      rw [if_neg hcc, norm_zero, zero_pow (by norm_num)]
      rw [min_cc_right hρ0 hθ0 hcc]
      exact mul_nonneg Cpt_pos.le (by positivity)

end

end Work.BourgainPlan.Oscillation.Lacunary
