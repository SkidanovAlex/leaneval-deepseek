import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_explicit
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_sinh_ofReal
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_sin_le_exp_im
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.Analysis.SpecialFunctions.Gamma.log_Gamma_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_real_growth

open Complex
open scoped Real Topology

set_option autoImplicit false

namespace Commons.Analysis.Complex

/-- Crude bound on the real Gamma function on `[1, 11]`. -/
lemma real_Gamma_le_M {σ : ℝ} (h1 : 1 ≤ σ) (hσ : σ ≤ 11) :
    Real.Gamma σ ≤ (10 : ℝ) ^ 11 := by
  by_cases h2 : σ ≤ 2
  · have hΓ1 : Real.Gamma σ ≤ 1 := by
      have hσmem : σ ∈ Set.Icc (1 : ℝ) 2 := by
        constructor <;> linarith
      exact Commons.Analysis.SpecialFunctions.Gamma.Gamma_le_one_of_mem_Icc_one_two hσmem
    have hle : (1 : ℝ) ≤ (10 : ℝ) ^ 11 := by
      have h10 : 1 ≤ (10 : ℝ) := by norm_num
      have hpow : (10 : ℝ) ^ 0 ≤ (10 : ℝ) ^ 11 := pow_le_pow_right₀ h10 (by norm_num : 0 ≤ 11)
      simpa using hpow
    exact le_trans hΓ1 hle
  · have h2' : 2 ≤ σ := le_of_not_ge h2
    have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn
    have hmem2 : σ ∈ Set.Ici (2 : ℝ) := by exact h2'
    have hmem11 : (11 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
    have hleΓ : Real.Gamma σ ≤ Real.Gamma (11 : ℝ) := hmono hmem2 hmem11 hσ
    have hΓ11 : Real.Gamma (11 : ℝ) = ((10 : ℕ).factorial : ℝ) := by
      have hcast : (11 : ℝ) = ((10 : ℕ) : ℝ) + 1 := by norm_num
      rw [hcast]
      exact Real.Gamma_nat_eq_factorial 10
    have hfac : ((10 : ℕ).factorial : ℝ) ≤ (10 : ℝ) ^ 11 := by
      have h10 : 1 ≤ (10 : ℝ) := by norm_num
      have hpow : (10 : ℝ) ^ 10 ≤ (10 : ℝ) ^ 11 := pow_le_pow_right₀ h10 (by norm_num)
      calc
        ((10 : ℕ).factorial : ℝ) ≤ (10 : ℝ) ^ 10 := by
          exact Commons.Analysis.SpecialFunctions.Gamma.factorial_le_pow_real 10
        _ ≤ (10 : ℝ) ^ 11 := hpow
    calc
      Real.Gamma σ ≤ Real.Gamma (11 : ℝ) := hleΓ
      _ = ((10 : ℕ).factorial : ℝ) := hΓ11
      _ ≤ (10 : ℝ) ^ 11 := hfac

/-- Explicit constants used in the final bounds. -/
noncomputable def Mbig : ℝ := (10 : ℝ) ^ 11
noncomputable def K6 : ℝ := Mbig * Real.exp 1 * (Real.pi / 2) ^ (6 : ℝ)
noncomputable def cRef : ℝ := Real.pi / K6

lemma Mbig_pos : 0 < Mbig := by
  dsimp [Mbig]
  positivity

lemma K6_pos : 0 < K6 := by
  dsimp [K6]
  exact mul_pos (mul_pos Mbig_pos (Real.exp_pos 1)) (Real.rpow_pos_of_pos (by positivity) _)

lemma cRef_pos : 0 < cRef := by
  dsimp [cRef]
  exact div_pos Real.pi_pos K6_pos

lemma exp_one_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
  simpa [Real.exp_zero] using (Real.exp_le_exp).2 (by norm_num : (0 : ℝ) ≤ 1)

lemma pi_div_two_ge_one : (1 : ℝ) ≤ Real.pi / 2 := by
  have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  linarith

lemma Mbig_le_K6 : Mbig ≤ K6 := by
  dsimp [K6]
  have hp : (1 : ℝ) ≤ (Real.pi / 2) ^ (6 : ℝ) := by
    have h0 : (Real.pi / 2) ^ (0 : ℝ) ≤ (Real.pi / 2) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le pi_div_two_ge_one (by norm_num : (0 : ℝ) ≤ 6)
    simpa using h0
  have h1 : Mbig ≤ Mbig * Real.exp 1 := le_mul_of_one_le_right Mbig_pos.le exp_one_ge_one
  have h2 : Mbig * Real.exp 1 ≤ Mbig * Real.exp 1 * (Real.pi / 2) ^ (6 : ℝ) :=
    le_mul_of_one_le_right (mul_nonneg Mbig_pos.le (Real.exp_pos 1).le) hp
  exact le_trans h1 h2

lemma K6_ge_one : (1 : ℝ) ≤ K6 := by
  calc
    (1 : ℝ) ≤ Mbig := by
      dsimp [Mbig]
      have h10 : 1 ≤ (10 : ℝ) := by norm_num
      have hp : (10 : ℝ) ^ 0 ≤ (10 : ℝ) ^ 11 := pow_le_pow_right₀ h10 (by norm_num)
      simpa using hp
    _ ≤ K6 := Mbig_le_K6

lemma K6_ge_pi : Real.pi ≤ K6 := by
  have hM : Real.pi ≤ Mbig := by
    have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
    have h4 : (4 : ℝ) ≤ Mbig := by
      dsimp [Mbig]
      have h10 : 1 ≤ (10 : ℝ) := by norm_num
      have hp : (10 : ℝ) ^ 1 ≤ (10 : ℝ) ^ 11 := pow_le_pow_right₀ h10 (by norm_num)
      have h1 : (10 : ℝ) ^ 1 = (10 : ℝ) := by norm_num
      nlinarith
    linarith
  exact le_trans hM Mbig_le_K6

lemma cRef_le_one : cRef ≤ 1 := by
  have hK : 0 < K6 := K6_pos
  have hpiK : Real.pi ≤ K6 := K6_ge_pi
  dsimp [cRef]
  exact (div_le_one₀ hK).mpr hpiK

/-- Norm of the Gamma function is nondecreasing when shifting the argument to the right by a
natural number, provided the imaginary part has modulus at least `1`. -/
lemma norm_Gamma_le_shift_nat (z : ℂ) {k : ℕ} (hk : 1 ≤ |z.im|) :
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + (k : ℂ))‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      let w : ℂ := z + (k : ℂ)
      have hw_ne : w ≠ 0 := by
        intro hw0
        have hre : w.im = z.im := by simp [w]
        have : |z.im| = 0 := by
          rw [← hre, hw0]
          simp
        have hnonneg : 0 ≤ |z.im| := abs_nonneg z.im
        linarith
      have hnorm : (1 : ℝ) ≤ ‖w‖ := by
        calc
          ‖w‖ ≥ |w.im| := Complex.abs_im_le_norm w
          _ = |z.im| := by simp [w]
          _ ≥ 1 := hk
      have hmain : ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ := by
        have hstep : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hw_ne
        calc
          ‖Complex.Gamma w‖ ≤ ‖w‖ * ‖Complex.Gamma w‖ := by
            exact le_mul_of_one_le_left (norm_nonneg _) hnorm
          _ = ‖w * Complex.Gamma w‖ := by rw [norm_mul]
          _ = ‖Complex.Gamma (w + 1)‖ := by rw [hstep]
      calc
        ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + (k : ℂ))‖ := ih
        _ = ‖Complex.Gamma w‖ := by simp [w]
        _ ≤ ‖Complex.Gamma (w + 1)‖ := hmain
        _ = ‖Complex.Gamma (z + (((k + 1 : ℕ) : ℂ)))‖ := by
          congr 1
          simp [w, Nat.cast_succ, add_assoc]

/-- Norm of Gamma at conjugated argument. -/
lemma norm_Gamma_conj (z : ℂ) : ‖Complex.Gamma (starRingEnd ℂ z)‖ = ‖Complex.Gamma z‖ := by
  rw [Complex.Gamma_conj, norm_conj]

/-- `‖sin(π·z)‖ ≤ e^{π·|z.im|}`. -/
lemma norm_sin_pi_le (z : ℂ) :
    ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
  have h1 := Commons.Analysis.SpecialFunctions.Gamma.norm_sin_le_exp_abs_im ((Real.pi : ℂ) * z)
  have him : (((Real.pi : ℂ) * z).im) = Real.pi * z.im := by
    rw [Complex.im_ofReal_mul]
  calc
    ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp |(((Real.pi : ℂ) * z).im)| := h1
    _ = Real.exp (Real.pi * |z.im|) := by
      rw [him]
      congr 1
      rw [abs_mul, abs_of_pos Real.pi_pos]

/-- Norm-form of Euler's reflection formula (from the commons). -/
lemma Gamma_mul_Gamma_one_sub_norm (z : ℂ) :
    ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  exact Commons.Analysis.SpecialFunctions.Gamma.Gamma_mul_Gamma_one_sub_norm z

/-- The complex sine does not vanish for `t ≠ 0` on the line `x + i·t`. -/
lemma sin_pi_ne_zero_of_ne_zero_im {x t : ℝ} (ht : t ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * ((x : ℂ) + I * (t : ℂ))) ≠ 0 := by
  let z : ℂ := (x : ℂ) + I * (t : ℂ)
  have hz_im : z.im = t := by simp [z]
  have harg : (((Real.pi : ℂ) * z).im) = Real.pi * t := by
    simp [Complex.im_ofReal_mul, hz_im]
  have him : (((Real.pi : ℂ) * z).im) ≠ 0 := by
    rw [harg]
    exact mul_ne_zero (ne_of_gt Real.pi_pos) ht
  exact Commons.Analysis.SpecialFunctions.Gamma.sin_ne_zero_of_im_ne_zero him

/-- `1 + |t| ≥ 1`. -/
lemma one_add_abs_ge_one (t : ℝ) : 1 ≤ 1 + |t| := by
  have h : 0 ≤ |t| := abs_nonneg t
  linarith

/-- Reference: real-part in `[1, 11]`, explicit Stirling-type upper bound with polynomial
slack `(1+|t|)^L`.  Generic in `L ∈ [1, 11]`. -/
lemma gamma_upper_main {L σ : ℝ} (hL11 : L ≤ 11) (h1 : 1 ≤ σ)
    (hσL : σ ≤ L) (t : ℝ) :
    ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ ≤
      (Mbig * Real.exp 1 * (Real.pi / 2) ^ L) * (1 + |t|) ^ L *
        Real.exp (-(Real.pi / 2) * |t|) := by
  have hσ11 : σ ≤ 11 := le_trans hσL hL11
  have hΓ := Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_explicit σ
    (lt_of_lt_of_le (by norm_num) h1) t
  have hM : Real.Gamma σ ≤ Mbig := by
    dsimp [Mbig]
    exact real_Gamma_le_M h1 hσ11
  have hpow1 : (Real.pi / 2) ^ σ ≤ (Real.pi / 2) ^ L := by
    refine Real.rpow_le_rpow_of_exponent_le ?_ hσL
    exact pi_div_two_ge_one
  have hpow2 : (1 + |t|) ^ σ ≤ (1 + |t|) ^ L := by
    refine Real.rpow_le_rpow_of_exponent_le (one_add_abs_ge_one t) hσL
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  have hE0 : 0 ≤ E := by dsimp [E]; exact Real.exp_nonneg _
  have hA : Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ ≤
      Mbig * Real.exp 1 * (Real.pi / 2) ^ L := by
    calc
      Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ
          ≤ Mbig * Real.exp 1 * (Real.pi / 2) ^ σ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hM (Real.exp_pos 1).le)
              (Real.rpow_nonneg (by positivity) σ)
      _ ≤ Mbig * Real.exp 1 * (Real.pi / 2) ^ L := by
            have hc : 0 ≤ Mbig * Real.exp 1 := mul_nonneg Mbig_pos.le (Real.exp_pos 1).le
            exact mul_le_mul_of_nonneg_left hpow1 hc
  have hq0 : 0 ≤ (1 + |t|) ^ σ := Real.rpow_nonneg (by positivity : 0 ≤ 1 + |t|) σ
  calc
    ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ ≤
        Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ * (1 + |t|) ^ σ * E := by
          simpa [E] using hΓ
    _ = (Real.Gamma σ * Real.exp 1 * (Real.pi / 2) ^ σ) * ((1 + |t|) ^ σ) * E := by ring
    _ ≤ (Mbig * Real.exp 1 * (Real.pi / 2) ^ L) * ((1 + |t|) ^ σ) * E := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hq0) hE0
    _ ≤ (Mbig * Real.exp 1 * (Real.pi / 2) ^ L) * ((1 + |t|) ^ L) * E := by
          have hc : 0 ≤ Mbig * Real.exp 1 * (Real.pi / 2) ^ L * E := by
            exact mul_nonneg (mul_nonneg (mul_nonneg Mbig_pos.le (Real.exp_pos 1).le)
              (Real.rpow_nonneg (by positivity) _)) hE0
          calc
            (Mbig * Real.exp 1 * (Real.pi / 2) ^ L) * ((1 + |t|) ^ σ) * E
                = (Mbig * Real.exp 1 * (Real.pi / 2) ^ L * E) * ((1 + |t|) ^ σ) := by ring
            _ ≤ (Mbig * Real.exp 1 * (Real.pi / 2) ^ L * E) * ((1 + |t|) ^ L) := by
                  exact mul_le_mul_of_nonneg_left hpow2 hc
            _ = (Mbig * Real.exp 1 * (Real.pi / 2) ^ L) * ((1 + |t|) ^ L) * E := by ring

end Commons.Analysis.Complex
namespace Commons.Analysis.Complex

/-- Uniform upper bound on a vertical strip `0 < u ≤ 6`, `|t| ≥ 1`. -/
lemma gamma_strip_upper (u t : ℝ) (hu0 : 0 < u) (hu6 : u ≤ 6) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((u : ℂ) + I * (t : ℂ))‖ ≤
      K6 * (1 + |t|) ^ (6 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) := by
  by_cases hu1 : 1 ≤ u
  · have hU := gamma_upper_main (hL11 := (by norm_num : (6 : ℝ) ≤ 11)) hu1 hu6 t
    simpa [K6] using hU
  · have hu1' : u < 1 := lt_of_not_ge hu1
    let uc : ℂ := (u : ℂ) + I * (t : ℂ)
    have huc_ne : uc ≠ 0 := by
      intro h0
      have hre : uc.im = t := by simp [uc]
      have : |t| = 0 := by
        rw [← hre, h0]
        simp
      linarith
    have hnorm : (1 : ℝ) ≤ ‖uc‖ := by
      calc
        ‖uc‖ ≥ |uc.im| := Complex.abs_im_le_norm uc
        _ = |t| := by simp [uc]
        _ ≥ 1 := ht
    have hshift : Complex.Gamma (uc + 1) = uc * Complex.Gamma uc :=
      Complex.Gamma_add_one uc huc_ne
    have harg : uc + 1 = (((u + 1 : ℝ) : ℂ) + I * (t : ℂ)) := by
      dsimp [uc]
      apply Complex.ext <;> simp <;> ring
    have hrel : ‖Complex.Gamma uc‖ ≤ ‖Complex.Gamma (uc + 1)‖ := by
      calc
        ‖Complex.Gamma uc‖ ≤ ‖uc‖ * ‖Complex.Gamma uc‖ := by
          exact le_mul_of_one_le_left (norm_nonneg _) hnorm
        _ = ‖uc * Complex.Gamma uc‖ := by rw [norm_mul]
        _ = ‖Complex.Gamma (uc + 1)‖ := by rw [hshift]
    have hσ12 : 1 ≤ u + 1 := by linarith
    have hσ6 : u + 1 ≤ 6 := by linarith
    have hU := gamma_upper_main (hL11 := (by norm_num : (6 : ℝ) ≤ 11)) hσ12 hσ6 t
    calc
      ‖Complex.Gamma ((u : ℂ) + I * (t : ℂ))‖ = ‖Complex.Gamma uc‖ := by simp [uc]
      _ ≤ ‖Complex.Gamma (uc + 1)‖ := hrel
      _ = ‖Complex.Gamma (((u + 1 : ℝ) : ℂ) + I * (t : ℂ))‖ := by rw [harg]
      _ ≤ K6 * (1 + |t|) ^ (6 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) := by
        simpa [K6] using hU

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

/-- Constant for the final upper bound. -/
noncomputable def K11 : ℝ := Mbig * Real.exp 1 * (Real.pi / 2) ^ (11 : ℝ)

lemma K11_pos : 0 < K11 := by
  dsimp [K11]
  exact mul_pos (mul_pos Mbig_pos (Real.exp_pos 1)) (Real.rpow_pos_of_pos (by positivity) _)

/-- Uniform upper bound for the whole strip `x ∈ [-5,5]`, `|y| ≥ 1` (polynomial slack
`(1+|y|)^11` and the sharp exponential factor). -/
lemma gamma_upper_all (x y : ℝ) (hx : x ∈ Set.Icc (-5) 5) (ht : 1 ≤ |y|) :
    ‖Complex.Gamma ((x : ℂ) + I * (y : ℂ))‖ ≤
      K11 * (1 + |y|) ^ (11 : ℝ) * Real.exp (-(Real.pi / 2) * |y|) := by
  let z : ℂ := (x : ℂ) + I * (y : ℂ)
  have hz_im : z.im = y := by simp [z]
  have hle := norm_Gamma_le_shift_nat z (k := 6) (by simpa [hz_im] using ht)
  let σ : ℝ := x + 6
  have hσ1 : 1 ≤ σ := by
    dsimp [σ]
    have hxlo : -5 ≤ x := hx.1
    linarith
  have hσ11 : σ ≤ 11 := by
    dsimp [σ]
    have hxhi : x ≤ 5 := hx.2
    linarith
  have hmain := gamma_upper_main (hL11 := (by norm_num : (11 : ℝ) ≤ 11)) hσ1 hσ11 y
  have harg : z + (6 : ℂ) = ((x + 6 : ℝ) : ℂ) + I * (y : ℂ) := by
    dsimp [z]
    apply Complex.ext <;> simp <;> ring
  calc
    ‖Complex.Gamma ((x : ℂ) + I * (y : ℂ))‖ = ‖Complex.Gamma z‖ := by simp [z]
    _ ≤ ‖Complex.Gamma (z + (6 : ℂ))‖ := hle
    _ = ‖Complex.Gamma (((x + 6 : ℝ) : ℂ) + I * (y : ℂ))‖ := by rw [harg]
    _ ≤ (Mbig * Real.exp 1 * (Real.pi / 2) ^ (11 : ℝ)) * (1 + |y|) ^ (11 : ℝ) *
          Real.exp (-(Real.pi / 2) * |y|) := by
            simpa [σ] using hmain
    _ = K11 * (1 + |y|) ^ (11 : ℝ) * Real.exp (-(Real.pi / 2) * |y|) := by
          simp [K11]

/-- Reflection-based lower bound for `x < 1` on the strip `x ∈ [-5, 1)`, `|t| ≥ 1`. -/
lemma gamma_lower_reflect (x t : ℝ) (hxlt : x < 1) (hx5 : -5 ≤ x) (ht : 1 ≤ |t|) :
    cRef * (1 + |t|) ^ (-6 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) ≤
      ‖Complex.Gamma ((x : ℂ) + I * (t : ℂ))‖ := by
  let z : ℂ := (x : ℂ) + I * (t : ℂ)
  let u : ℝ := 1 - x
  have hz_im : z.im = t := by simp [z]
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu6 : u ≤ 6 := by
    dsimp [u]
    have hxlo : -5 ≤ x := hx5
    linarith
  have ht_ne : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    norm_num at ht
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    simpa [z] using sin_pi_ne_zero_of_ne_zero_im (x := x) (t := t) ht_ne
  have hsin_pos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    exact norm_pos_iff.mpr hsin_ne
  have hsinle := norm_sin_pi_le z
  have hsinle' : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |t|) := by
    simpa [hz_im] using hsinle
  have hinv : Real.exp (-(Real.pi * |t|)) ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
    have hb : (Real.exp (Real.pi * |t|))⁻¹ ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
      exact (inv_le_inv₀ (by positivity : 0 < Real.exp (Real.pi * |t|)) hsin_pos).mpr hsinle'
    simpa [Real.exp_neg] using hb
  have hprod := Gamma_mul_Gamma_one_sub_norm z
  have hprod_ge : Real.pi * Real.exp (-(Real.pi * |t|)) ≤
      ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := by
    calc
      Real.pi * Real.exp (-(Real.pi * |t|)) ≤
          Real.pi * (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (le_of_lt Real.pi_pos)
      _ = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by ring
      _ = ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := by rw [← hprod]
  have hup0 := gamma_strip_upper u t hu0 hu6 ht
  have hconj : ‖Complex.Gamma (1 - z)‖ = ‖Complex.Gamma ((u : ℂ) + I * (t : ℂ))‖ := by
    have hc : starRingEnd ℂ ((u : ℂ) + I * (t : ℂ)) = 1 - z := by
      dsimp [z, u]
      apply Complex.ext <;> simp <;> ring
    calc
      ‖Complex.Gamma (1 - z)‖ =
          ‖Complex.Gamma (starRingEnd ℂ ((u : ℂ) + I * (t : ℂ)))‖ := by rw [← hc]
      _ = ‖Complex.Gamma ((u : ℂ) + I * (t : ℂ))‖ := norm_Gamma_conj _
  have hU : ‖Complex.Gamma (1 - z)‖ ≤ K6 * (1 + |t|) ^ (6 : ℝ) *
      Real.exp (-(Real.pi / 2) * |t|) := by
    rw [hconj]
    exact hup0
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  have hEpos : 0 < E := by dsimp [E]; exact Real.exp_pos _
  have hxpos : 0 < 1 + |t| := by positivity
  have hUpos : 0 < K6 * (1 + |t|) ^ (6 : ℝ) * E := by
    exact mul_pos (mul_pos K6_pos (Real.rpow_pos_of_pos hxpos _)) hEpos
  have hchain : Real.pi * Real.exp (-(Real.pi * |t|)) ≤
      ‖Complex.Gamma z‖ * (K6 * (1 + |t|) ^ (6 : ℝ) * E) := by
    calc
      Real.pi * Real.exp (-(Real.pi * |t|)) ≤
          ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := hprod_ge
      _ ≤ ‖Complex.Gamma z‖ * (K6 * (1 + |t|) ^ (6 : ℝ) * E) := by
        exact mul_le_mul_of_nonneg_left hU (norm_nonneg _)
  have hE2 : Real.exp (-(Real.pi * |t|)) = E * E := by
    dsimp [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hrr : (1 + |t|) ^ (-6 : ℝ) * (1 + |t|) ^ (6 : ℝ) = 1 := by
    rw [← Real.rpow_add hxpos]
    have hz : (-6 : ℝ) + 6 = 0 := by norm_num
    rw [hz, Real.rpow_zero]
  have hEE : Real.pi * (E * E) = Real.pi * Real.exp (-(Real.pi * |t|)) := by
    rw [hE2]
  have hLHSid : (cRef * (1 + |t|) ^ (-6 : ℝ) * E) *
      (K6 * (1 + |t|) ^ (6 : ℝ) * E) = Real.pi * (E * E) := by
    dsimp [cRef]
    have hb : K6 ≠ 0 := K6_pos.ne'
    have hx6 : (1 + |t|) ^ (6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hxpos _).ne'
    have hEn : E ≠ 0 := hEpos.ne'
    field_simp [hb, hx6, hEn]
    ring_nf
    exact hrr
  have hcross : (cRef * (1 + |t|) ^ (-6 : ℝ) * E) * (K6 * (1 + |t|) ^ (6 : ℝ) * E) ≤
      ‖Complex.Gamma z‖ * (K6 * (1 + |t|) ^ (6 : ℝ) * E) := by
    calc
      (cRef * (1 + |t|) ^ (-6 : ℝ) * E) * (K6 * (1 + |t|) ^ (6 : ℝ) * E)
          = Real.pi * Real.exp (-(Real.pi * |t|)) := hLHSid.trans hEE
      _ ≤ ‖Complex.Gamma z‖ * (K6 * (1 + |t|) ^ (6 : ℝ) * E) := hchain
  have hfinal : cRef * (1 + |t|) ^ (-6 : ℝ) * E ≤ ‖Complex.Gamma z‖ := by
    exact le_of_mul_le_mul_right hcross hUpos
  calc
    cRef * (1 + |t|) ^ (-6 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) ≤ ‖Complex.Gamma z‖ := by
      simpa [E] using hfinal
    _ = ‖Complex.Gamma ((x : ℂ) + I * (t : ℂ))‖ := by simp [z]

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

/-- Upper bound in the final form `B·E·(1+|y|)^20`. -/
lemma gamma_upper_final (x y : ℝ) (hx : x ∈ Set.Icc (-5) 5) (ht : 1 ≤ |y|) :
    ‖Complex.Gamma ((x : ℂ) + I * (y : ℂ))‖ ≤
      K11 * Real.exp (-(Real.pi / 2) * |y|) * (1 + |y|) ^ 20 := by
  have h1 := gamma_upper_all x y hx ht
  have hx0 : 0 ≤ 1 + |y| := by positivity
  have hbase : 1 ≤ 1 + |y| := one_add_abs_ge_one y
  have hq : (1 + |y|) ^ (11 : ℝ) ≤ (1 + |y|) ^ (20 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (11 : ℝ) ≤ 20)
  have hq20 : (1 + |y|) ^ (20 : ℝ) = (1 + |y|) ^ 20 := by
    exact Real.rpow_natCast (1 + |y|) 20
  let E : ℝ := Real.exp (-(Real.pi / 2) * |y|)
  have hE0 : 0 ≤ E := by dsimp [E]; exact Real.exp_nonneg _
  calc
    ‖Complex.Gamma ((x : ℂ) + I * (y : ℂ))‖ ≤ K11 * (1 + |y|) ^ (11 : ℝ) * E := by
      simpa [E] using h1
    _ ≤ K11 * (1 + |y|) ^ (20 : ℝ) * E := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq K11_pos.le) hE0
    _ = K11 * E * (1 + |y|) ^ 20 := by
      rw [hq20]
      ring

/-- Turn a `cRef·(1+|t|)^{-6}·E` lower bound into the division form of the final statement. -/
lemma gamma_lower_final_aux {z : ℂ} {t : ℝ} (ht : 1 ≤ |t|)
    (h : cRef * (1 + |t|) ^ (-6 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) ≤
      ‖Complex.Gamma z‖) :
    cRef * Real.exp (-(Real.pi / 2) * |t|) / (1 + |t|) ^ 20 ≤ ‖Complex.Gamma z‖ := by
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  have hbase : 1 ≤ 1 + |t| := one_add_abs_ge_one t
  have hE0 : 0 ≤ E := by dsimp [E]; exact Real.exp_nonneg _
  have hcmp : (1 + |t|) ^ (-(20 : ℝ)) ≤ (1 + |t|) ^ (-6 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (-(20 : ℝ)) ≤ (-6 : ℝ))
  have hpart : cRef * (1 + |t|) ^ (-(20 : ℝ)) * E ≤ cRef * (1 + |t|) ^ (-6 : ℝ) * E := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcmp cRef_pos.le) hE0
  have hconv : cRef * E * (1 + |t|) ^ (-(20 : ℝ)) = cRef * E / (1 + |t|) ^ 20 := by
    have hx0 : 0 ≤ 1 + |t| := by positivity
    rw [Real.rpow_neg hx0]
    rw [← Real.rpow_natCast]
    rfl
  have hA : cRef * E * (1 + |t|) ^ (-(20 : ℝ)) ≤ ‖Complex.Gamma z‖ := by
    calc
      cRef * E * (1 + |t|) ^ (-(20 : ℝ))
          = cRef * (1 + |t|) ^ (-(20 : ℝ)) * E := by ring
      _ ≤ cRef * (1 + |t|) ^ (-6 : ℝ) * E := hpart
      _ ≤ ‖Complex.Gamma z‖ := by
        simpa [E] using h
  rw [← hconv]
  exact hA

end Commons.Analysis.Complex
