import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_real_growth
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_le_norm_gammaR_re

open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Real part of the negated half: `re (-(x:ℂ)/2) = -(x/2)`. -/
lemma re_neg_half (x : ℝ) : (-(x : ℂ) / 2).re = -(x / 2) := by
  rw [Complex.div_re, Complex.neg_re]
  norm_num
  ring

/-- The norm of `Gammaℝ` on the positive real axis: `‖Gammaℝ x‖ = π^(-x/2) · Γ(x/2)`. -/
lemma norm_gammaR_real {x : ℝ} (hx : 0 < x) :
    ‖Complex.Gammaℝ (x : ℂ)‖ = Real.pi ^ (-(x / 2)) * Real.Gamma (x / 2) := by
  rw [Complex.Gammaℝ_def]
  rw [norm_mul]
  have hbase : ‖(Real.pi : ℂ) ^ (-(x : ℂ) / 2)‖ = Real.pi ^ (-(x / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    exact re_neg_half x
  have harg : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by
    norm_num
  have hΓ : ‖Complex.Gamma ((x : ℂ) / 2)‖ = Real.Gamma (x / 2) := by
    rw [harg, Complex.Gamma_ofReal]
    exact Complex.norm_of_nonneg (le_of_lt (Real.Gamma_pos_of_pos (by linarith : 0 < x / 2)))
  rw [hbase, hΓ]

/-- `π^(-x/2) ≤ 1` for `x ≥ 0`. -/
lemma rpow_pi_neg_half_le_one {x : ℝ} (hx : 0 ≤ x) :
    Real.pi ^ (-(x / 2)) ≤ 1 := by
  rw [Real.rpow_def_of_pos Real.pi_pos]
  rw [← Real.exp_zero]
  rw [Real.exp_le_exp]
  have hlogpi : 0 ≤ Real.log Real.pi := by
    exact Real.log_nonneg (by have hp := Real.pi_gt_three; linarith)
  have hnonpos : -(x / 2) ≤ 0 := by linarith
  calc
    Real.log Real.pi * (-(x / 2)) ≤ Real.log Real.pi * 0 := by
      exact mul_le_mul_of_nonneg_left hnonpos hlogpi
    _ = 0 := by ring

/-- Γ is bounded on `[1/4, 1]`: `Γ u ≤ 32/5`.  (Proof: two applications of the
functional equation `Γ(t+1) = t·Γ(t)` bring the argument into `[9/4, 3]`, where
`Γ` is increasing and `Γ 3 = 2`.) -/
lemma real_gamma_le_thirtytwo_fifths {u : ℝ} (hu1 : 1 / 4 ≤ u) (hu2 : u ≤ 1) :
    Real.Gamma u ≤ 32 / 5 := by
  have hu_pos : 0 < u := by linarith
  have hu1_ne : u ≠ 0 := ne_of_gt hu_pos
  have hrec1 : Real.Gamma (u + 1) = u * Real.Gamma u := Real.Gamma_add_one hu1_ne
  have hrec2 : Real.Gamma (u + 2) = (u + 1) * Real.Gamma (u + 1) := by
    have hs : u + 1 ≠ 0 := by linarith
    calc
      Real.Gamma (u + 2) = Real.Gamma ((u + 1) + 1) := by congr 1; ring
      _ = (u + 1) * Real.Gamma (u + 1) := Real.Gamma_add_one (s := u + 1) hs
  have hG2 : Real.Gamma (u + 2) = (u + 1) * (u * Real.Gamma u) := by
    rw [hrec2, hrec1]
  have hu2mem : u + 2 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have h3mem : (3 : ℝ) ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    norm_num
  have hmono : Real.Gamma (u + 2) ≤ Real.Gamma 3 := by
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn hu2mem h3mem (by linarith)
  have hG3 : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial (n := 2) using 1 <;> norm_num
  have hprod_pos : 0 < (u + 1) * u := by positivity
  have hΓu_eq : Real.Gamma u = Real.Gamma (u + 2) / ((u + 1) * u) := by
    rw [hG2]
    field_simp [ne_of_gt hprod_pos]
  have hΓu_le : Real.Gamma u ≤ Real.Gamma 3 / ((u + 1) * u) := by
    rw [hΓu_eq]
    exact div_le_div_of_nonneg_right hmono (le_of_lt hprod_pos)
  have hu1_5 : (5 / 4 : ℝ) ≤ u + 1 := by linarith
  have hden : (5 / 16 : ℝ) ≤ (u + 1) * u := by
    calc
      (5 / 16 : ℝ) = (5 / 4) * (1 / 4) := by norm_num
      _ ≤ (u + 1) * u := by
        exact mul_le_mul hu1_5 hu1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith : (0 : ℝ) ≤ u + 1)
  calc
    Real.Gamma u ≤ Real.Gamma 3 / ((u + 1) * u) := hΓu_le
    _ = (2 : ℝ) / ((u + 1) * u) := by rw [hG3]
    _ ≤ 2 / (5 / 16) := by
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 5 / 16) hden
    _ = 32 / 5 := by norm_num

/-- `Gammaℝ` is uniformly bounded on `[1/2, 2]`: ≤ 32/5. -/
lemma norm_gammaR_le_of_le_two {x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 2) :
    ‖Complex.Gammaℝ (x : ℂ)‖ ≤ 32 / 5 := by
  have hxpos : 0 < x := by linarith
  rw [norm_gammaR_real hxpos]
  have hpi : Real.pi ^ (-(x / 2)) ≤ 1 := rpow_pi_neg_half_le_one (by linarith : 0 ≤ x)
  have hΓpos : 0 ≤ Real.Gamma (x / 2) :=
    le_of_lt (Real.Gamma_pos_of_pos (by linarith : 0 < x / 2))
  calc
    Real.pi ^ (-(x / 2)) * Real.Gamma (x / 2) ≤ 1 * Real.Gamma (x / 2) := by
      exact mul_le_mul_of_nonneg_right hpi hΓpos
    _ = Real.Gamma (x / 2) := by ring
    _ ≤ 32 / 5 := real_gamma_le_thirtytwo_fifths (by linarith : 1 / 4 ≤ x / 2) (by linarith : x / 2 ≤ 1)

/-- `Gammaℝ` growth for `x ≥ 2`, with the explicit constant one:
`‖Gammaℝ x‖ ≤ exp((x/2)·log(x/2 + 2))`. -/
lemma norm_gammaR_le_exp_growth {x : ℝ} (hx : 2 ≤ x) :
    ‖Complex.Gammaℝ (x : ℂ)‖ ≤ Real.exp ((x / 2) * Real.log (x / 2 + 2)) := by
  have hxpos : 0 < x := by linarith
  have hx2pos : 0 < x / 2 := by linarith
  rw [norm_gammaR_real hxpos]
  have hpi : Real.pi ^ (-(x / 2)) ≤ 1 := rpow_pi_neg_half_le_one (by linarith : 0 ≤ x)
  have hΓpos : 0 ≤ Real.Gamma (x / 2) := le_of_lt (Real.Gamma_pos_of_pos hx2pos)
  calc
    Real.pi ^ (-(x / 2)) * Real.Gamma (x / 2) ≤ 1 * Real.Gamma (x / 2) := by
      exact mul_le_mul_of_nonneg_right hpi hΓpos
    _ = Real.Gamma (x / 2) := by ring
    _ ≤ Real.exp ((x / 2) * Real.log (x / 2 + 2)) := by
      exact real_gamma_growth (by linarith : 1 ≤ x / 2)

/-- `exp 3 > 32/5`, from `e > 2`. -/
lemma exp_three_gt_thirtytwo_fifths : (32 / 5 : ℝ) < Real.exp 3 := by
  have h3 : (Real.exp (3 : ℝ)) = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num]
    exact Real.exp_nat_mul (x := 1) (n := 3)
  rw [h3]
  calc
    (32 / 5 : ℝ) < (2 : ℝ) ^ 3 := by norm_num
    _ < (Real.exp 1) ^ 3 := by
      exact pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (3 : ℕ) ≠ 0)

/-- Monotonicity of the growth exponent for `x ≥ 2`. -/
lemma half_growth_le_two_growth {x : ℝ} (hx : 2 ≤ x) :
    (x / 2) * Real.log (x / 2 + 2) ≤
      2 * (x + 1) * (Real.log (x + 2) + 1) := by
  have hx2 : 0 ≤ x / 2 := by linarith
  have hlog1 : Real.log (x / 2 + 2) ≤ Real.log (x + 2) := by
    exact Real.log_le_log (by linarith : 0 < x / 2 + 2) (by linarith)
  have hlog2 : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith : 1 ≤ x + 2)
  have hlog2p1 : 0 ≤ Real.log (x + 2) + 1 := by linarith
  have hx2le : x / 2 ≤ x + 1 := by linarith
  have hx1le : x + 1 ≤ 2 * (x + 1) := by nlinarith
  calc
    (x / 2) * Real.log (x / 2 + 2) ≤ (x / 2) * Real.log (x + 2) := by
      exact mul_le_mul_of_nonneg_left hlog1 hx2
    _ ≤ (x / 2) * (Real.log (x + 2) + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hx2
    _ ≤ (x + 1) * (Real.log (x + 2) + 1) := by
      exact mul_le_mul_of_nonneg_right hx2le hlog2p1
    _ ≤ 2 * (x + 1) * (Real.log (x + 2) + 1) := by
      exact mul_le_mul_of_nonneg_right hx1le hlog2p1

/-- Lower bound `3 ≤ 2·(x+1)·(log(x+2)+1)` for `x ≥ 1/2`. -/
lemma three_le_two_mul_growth {x : ℝ} (hx : 1 / 2 ≤ x) :
    3 ≤ 2 * (x + 1) * (Real.log (x + 2) + 1) := by
  have hlog2 : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith : 1 ≤ x + 2)
  have hlogp1 : 1 ≤ Real.log (x + 2) + 1 := by linarith
  have htwo : 3 ≤ 2 * (x + 1) := by nlinarith
  calc
    3 = 3 * 1 := by ring
    _ ≤ 2 * (x + 1) * (Real.log (x + 2) + 1) := by
      exact mul_le_mul htwo hlogp1 (by norm_num : (0 : ℝ) ≤ 1) (by nlinarith : (0 : ℝ) ≤ 2 * (x + 1))

/-- **Real-axis growth of the norm of `Gammaℝ`**: there is a constant `c ≥ 0` such that
`‖Gammaℝ(x)‖ ≤ exp (c·(x+1)·(log (x+2) + 1))` for every real `x ≥ 1/2`.

Here `Gammaℝ s = π^(-s/2) · Γ(s/2)` (`Complex.Gammaℝ_def`).  For `x ≥ 2` use
`gamma_real_growth` at the point `x/2 ≥ 1` together with
`‖π^(-(x:ℂ)/2)‖ = π^(-x/2) ≤ 1` (from `Complex.norm_cpow_eq_rpow_re_of_pos`).
For `1/2 ≤ x ≤ 2` bound `‖Γ(x/2)‖` by an absolute constant (`Γ` is decreasing on
`(0, Γ⁻¹... ]`; a crude finite bound like `‖Γ(u)‖ ≤ 10` for `1/4 ≤ u ≤ 1` is fine —
use e.g. the integral representation or monotonicity facts available in Mathlib).
-/
theorem gammaR_real_growth :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 1 / 2 ≤ x →
      ‖Complex.Gammaℝ (x : ℂ)‖ ≤ Real.exp (c * (x + 1) * (Real.log (x + 2) + 1)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro x hx
  by_cases hx2 : x ≤ 2
  · have hbound : ‖Complex.Gammaℝ (x : ℂ)‖ ≤ 32 / 5 := norm_gammaR_le_of_le_two hx hx2
    have hE : (32 / 5 : ℝ) ≤
        Real.exp (2 * (x + 1) * (Real.log (x + 2) + 1)) := by
      have h3 : 3 ≤ 2 * (x + 1) * (Real.log (x + 2) + 1) := three_le_two_mul_growth hx
      exact le_trans (le_of_lt exp_three_gt_thirtytwo_fifths) (Real.exp_le_exp.mpr h3)
    exact hbound.trans hE
  · have hxbig : 2 ≤ x := by linarith
    have hbound := norm_gammaR_le_exp_growth hxbig
    have hineq := half_growth_le_two_growth hxbig
    exact hbound.trans (Real.exp_le_exp.mpr hineq)

end Commons.Analysis.SpecialFunctions.Gamma