import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound

open Complex
open scoped Real Topology BigOperators

noncomputable section
namespace Commons.NumberTheory.Zeta

/-- `‖cos (π * w / 2)‖ ≤ exp (π / 2 * |t|)` for `w = 1 - (σ + I*t)`. -/
private lemma cos_pi_two_bound_neg {σ t : ℝ} (w : ℂ) (hw : w = 1 - ((σ : ℂ) + I * (t : ℂ))) :
    ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
  have hcos : Complex.cos (↑Real.pi * w / 2) =
      Complex.sin (↑Real.pi * ((σ : ℂ) + I * (t : ℂ)) / 2) := by
    have h := Complex.sin_pi_div_two_sub (↑Real.pi * w / 2)
    rw [← h]
    congr 1
    rw [hw]
    ring
  rw [hcos]
  have hpi := Commons.Analysis.Complex.norm_sin_pi_le (((σ : ℂ) + I * (t : ℂ)) / 2)
  have hsimp : ‖Complex.sin (↑Real.pi * (((σ : ℂ) + I * (t : ℂ)) / 2))‖ =
      ‖Complex.sin (↑Real.pi * ((σ : ℂ) + I * (t : ℂ)) / 2)‖ := by
    congr 1
    ring
  have him : |((((σ : ℂ) + I * (t : ℂ)) / 2).im)| = |t| / 2 := by
    have h1 : ((((σ : ℂ) + I * (t : ℂ)) / 2).im) = t / 2 := by simp
    rw [h1]
    rw [abs_div]
    simp
  rw [← hsimp]
  calc
    ‖Complex.sin (↑Real.pi * (((σ : ℂ) + I * (t : ℂ)) / 2))‖ ≤
        Real.exp (Real.pi * |((((σ : ℂ) + I * (t : ℂ)) / 2)).im|) := by simpa using hpi
    _ = Real.exp ((Real.pi / 2) * |t|) := by
      rw [him]
      congr 1
      ring

/-- Zeta growth on the strip `-2 ≤ Re s ≤ -1`, `|t| ≥ 1`, polynomial bound of degree 12. -/
theorem zeta_strip_polyGrowth_neg :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ t : ℝ, -2 ≤ σ → σ ≤ -1 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 12 := by
  rcases zeta_strip_polyGrowth with ⟨Cps, hCps, hCpsSpec⟩
  let K6 : ℝ := Commons.Analysis.Complex.K6
  have hK6 : 0 < K6 := by simpa [K6] using Commons.Analysis.Complex.K6_pos
  have hC : 0 < 2 * K6 * Cps := by positivity
  refine ⟨2 * K6 * Cps, hC, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let u : ℝ := 1 - σ
  let w : ℂ := 1 - s
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hu6 : u ≤ 6 := by dsimp [u]; linarith
  have hu_lo : -1 ≤ u := by dsimp [u]; linarith
  have hu_le3 : u ≤ 3 := by dsimp [u]; linarith
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  have hwim : w.im = -t := by dsimp [w, s]; simp
  have hw_ne : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have him := congrArg Complex.im hn
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    norm_num at ht
  have hw1 : w ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    norm_num at ht
  have hFE0 := riemannZeta_one_sub (s := w) hw_ne hw1
  have hsw : s = 1 - w := by dsimp [w, s]; ring
  have hFE : riemannZeta s =
      2 * (2 * ↑Real.pi) ^ (-w) * Complex.Gamma w * Complex.cos (↑Real.pi * w / 2) *
        riemannZeta w := by
    simpa [hsw] using hFE0
  have htwon : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hwform : w = (u : ℂ) + I * ((-t : ℝ) : ℂ) := by
    dsimp [w, s, u]
    apply Complex.ext <;> simp <;> ring
  -- factor: (2π)^{-w}
  have hb2π : ((2 * Real.pi : ℝ) : ℂ) = (2 : ℂ) * ↑Real.pi := by
    rw [Complex.ofReal_mul]
    norm_num
  have hre : (-w).re = σ - 1 := by dsimp [w, s]; simp
  have hpow2 : ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ = (2 * Real.pi : ℝ) ^ (σ - 1) := by
    rw [← hb2π]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (2 * Real.pi : ℝ)) (-w)]
    rw [hre]
  have hpow2le : ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ ≤ 1 := by
    rw [hpow2]
    have hx : 1 ≤ 2 * Real.pi := by
      have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      nlinarith
    have hle : σ - 1 ≤ 0 := by linarith
    calc
      (2 * Real.pi : ℝ) ^ (σ - 1) ≤ (2 * Real.pi : ℝ) ^ (0 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hx hle
      _ = 1 := by rw [Real.rpow_zero]
  -- factor: Gamma
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  let F : ℝ := Real.exp ((Real.pi / 2) * |t|)
  have hEe : E * F = 1 := by
    dsimp [E, F]
    rw [← Real.exp_add]
    rw [show (-(Real.pi / 2)) * |t| + (Real.pi / 2) * |t| = 0 by ring]
    rw [Real.exp_zero]
  have hGn : ‖Complex.Gamma w‖ ≤ K6 * (1 + |t|) ^ (6 : ℝ) * E := by
    have h := Commons.Analysis.Complex.gamma_strip_upper u (-t) hu_pos hu6 (by simpa using ht)
    rw [hwform]
    simpa [E] using h
  -- factor: cos
  have hcos : ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ F := by
    have hb := cos_pi_two_bound_neg w (by dsimp [w, s])
    simpa [F] using hb
  -- factor: zeta at w
  have hzw : ‖riemannZeta w‖ ≤ Cps * (|t| + 3) ^ 4 := by
    have h := hCpsSpec u (-t) hu_lo hu_le3 (by simpa using ht)
    rw [hwform]
    simpa using h
  have hmain : ‖riemannZeta s‖ ≤ 2 * K6 * Cps * (1 + |t|) ^ (6 : ℝ) * (|t| + 3) ^ 4 := by
    have hsplit : ‖riemannZeta s‖ =
        ‖(2 : ℂ)‖ * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
          ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := by
      rw [hFE]
      simp only [norm_mul]
    calc
      ‖riemannZeta s‖ =
          ‖(2 : ℂ)‖ * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
            ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := hsplit
      _ = 2 * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
            ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := by rw [htwon]
      _ ≤ 2 * 1 * (K6 * (1 + |t|) ^ (6 : ℝ) * E) * F * (Cps * (|t| + 3) ^ 4) := by
        gcongr
      _ = 2 * K6 * Cps * (1 + |t|) ^ (6 : ℝ) * (|t| + 3) ^ 4 * (E * F) := by
        ring
      _ = 2 * K6 * Cps * (1 + |t|) ^ (6 : ℝ) * (|t| + 3) ^ 4 := by
        rw [hEe]
        ring
  have hconst0 : 0 ≤ 2 * K6 * Cps := le_of_lt hC
  have hmain' : ‖riemannZeta s‖ ≤ 2 * K6 * Cps * (1 + |t|) ^ 6 * (|t| + 3) ^ 4 := by
    simpa [Real.rpow_natCast] using hmain
  have hmain10 : ‖riemannZeta s‖ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 10 := by
    calc
      ‖riemannZeta s‖ ≤ 2 * K6 * Cps * (1 + |t|) ^ 6 * (|t| + 3) ^ 4 := hmain'
      _ = 2 * K6 * Cps * ((1 + |t|) ^ 6 * (|t| + 3) ^ 4) := by ring
      _ ≤ 2 * K6 * Cps * ((|t| + 3) ^ 6 * (|t| + 3) ^ 4) := by
        have hq : (1 + |t|) ^ 6 ≤ (|t| + 3) ^ 6 := by
          exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t|)
            (by nlinarith : 1 + |t| ≤ |t| + 3) 6
        have hq4 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hq4) hconst0
      _ = (2 * K6 * Cps) * (|t| + 3) ^ 10 := by
        rw [← pow_add]
  have ht13 : 1 ≤ |t| + 3 := by nlinarith [ht]
  have hfin : ‖riemannZeta s‖ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 12 := by
    calc
      ‖riemannZeta s‖ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 10 := hmain10
      _ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 12 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht13 (by norm_num : (10 : ℕ) ≤ 12)) hconst0
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ = ‖riemannZeta s‖ := by simp [s]
    _ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 12 := hfin

end Commons.NumberTheory.Zeta
