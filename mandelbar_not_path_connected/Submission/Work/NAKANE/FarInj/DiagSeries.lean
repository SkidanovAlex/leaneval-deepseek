/-
# The series estimate for the diagonal Lipschitz bound of the Böttcher series

`bottcherSeries c z = Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] z))`,
`normFactor c w = pMap c w / w^4`, `pMap c w = (w² + c̄)² + c`.

This file proves the analytical heart of

`‖bottcherSeries x x - bottcherSeries y y‖ ≤ C ‖x - y‖ / ‖x‖²`   (`‖x‖ ≥ 256`, `‖y - x‖ ≤ ‖x‖/2`):

term by term, `‖log (normFactor x (z n)) - log (normFactor y (w n))‖` is controlled by

* `‖normFactor x (z_n) - normFactor y (z_n)‖` — the *parameter* moves, the point is fixed;
  handled by the exact expansion `normFactor c z - 1 = 2c̄/z² + (c̄²+c)/z⁴`;
* `‖normFactor y (z_n) - normFactor y (w_n)‖` — the *point* moves, the parameter is fixed;
  handled by the orbit separation `‖z_n - w_n‖ ≤ 32^n (‖x-y‖/‖x‖) (‖z_n‖ + ‖w_n‖)`.

The dominant contribution is the very first term (`n = 0`), which is exactly the leading
`c̄/(2z²)` behaviour of the Böttcher series differentiated along the diagonal.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.NAKANE.FarInj.DiagFoundation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ComplexConjugate Topology
open Work.Bottcher

namespace Work.NAKANE.FarInj

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-! ## Geometric series -/

private lemma summable_quarter_pow_succ : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_right (1 / 4)

private lemma tsum_quarter_pow_succ :
    (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1)) = 1 / 3 := by
  have h : (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1))
      = fun n => (1 / 4 : ℝ) ^ n * (1 / 4) := by
    funext n; rw [pow_succ]
  rw [h, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)]
  norm_num

private lemma summable_quarter_succ_mul_half :
    Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n) := by
  have h : (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n)
      = fun n => (1 / 4 : ℝ) * (1 / 8) ^ n := by
    funext n
    rw [pow_succ, show (1 / 4 : ℝ) ^ n * (1 / 4) * (1 / 2) ^ n
        = (1 / 4) * ((1 / 4) ^ n * (1 / 2) ^ n) by ring,
      show (1 / 4 : ℝ) ^ n * (1 / 2) ^ n = (1 / 8) ^ n by
        rw [← mul_pow, show ((1 / 4 : ℝ) * (1 / 2)) = 1 / 8 by norm_num]]
  rw [h]
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1)).mul_left (1 / 4)

private lemma tsum_quarter_succ_mul_half :
    (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n) = 2 / 7 := by
  have h : (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n)
      = fun n => (1 / 4 : ℝ) * (1 / 8) ^ n := by
    funext n
    rw [pow_succ, show (1 / 4 : ℝ) ^ n * (1 / 4) * (1 / 2) ^ n
        = (1 / 4) * ((1 / 4) ^ n * (1 / 2) ^ n) by ring,
      show (1 / 4 : ℝ) ^ n * (1 / 2) ^ n = (1 / 8) ^ n by
        rw [← mul_pow, show ((1 / 4 : ℝ) * (1 / 2)) = 1 / 8 by norm_num]]
  rw [h, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1)]
  norm_num

/-- A sequence whose successive terms shrink by at least the factor `q ≥ 0` is dominated by
the geometric sequence with ratio `q`. -/
private lemma geom_ratio_le {a : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ n, a (n + 1) ≤ q * a n) (n : ℕ) : a n ≤ a 0 * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc a (n + 1) ≤ q * a n := hstep n
        _ ≤ q * (a 0 * q ^ n) := mul_le_mul_of_nonneg_left ih hq
        _ = a 0 * q ^ (n + 1) := by rw [pow_succ]; ring

/-- `‖(c : ℂ)‖ = c` for a nonnegative real `c`. -/
private lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private lemma norm_two : ‖(2 : ℂ)‖ = 2 := by norm_num

/-- `‖((1/4 : ℝ) : ℂ) ^ (n+1)‖ = (1/4) ^ (n+1)`. -/
private lemma norm_quarter_pow (n : ℕ) :
    ‖(((1 / 4 : ℝ) : ℂ) ^ (n + 1))‖ = (1 / 4 : ℝ) ^ (n + 1) := by
  rw [norm_pow, norm_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]

/-! ## The main series estimate -/

/-- **Diagonal Lipschitz estimate for the Böttcher series, series part.**
Assuming the orbit-separation estimate `horb`, the diagonal Böttcher series differs by at
most `64 ‖x - y‖ / ‖x‖²` on the region `‖x‖ ≥ 256`, `‖y - x‖ ≤ ‖x‖/2`. -/
lemma bottcherSeries_diag_sub_le (x y : ℂ) (hA : 256 ≤ ‖x‖) (hδ : ‖y - x‖ ≤ ‖x‖ / 2)
    (horb : ∀ n, ‖(pMap x)^[n] x - (pMap y)^[n] y‖
      ≤ 32 ^ n * (‖x - y‖ / ‖x‖)
        * (‖(pMap x)^[n] x‖ + ‖(pMap y)^[n] y‖)) :
    ‖bottcherSeries x x - bottcherSeries y y‖ ≤ 64 * ‖x - y‖ / ‖x‖ ^ 2 := by
  have hAx : (0 : ℝ) < ‖x‖ := by linarith
  have hδ' : ‖x - y‖ ≤ ‖x‖ / 2 := by rw [← norm_sub_rev y x]; exact hδ
  have hyge : ‖x‖ / 2 ≤ ‖y‖ := by
    have h := norm_sub_norm_le x y
    linarith
  have hyle : ‖y‖ ≤ 3 * ‖x‖ / 2 := by
    have h := norm_sub_norm_le y x
    linarith
  have hδnn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  let z : ℕ → ℂ := fun n => (pMap x)^[n] x
  let w : ℕ → ℂ := fun n => (pMap y)^[n] y
  have hzb : ∀ n, 16 ≤ ‖z n‖ ∧ 16 ≤ ‖w n‖ ∧ ‖x‖ ≤ ‖z n‖ ∧ ‖y‖ ≤ ‖w n‖ := by
    intro n
    obtain ⟨b1, b2, b3, b4⟩ := orbit_bounds x y hA hδ n
    have e1 : z n = (pMap x)^[n] x := rfl
    have e2 : w n = (pMap y)^[n] y := rfl
    rw [e1, e2]
    exact ⟨b1, b2, b3, b4⟩
  let T : ℕ → ℝ := fun n => min ‖z n‖ ‖w n‖
  have hTA : ∀ n, ‖x‖ / 2 ≤ T n := by
    intro n
    obtain ⟨b1, b2, b3, b4⟩ := hzb n
    exact le_min (by linarith) (by linarith)
  have hTpos : ∀ n, (3 : ℝ) ≤ T n := by intro n; linarith [hTA n]
  have hTstep : ∀ n, T n ^ 4 / 2 ≤ T (n + 1) := by
    intro n
    obtain ⟨b1, b2, b3, b4⟩ := hzb n
    have hzsucc : z (n + 1) = pMap x (z n) := by
      simp only [z]; rw [Function.iterate_succ_apply']
    have hwsucc : w (n + 1) = pMap y (w n) := by
      simp only [w]; rw [Function.iterate_succ_apply']
    have g1 : ‖z n‖ ^ 4 / 2 ≤ ‖z (n + 1)‖ := by
      have h := (norm_pMap_ge x (z n) b1 (by linarith)).1
      rwa [hzsucc]
    have g2 : ‖w n‖ ^ 4 / 2 ≤ ‖w (n + 1)‖ := by
      have h := (norm_pMap_ge y (w n) b2 (by linarith)).1
      rwa [hwsucc]
    have hmin4 : (min ‖z n‖ ‖w n‖) ^ 4 / 2 = min (‖z n‖ ^ 4 / 2) (‖w n‖ ^ 4 / 2) := by
      rcases le_total ‖z n‖ ‖w n‖ with h | h
      · rw [min_eq_left h]
        have h' : ‖z n‖ ^ 4 / 2 ≤ ‖w n‖ ^ 4 / 2 := by
          have hp := pow_le_pow_left₀ (norm_nonneg (z n)) h 4
          linarith
        rw [min_eq_left h']
      · rw [min_eq_right h]
        have h' : ‖w n‖ ^ 4 / 2 ≤ ‖z n‖ ^ 4 / 2 := by
          have hp := pow_le_pow_left₀ (norm_nonneg (w n)) h 4
          linarith
        rw [min_eq_right h']
    show T n ^ 4 / 2 ≤ T (n + 1)
    rw [show T n = min ‖z n‖ ‖w n‖ from rfl, hmin4,
      show T (n + 1) = min ‖z (n + 1)‖ ‖w (n + 1)‖ from rfl]
    exact min_le_min g1 g2
  -- geometric bounds on `32^n / T n ^ 2` and `32^n / T n ^ 4`
  have hT0 : ‖x‖ / 2 ≤ T 0 := hTA 0
  have hT0pos : (0 : ℝ) < T 0 := by linarith [hTpos 0]
  have hinv2 : 1 / T 0 ^ 2 ≤ 4 / ‖x‖ ^ 2 := by
    have hden : ‖x‖ ^ 2 / 4 ≤ T 0 ^ 2 := by
      have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ ‖x‖ / 2) hT0 2
      nlinarith [hp]
    rw [show (4 : ℝ) / ‖x‖ ^ 2 = 1 / (‖x‖ ^ 2 / 4) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hinv4 : 1 / T 0 ^ 4 ≤ 16 / ‖x‖ ^ 4 := by
    have hden : ‖x‖ ^ 4 / 16 ≤ T 0 ^ 4 := by
      have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ ‖x‖ / 2) hT0 4
      nlinarith [hp]
    rw [show (16 : ℝ) / ‖x‖ ^ 4 = 1 / (‖x‖ ^ 4 / 16) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hbstep : ∀ n, 32 ^ (n + 1) / T (n + 1) ^ 2 ≤ (1 / 2) * (32 ^ n / T n ^ 2) := by
    intro n
    have hp : (0 : ℝ) < T n := by linarith [hTpos n]
    have hdn : (0 : ℝ) < T (n + 1) := by linarith [hTA (n + 1)]
    have h6 : (256 : ℝ) ≤ T n ^ 6 := by
      have h4 : (3 : ℝ) ≤ T n := hTpos n
      have hp4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 : ℝ)) h4 6
      norm_num at hp4; linarith
    have hkey : 64 * T n ^ 2 ≤ T (n + 1) ^ 2 := by
      have h1 : (T n ^ 4 / 2) ^ 2 ≤ T (n + 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hTstep n) 2
      have h2 : (T n ^ 4 / 2) ^ 2 = T n ^ 8 / 4 := by ring
      have h3 : T n ^ 2 * 256 ≤ T n ^ 2 * T n ^ 6 :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      nlinarith [h1, h2.le, h2.ge, h3]
    rw [pow_succ, div_le_iff₀ (pow_pos hdn 2)]
    have hrw : (1 / 2) * (32 ^ n / T n ^ 2) * T (n + 1) ^ 2
        = 32 ^ n * T (n + 1) ^ 2 / (2 * T n ^ 2) := by
      field_simp
    rw [hrw, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * T n ^ 2)]
    nlinarith [hkey, show (0 : ℝ) < 32 ^ n by positivity]
  have hdstep : ∀ n, 32 ^ (n + 1) / T (n + 1) ^ 4 ≤ (1 / 2) * (32 ^ n / T n ^ 4) := by
    intro n
    have hp : (0 : ℝ) < T n := by linarith [hTpos n]
    have hdn : (0 : ℝ) < T (n + 1) := by linarith [hTA (n + 1)]
    have h12 : (1024 : ℝ) ≤ T n ^ 12 := by
      have h4 : (3 : ℝ) ≤ T n := hTpos n
      have hp4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 : ℝ)) h4 12
      norm_num at hp4; linarith
    have hkey : 64 * T n ^ 4 ≤ T (n + 1) ^ 4 := by
      have h1 : (T n ^ 4 / 2) ^ 4 ≤ T (n + 1) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (hTstep n) 4
      have h2 : (T n ^ 4 / 2) ^ 4 = T n ^ 16 / 16 := by ring
      have h3 : T n ^ 4 * 1024 ≤ T n ^ 4 * T n ^ 12 :=
        mul_le_mul_of_nonneg_left h12 (by positivity)
      nlinarith [h1, h2.le, h2.ge, h3]
    rw [pow_succ, div_le_iff₀ (pow_pos hdn 4)]
    have hrw : (1 / 2) * (32 ^ n / T n ^ 4) * T (n + 1) ^ 4
        = 32 ^ n * T (n + 1) ^ 4 / (2 * T n ^ 4) := by
      field_simp
    rw [hrw, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * T n ^ 4)]
    nlinarith [hkey, show (0 : ℝ) < 32 ^ n by positivity]
  have hb : ∀ n, 32 ^ n / T n ^ 2 ≤ (4 / ‖x‖ ^ 2) * (1 / 2) ^ n := by
    intro n
    calc 32 ^ n / T n ^ 2 ≤ (32 ^ 0 / T 0 ^ 2) * (1 / 2) ^ n :=
          geom_ratio_le (a := fun m => 32 ^ m / T m ^ 2) (q := 1 / 2) (by norm_num) hbstep n
      _ = (1 / T 0 ^ 2) * (1 / 2) ^ n := by norm_num
      _ ≤ (4 / ‖x‖ ^ 2) * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_right hinv2 (by positivity)
  have hd : ∀ n, 32 ^ n / T n ^ 4 ≤ (16 / ‖x‖ ^ 4) * (1 / 2) ^ n := by
    intro n
    calc 32 ^ n / T n ^ 4 ≤ (32 ^ 0 / T 0 ^ 4) * (1 / 2) ^ n :=
          geom_ratio_le (a := fun m => 32 ^ m / T m ^ 4) (q := 1 / 2) (by norm_num) hdstep n
      _ = (1 / T 0 ^ 4) * (1 / 2) ^ n := by norm_num
      _ ≤ (16 / ‖x‖ ^ 4) * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_right hinv4 (by positivity)
  -- the orbits avoid `0`
  have hz_ne : ∀ n, z n ≠ 0 := by
    intro n h
    have := (hzb n).1
    rw [h, norm_zero] at this; linarith
  have hw_ne : ∀ n, w n ≠ 0 := by
    intro n h
    have := (hzb n).2.1
    rw [h, norm_zero] at this; linarith

  /- ### Part A: the parameter moves, the point is fixed -/

  have hpartA : ∀ n, ‖normFactor x (z n) - normFactor y (z n)‖ ≤ 5 * ‖x - y‖ / ‖x‖ ^ 2 := by
    intro n
    have hzx : ‖x‖ ≤ ‖z n‖ := (hzb n).2.2.1
    have hfx : normFactor x (z n)
        = 1 + (2 * conj x / (z n) ^ 2 + ((conj x) ^ 2 + x) / (z n) ^ 4) := by
      rw [← normFactor_sub_one x (z n) (hz_ne n)]; ring
    have hfy : normFactor y (z n)
        = 1 + (2 * conj y / (z n) ^ 2 + ((conj y) ^ 2 + y) / (z n) ^ 4) := by
      rw [← normFactor_sub_one y (z n) (hz_ne n)]; ring
    have hmain : normFactor x (z n) - normFactor y (z n)
        = 2 * (conj x - conj y) / (z n) ^ 2
          + (((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)) / (z n) ^ 4 := by
      rw [hfx, hfy]
      ring_nf
    rw [hmain]
    have h1 : ‖2 * (conj x - conj y) / (z n) ^ 2‖ ≤ 2 * ‖x - y‖ / ‖x‖ ^ 2 := by
      have hden : ‖x‖ ^ 2 ≤ ‖z n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hzx 2
      rw [norm_div, norm_mul, norm_pow]
      have hcn : conj x - conj y = conj (x - y) := by rw [map_sub]
      rw [hcn, Complex.norm_conj, norm_two]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hAx 2) hden
    have h2 : ‖(((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)) / (z n) ^ 4‖
        ≤ 3 * ‖x - y‖ / ‖x‖ ^ 2 := by
      have hden : ‖x‖ ^ 4 ≤ ‖z n‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg x) hzx 4
      have hnum : ‖((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)‖
          ≤ ‖x - y‖ * (‖x‖ + ‖y‖) + ‖x - y‖ := by
        have hrw2 : ((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)
            = (conj x - conj y) * (conj x + conj y) + (x - y) := by ring
        rw [hrw2]
        have e1 : ‖conj x - conj y‖ = ‖x - y‖ := by
          have c : conj x - conj y = conj (x - y) := by rw [map_sub]
          rw [c, Complex.norm_conj]
        have e2 : ‖conj x + conj y‖ ≤ ‖x‖ + ‖y‖ := by
          calc ‖conj x + conj y‖ ≤ ‖conj x‖ + ‖conj y‖ := norm_add_le _ _
            _ = ‖x‖ + ‖y‖ := by rw [Complex.norm_conj, Complex.norm_conj]
        have e3 : ‖(conj x - conj y) * (conj x + conj y)‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
          rw [norm_mul, e1]
          exact mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
        calc ‖(conj x - conj y) * (conj x + conj y) + (x - y)‖
            ≤ ‖(conj x - conj y) * (conj x + conj y)‖ + ‖x - y‖ := norm_add_le _ _
          _ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) + ‖x - y‖ := by linarith [e3]
      rw [norm_div, norm_pow]
      have hdenpos : (0 : ℝ) < ‖x‖ ^ 4 := by positivity
      have hstep1 : ‖((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)‖ / ‖z n‖ ^ 4
          ≤ ‖((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)‖ / ‖x‖ ^ 4 :=
        div_le_div_of_nonneg_left (norm_nonneg _) hdenpos hden
      have hstep2 : ‖((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)‖ / ‖x‖ ^ 4
          ≤ (‖x - y‖ * (‖x‖ + ‖y‖) + ‖x - y‖) / ‖x‖ ^ 4 :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      have hstep3 : (‖x - y‖ * (‖x‖ + ‖y‖) + ‖x - y‖) / ‖x‖ ^ 4
          ≤ 3 * ‖x - y‖ / ‖x‖ ^ 2 := by
        rw [div_le_div_iff₀ hdenpos (pow_pos hAx 2)]
        have hbr : ‖x‖ + ‖y‖ + 1 ≤ 3 * ‖x‖ ^ 2 := by nlinarith [hyle, hA, norm_nonneg x]
        have h0 : (0 : ℝ) ≤ ‖x - y‖ * ‖x‖ ^ 2 := by positivity
        nlinarith [hbr, hδnn, h0, norm_nonneg x]
      linarith [hstep1, hstep2, hstep3]
    calc ‖2 * (conj x - conj y) / (z n) ^ 2
            + (((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)) / (z n) ^ 4‖
        ≤ ‖2 * (conj x - conj y) / (z n) ^ 2‖
            + ‖(((conj x) ^ 2 + x) - ((conj y) ^ 2 + y)) / (z n) ^ 4‖ := norm_add_le _ _
      _ ≤ 2 * ‖x - y‖ / ‖x‖ ^ 2 + 3 * ‖x - y‖ / ‖x‖ ^ 2 := add_le_add h1 h2
      _ = 5 * ‖x - y‖ / ‖x‖ ^ 2 := by ring

  /- ### Part B: the point moves, the parameter is fixed -/

  have hpartB : ∀ n, ‖normFactor y (z n) - normFactor y (w n)‖
      ≤ 12 * ‖x - y‖ * (32 ^ n / T n ^ 2) + 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4) := by
    intro n
    obtain ⟨b1, b2, b3, b4⟩ := hzb n
    have hzn : z n ≠ 0 := hz_ne n
    have hwn : w n ≠ 0 := hw_ne n
    have hxne : (‖x‖ : ℝ) ≠ 0 := hAx.ne'
    have hTposn : (0 : ℝ) < T n := by linarith [hTpos n]
    have hMpos : (0 : ℝ) < max ‖z n‖ ‖w n‖ := by
      have h : ‖z n‖ ≤ max ‖z n‖ ‖w n‖ := le_max_left _ _
      linarith
    have hTm : T n * max ‖z n‖ ‖w n‖ = ‖z n‖ * ‖w n‖ := by
      rw [show T n = min ‖z n‖ ‖w n‖ from rfl]
      exact min_mul_max _ _
    have he : ‖z n - w n‖ ≤ 32 ^ n * (‖x - y‖ / ‖x‖) * (‖z n‖ + ‖w n‖) := by
      have h := horb n
      simpa only [z, w] using h
    have hs : ‖z n‖ + ‖w n‖ ≤ 2 * max ‖z n‖ ‖w n‖ := by
      calc ‖z n‖ + ‖w n‖ ≤ max ‖z n‖ ‖w n‖ + max ‖z n‖ ‖w n‖ :=
            add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max ‖z n‖ ‖w n‖ := by ring
    have hs' : ‖z n + w n‖ ≤ 2 * max ‖z n‖ ‖w n‖ := le_trans (norm_add_le _ _) hs
    have hdrop1 : normFactor y (z n)
        = 1 + (2 * conj y / (z n) ^ 2 + ((conj y) ^ 2 + y) / (z n) ^ 4) := by
      rw [← normFactor_sub_one y (z n) (hz_ne n)]; ring
    have hdrop2 : normFactor y (w n)
        = 1 + (2 * conj y / (w n) ^ 2 + ((conj y) ^ 2 + y) / (w n) ^ 4) := by
      rw [← normFactor_sub_one y (w n) (hw_ne n)]; ring
    have hmain : normFactor y (z n) - normFactor y (w n)
        = 2 * conj y * (1 / (z n) ^ 2 - 1 / (w n) ^ 2)
          + ((conj y) ^ 2 + y) * (1 / (z n) ^ 4 - 1 / (w n) ^ 4) := by
      rw [hdrop1, hdrop2]
      ring_nf
    rw [hmain]
    have hden2 : ‖z n‖ ^ 2 * ‖w n‖ ^ 2 = T n ^ 2 * max ‖z n‖ ‖w n‖ ^ 2 := by
      rw [show T n ^ 2 * max ‖z n‖ ‖w n‖ ^ 2 = (T n * max ‖z n‖ ‖w n‖) ^ 2 by ring, hTm]
      ring
    have hden4 : ‖z n‖ ^ 4 * ‖w n‖ ^ 4 = T n ^ 4 * max ‖z n‖ ‖w n‖ ^ 4 := by
      rw [show T n ^ 4 * max ‖z n‖ ‖w n‖ ^ 4 = (T n * max ‖z n‖ ‖w n‖) ^ 4 by ring, hTm]
      ring
    have hM3 : (0 : ℝ) < max ‖z n‖ ‖w n‖ ^ 3 := by positivity
    have hB1 : ‖2 * conj y * (1 / (z n) ^ 2 - 1 / (w n) ^ 2)‖
        ≤ 12 * ‖x - y‖ * (32 ^ n / T n ^ 2) := by
      have hfrac : ‖1 / (z n) ^ 2 - 1 / (w n) ^ 2‖
          = ‖z n - w n‖ * ‖z n + w n‖ / (T n ^ 2 * max ‖z n‖ ‖w n‖ ^ 2) := by
        have h1 : ‖1 / (z n) ^ 2 - 1 / (w n) ^ 2‖
            = ‖(w n) ^ 2 - (z n) ^ 2‖ / (‖z n‖ ^ 2 * ‖w n‖ ^ 2) := by
          rw [show 1 / (z n) ^ 2 - 1 / (w n) ^ 2
                = ((w n) ^ 2 - (z n) ^ 2) / ((z n) ^ 2 * (w n) ^ 2) by
              field_simp,
            norm_div, norm_mul, norm_pow, norm_pow]
        rw [h1, show (w n) ^ 2 - (z n) ^ 2 = -(z n - w n) * (z n + w n) by ring,
          norm_mul, norm_neg, hden2]
      have hupper : ‖z n - w n‖ * ‖z n + w n‖
          ≤ 32 ^ n * (‖x - y‖ / ‖x‖) * (2 * max ‖z n‖ ‖w n‖) * (2 * max ‖z n‖ ‖w n‖) := by
        calc ‖z n - w n‖ * ‖z n + w n‖
            ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (‖z n‖ + ‖w n‖)) * ‖z n + w n‖ :=
              mul_le_mul_of_nonneg_right he (norm_nonneg _)
          _ ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (‖z n‖ + ‖w n‖)) * (2 * max ‖z n‖ ‖w n‖) :=
              mul_le_mul_of_nonneg_left hs' (by positivity)
          _ ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (2 * max ‖z n‖ ‖w n‖))
                * (2 * max ‖z n‖ ‖w n‖) := by
              have h2' : (0 : ℝ) ≤ 32 ^ n * (‖x - y‖ / ‖x‖) := by positivity
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs h2') (by positivity)
      have hkey : ‖1 / (z n) ^ 2 - 1 / (w n) ^ 2‖
          ≤ 4 * ‖x - y‖ * (32 ^ n / T n ^ 2) / ‖x‖ := by
        rw [hfrac]
        calc ‖z n - w n‖ * ‖z n + w n‖ / (T n ^ 2 * max ‖z n‖ ‖w n‖ ^ 2)
            ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (2 * max ‖z n‖ ‖w n‖)
                  * (2 * max ‖z n‖ ‖w n‖)) / (T n ^ 2 * max ‖z n‖ ‖w n‖ ^ 2) :=
              div_le_div_of_nonneg_right hupper (by positivity)
          _ = 4 * ‖x - y‖ * (32 ^ n / T n ^ 2) / ‖x‖ := by
              field_simp
              ring
      calc ‖2 * conj y * (1 / (z n) ^ 2 - 1 / (w n) ^ 2)‖
          = 2 * ‖y‖ * ‖1 / (z n) ^ 2 - 1 / (w n) ^ 2‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj, norm_two]
        _ ≤ 2 * (3 * ‖x‖ / 2) * (4 * ‖x - y‖ * (32 ^ n / T n ^ 2) / ‖x‖) := by
            have hy2 : ‖y‖ ≤ 3 * ‖x‖ / 2 := hyle
            calc 2 * ‖y‖ * ‖1 / (z n) ^ 2 - 1 / (w n) ^ 2‖
                ≤ 2 * (3 * ‖x‖ / 2) * ‖1 / (z n) ^ 2 - 1 / (w n) ^ 2‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  linarith
              _ ≤ 2 * (3 * ‖x‖ / 2) * (4 * ‖x - y‖ * (32 ^ n / T n ^ 2) / ‖x‖) :=
                  mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 12 * ‖x - y‖ * (32 ^ n / T n ^ 2) := by
            field_simp
            ring
    have hB2 : ‖((conj y) ^ 2 + y) * (1 / (z n) ^ 4 - 1 / (w n) ^ 4)‖
        ≤ 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4) := by
      have hpoly : ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
          ≤ 4 * max ‖z n‖ ‖w n‖ ^ 3 := by
        have hM := le_max_left ‖z n‖ ‖w n‖
        have hM' := le_max_right ‖z n‖ ‖w n‖
        have hz0 : (0 : ℝ) ≤ ‖z n‖ := norm_nonneg _
        have hw0 : (0 : ℝ) ≤ ‖w n‖ := norm_nonneg _
        have hsum : ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
            ≤ (‖z n‖ ^ 3 + ‖z n‖ ^ 2 * ‖w n‖ + ‖z n‖ * ‖w n‖ ^ 2) + ‖w n‖ ^ 3 := by
          calc ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
              ≤ ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2‖ + ‖(w n) ^ 3‖ := norm_add_le _ _
            _ ≤ (‖(z n) ^ 3 + (z n) ^ 2 * (w n)‖ + ‖(z n) * (w n) ^ 2‖) + ‖(w n) ^ 3‖ := by
                linarith [norm_add_le ((z n) ^ 3 + (z n) ^ 2 * (w n)) ((z n) * (w n) ^ 2)]
            _ ≤ ((‖(z n) ^ 3‖ + ‖(z n) ^ 2 * (w n)‖) + ‖(z n) * (w n) ^ 2‖) + ‖(w n) ^ 3‖ := by
                linarith [norm_add_le ((z n) ^ 3) ((z n) ^ 2 * (w n))]
            _ = (‖z n‖ ^ 3 + ‖z n‖ ^ 2 * ‖w n‖ + ‖z n‖ * ‖w n‖ ^ 2) + ‖w n‖ ^ 3 := by
                simp only [norm_pow, norm_mul]
        have p1 : ‖z n‖ ^ 3 ≤ max ‖z n‖ ‖w n‖ ^ 3 := pow_le_pow_left₀ hz0 hM 3
        have p2 : ‖z n‖ ^ 2 * ‖w n‖ ≤ max ‖z n‖ ‖w n‖ ^ 3 := by
          have h1 : ‖z n‖ ^ 2 ≤ max ‖z n‖ ‖w n‖ ^ 2 := pow_le_pow_left₀ hz0 hM 2
          have := mul_le_mul h1 hM' hw0 (by positivity : (0 : ℝ) ≤ max ‖z n‖ ‖w n‖ ^ 2)
          have he : max ‖z n‖ ‖w n‖ ^ 2 * max ‖z n‖ ‖w n‖ = max ‖z n‖ ‖w n‖ ^ 3 := by ring
          linarith [this, he.le, he.ge]
        have p3 : ‖z n‖ * ‖w n‖ ^ 2 ≤ max ‖z n‖ ‖w n‖ ^ 3 := by
          have h1 : ‖w n‖ ^ 2 ≤ max ‖z n‖ ‖w n‖ ^ 2 := pow_le_pow_left₀ hw0 hM' 2
          have := mul_le_mul hM h1 (by positivity : (0 : ℝ) ≤ ‖w n‖ ^ 2) (by positivity : (0 : ℝ) ≤ max ‖z n‖ ‖w n‖)
          have he : max ‖z n‖ ‖w n‖ * max ‖z n‖ ‖w n‖ ^ 2 = max ‖z n‖ ‖w n‖ ^ 3 := by ring
          linarith [this, he.le, he.ge]
        have p4 : ‖w n‖ ^ 3 ≤ max ‖z n‖ ‖w n‖ ^ 3 := pow_le_pow_left₀ hw0 hM' 3
        linarith [hsum, p1, p2, p3, p4]
      have hfrac : ‖1 / (z n) ^ 4 - 1 / (w n) ^ 4‖
          = ‖z n - w n‖
              * ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
            / (T n ^ 4 * max ‖z n‖ ‖w n‖ ^ 4) := by
        have h1 : ‖1 / (z n) ^ 4 - 1 / (w n) ^ 4‖
            = ‖(w n) ^ 4 - (z n) ^ 4‖ / (‖z n‖ ^ 4 * ‖w n‖ ^ 4) := by
          rw [show 1 / (z n) ^ 4 - 1 / (w n) ^ 4
                = ((w n) ^ 4 - (z n) ^ 4) / ((z n) ^ 4 * (w n) ^ 4) by
              field_simp,
            norm_div, norm_mul, norm_pow, norm_pow]
        rw [h1, show (w n) ^ 4 - (z n) ^ 4
              = -(z n - w n) * ((z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3) by
            ring,
          norm_mul, norm_neg, hden4]
      have hupper : ‖z n - w n‖
            * ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
          ≤ 32 ^ n * (‖x - y‖ / ‖x‖) * (2 * max ‖z n‖ ‖w n‖) * (4 * max ‖z n‖ ‖w n‖ ^ 3) := by
        calc ‖z n - w n‖
              * ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
            ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (‖z n‖ + ‖w n‖))
                * ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖ :=
              mul_le_mul_of_nonneg_right he (norm_nonneg _)
          _ ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (‖z n‖ + ‖w n‖)) * (4 * max ‖z n‖ ‖w n‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hpoly (by positivity)
          _ ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (2 * max ‖z n‖ ‖w n‖))
                * (4 * max ‖z n‖ ‖w n‖ ^ 3) := by
              have h2' : (0 : ℝ) ≤ 32 ^ n * (‖x - y‖ / ‖x‖) := by positivity
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs h2') (by positivity)
      have hkey : ‖1 / (z n) ^ 4 - 1 / (w n) ^ 4‖
          ≤ 8 * ‖x - y‖ * (32 ^ n / T n ^ 4) / ‖x‖ := by
        rw [hfrac]
        calc ‖z n - w n‖
              * ‖(z n) ^ 3 + (z n) ^ 2 * (w n) + (z n) * (w n) ^ 2 + (w n) ^ 3‖
              / (T n ^ 4 * max ‖z n‖ ‖w n‖ ^ 4)
            ≤ (32 ^ n * (‖x - y‖ / ‖x‖) * (2 * max ‖z n‖ ‖w n‖)
                  * (4 * max ‖z n‖ ‖w n‖ ^ 3)) / (T n ^ 4 * max ‖z n‖ ‖w n‖ ^ 4) :=
              div_le_div_of_nonneg_right hupper (by positivity)
          _ = 8 * ‖x - y‖ * (32 ^ n / T n ^ 4) / ‖x‖ := by
              field_simp
              ring
      have hcy : ‖(conj y) ^ 2 + y‖ ≤ 3 * ‖x‖ ^ 2 := by
        calc ‖(conj y) ^ 2 + y‖ ≤ ‖(conj y) ^ 2‖ + ‖y‖ := norm_add_le _ _
          _ = ‖y‖ ^ 2 + ‖y‖ := by rw [norm_pow, Complex.norm_conj]
          _ ≤ 3 * ‖x‖ ^ 2 := by nlinarith [hyle, norm_nonneg y, hA]
      calc ‖((conj y) ^ 2 + y) * (1 / (z n) ^ 4 - 1 / (w n) ^ 4)‖
          = ‖(conj y) ^ 2 + y‖ * ‖1 / (z n) ^ 4 - 1 / (w n) ^ 4‖ := norm_mul _ _
        _ ≤ 3 * ‖x‖ ^ 2 * (8 * ‖x - y‖ * (32 ^ n / T n ^ 4) / ‖x‖) :=
            mul_le_mul hcy hkey (norm_nonneg _) (by positivity)
        _ = 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4) := by
            field_simp
            ring
    calc ‖2 * conj y * (1 / (z n) ^ 2 - 1 / (w n) ^ 2)
            + ((conj y) ^ 2 + y) * (1 / (z n) ^ 4 - 1 / (w n) ^ 4)‖
        ≤ ‖2 * conj y * (1 / (z n) ^ 2 - 1 / (w n) ^ 2)‖
            + ‖((conj y) ^ 2 + y) * (1 / (z n) ^ 4 - 1 / (w n) ^ 4)‖ := norm_add_le _ _
      _ ≤ 12 * ‖x - y‖ * (32 ^ n / T n ^ 2) + 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4) :=
          add_le_add hB1 hB2

  /- ### The normalised factors stay within `1/2` of `1` -/

  have hnf1 : ∀ n, ‖normFactor x (z n) - 1‖ ≤ 1 / 2 := by
    intro n
    rw [normFactor_sub_one x (z n) (hz_ne n)]
    have hzx : ‖x‖ ≤ ‖z n‖ := (hzb n).2.2.1
    have hden2 : ‖x‖ ^ 2 ≤ ‖z n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hzx 2
    have hden4 : ‖x‖ ^ 4 ≤ ‖z n‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg x) hzx 4
    have hsplit : ‖2 * conj x / (z n) ^ 2 + ((conj x) ^ 2 + x) / (z n) ^ 4‖
        ≤ 2 * ‖x‖ / ‖z n‖ ^ 2 + (‖x‖ ^ 2 + ‖x‖) / ‖z n‖ ^ 4 := by
      refine le_trans (norm_add_le _ _) ?_
      have e1 : ‖2 * conj x / (z n) ^ 2‖ = 2 * ‖x‖ / ‖z n‖ ^ 2 := by
        rw [norm_div, norm_mul, norm_pow, Complex.norm_conj, norm_two]
      have e2 : ‖((conj x) ^ 2 + x) / (z n) ^ 4‖ ≤ (‖x‖ ^ 2 + ‖x‖) / ‖z n‖ ^ 4 := by
        rw [norm_div, norm_pow]
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc ‖(conj x) ^ 2 + x‖ ≤ ‖(conj x) ^ 2‖ + ‖x‖ := norm_add_le _ _
          _ = ‖x‖ ^ 2 + ‖x‖ := by rw [norm_pow, Complex.norm_conj]
      linarith [e1, e2]
    have hsmall : 2 * ‖x‖ / ‖z n‖ ^ 2 + (‖x‖ ^ 2 + ‖x‖) / ‖z n‖ ^ 4 ≤ 1 / 2 := by
      have hzp : (0 : ℝ) < ‖z n‖ := by linarith [(hzb n).1]
      have ha : 2 * ‖x‖ / ‖z n‖ ^ 2 ≤ 2 / ‖x‖ := by
        rw [div_le_div_iff₀ (pow_pos hzp 2) hAx]
        nlinarith [hden2, norm_nonneg x]
      have hb2 : (‖x‖ ^ 2 + ‖x‖) / ‖z n‖ ^ 4 ≤ (‖x‖ + 1) / ‖x‖ ^ 3 := by
        rw [div_le_div_iff₀ (pow_pos hzp 4) (pow_pos hAx 3)]
        have hm := mul_le_mul_of_nonneg_left hden4 (by positivity : (0 : ℝ) ≤ ‖x‖ + 1)
        nlinarith [hm, norm_nonneg x]
      have hfin : 2 / ‖x‖ + (‖x‖ + 1) / ‖x‖ ^ 3 ≤ 1 / 2 := by
        have h3 : (0 : ℝ) < ‖x‖ ^ 3 := by positivity
        rw [show (2 : ℝ) / ‖x‖ = 2 * ‖x‖ ^ 2 / ‖x‖ ^ 3 by
              rw [div_eq_div_iff hAx.ne' h3.ne']; ring]
        rw [← add_div, div_le_iff₀ h3]
        nlinarith [hA, norm_nonneg x]
      linarith [ha, hb2, hfin]
    linarith [hsplit, hsmall]
  have hnf2 : ∀ n, ‖normFactor y (w n) - 1‖ ≤ 1 / 2 := by
    intro n
    rw [normFactor_sub_one y (w n) (hw_ne n)]
    have hwy : ‖y‖ ≤ ‖w n‖ := (hzb n).2.2.2
    have hden2 : ‖y‖ ^ 2 ≤ ‖w n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hwy 2
    have hden4 : ‖y‖ ^ 4 ≤ ‖w n‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg y) hwy 4
    have hsplit : ‖2 * conj y / (w n) ^ 2 + ((conj y) ^ 2 + y) / (w n) ^ 4‖
        ≤ 2 * ‖y‖ / ‖w n‖ ^ 2 + (‖y‖ ^ 2 + ‖y‖) / ‖w n‖ ^ 4 := by
      refine le_trans (norm_add_le _ _) ?_
      have e1 : ‖2 * conj y / (w n) ^ 2‖ = 2 * ‖y‖ / ‖w n‖ ^ 2 := by
        rw [norm_div, norm_mul, norm_pow, Complex.norm_conj, norm_two]
      have e2 : ‖((conj y) ^ 2 + y) / (w n) ^ 4‖ ≤ (‖y‖ ^ 2 + ‖y‖) / ‖w n‖ ^ 4 := by
        rw [norm_div, norm_pow]
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc ‖(conj y) ^ 2 + y‖ ≤ ‖(conj y) ^ 2‖ + ‖y‖ := norm_add_le _ _
          _ = ‖y‖ ^ 2 + ‖y‖ := by rw [norm_pow, Complex.norm_conj]
      linarith [e1, e2]
    have hsmall : 2 * ‖y‖ / ‖w n‖ ^ 2 + (‖y‖ ^ 2 + ‖y‖) / ‖w n‖ ^ 4 ≤ 1 / 2 := by
      have hwp : (0 : ℝ) < ‖w n‖ := by linarith [(hzb n).2.1]
      have hyp : (0 : ℝ) < ‖y‖ := by linarith
      have ha : 2 * ‖y‖ / ‖w n‖ ^ 2 ≤ 2 / ‖y‖ := by
        rw [div_le_div_iff₀ (pow_pos hwp 2) hyp]
        nlinarith [hden2, norm_nonneg y]
      have hb2 : (‖y‖ ^ 2 + ‖y‖) / ‖w n‖ ^ 4 ≤ (‖y‖ + 1) / ‖y‖ ^ 3 := by
        rw [div_le_div_iff₀ (pow_pos hwp 4) (pow_pos hyp 3)]
        have hm := mul_le_mul_of_nonneg_left hden4 (by positivity : (0 : ℝ) ≤ ‖y‖ + 1)
        nlinarith [hm, norm_nonneg y]
      have hfin : 2 / ‖y‖ + (‖y‖ + 1) / ‖y‖ ^ 3 ≤ 1 / 2 := by
        have hy3 : (0 : ℝ) < ‖y‖ ^ 3 := pow_pos hyp 3
        rw [show (2 : ℝ) / ‖y‖ = 2 * ‖y‖ ^ 2 / ‖y‖ ^ 3 by
              rw [div_eq_div_iff hyp.ne' hy3.ne']; ring]
        rw [← add_div, div_le_iff₀ hy3]
        nlinarith [hyge, hA, norm_nonneg y]
      linarith [ha, hb2, hfin]
    linarith [hsplit, hsmall]

  /- ### The termwise bound -/

  have hdiff : ∀ n, ‖normFactor x (z n) - normFactor y (w n)‖
      ≤ 5 * ‖x - y‖ / ‖x‖ ^ 2 + 12 * ‖x - y‖ * (32 ^ n / T n ^ 2)
        + 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4) := by
    intro n
    have hdec : normFactor x (z n) - normFactor y (w n)
        = (normFactor x (z n) - normFactor y (z n))
          + (normFactor y (z n) - normFactor y (w n)) := by ring
    rw [hdec]
    have htri := norm_add_le (normFactor x (z n) - normFactor y (z n))
      (normFactor y (z n) - normFactor y (w n))
    linarith [htri, hpartA n, hpartB n]
  have hF : ∀ n, ‖bottcherTerm x n x - bottcherTerm y n y‖
      ≤ (1 / 4 : ℝ) ^ (n + 1) * (2 * (5 * ‖x - y‖ / ‖x‖ ^ 2
          + 12 * ‖x - y‖ * (32 ^ n / T n ^ 2)
          + 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4))) := by
    intro n
    have hkey : bottcherTerm x n x - bottcherTerm y n y
        = ((1 / 4 : ℝ) ^ (n + 1) : ℂ)
          * (Complex.log (normFactor x (z n)) - Complex.log (normFactor y (w n))) := by
      simp only [bottcherTerm]
      rw [show (pMap x)^[n] x = z n from rfl, show (pMap y)^[n] y = w n from rfl]
      ring
    rw [hkey, norm_mul, norm_quarter_pow n]
    have hlog := norm_log_sub_log_le (hnf1 n) (hnf2 n)
    calc (1 / 4 : ℝ) ^ (n + 1)
            * ‖Complex.log (normFactor x (z n)) - Complex.log (normFactor y (w n))‖
        ≤ (1 / 4 : ℝ) ^ (n + 1) * (2 * ‖normFactor x (z n) - normFactor y (w n)‖) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (1 / 4 : ℝ) ^ (n + 1) * (2 * (5 * ‖x - y‖ / ‖x‖ ^ 2
            + 12 * ‖x - y‖ * (32 ^ n / T n ^ 2)
            + 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4))) :=
          mul_le_mul_of_nonneg_left (by linarith [hdiff n]) (by positivity)

  /- ### Summation -/

  let c1 : ℝ := 10 * ‖x - y‖ / ‖x‖ ^ 2
  let c2 : ℝ := 96 * ‖x - y‖ / ‖x‖ ^ 2 + 768 * ‖x - y‖ / ‖x‖ ^ 3
  let G : ℕ → ℝ := fun n => c1 * (1 / 4 : ℝ) ^ (n + 1)
    + c2 * ((1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n)
  have hFG : ∀ n, ‖bottcherTerm x n x - bottcherTerm y n y‖ ≤ G n := by
    intro n
    refine le_trans (hF n) ?_
    have h1 := hb n
    have h2 := hd n
    have g1 : 12 * ‖x - y‖ * (32 ^ n / T n ^ 2) ≤ 12 * ‖x - y‖ * ((4 / ‖x‖ ^ 2) * (1 / 2) ^ n) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have g2 : 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4)
        ≤ 24 * ‖x‖ * ‖x - y‖ * ((16 / ‖x‖ ^ 4) * (1 / 2) ^ n) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e1 : (1 / 4 : ℝ) ^ (n + 1) * (2 * (12 * ‖x - y‖ * (32 ^ n / T n ^ 2)))
        ≤ (1 / 4 : ℝ) ^ (n + 1) * (2 * (12 * ‖x - y‖ * ((4 / ‖x‖ ^ 2) * (1 / 2) ^ n))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left g1 (by norm_num)) (by positivity)
    have e2 : (1 / 4 : ℝ) ^ (n + 1) * (2 * (24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4)))
        ≤ (1 / 4 : ℝ) ^ (n + 1) * (2 * (24 * ‖x‖ * ‖x - y‖ * ((16 / ‖x‖ ^ 4) * (1 / 2) ^ n))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left g2 (by norm_num)) (by positivity)
    have e3 : (1 / 4 : ℝ) ^ (n + 1) * (2 * (5 * ‖x - y‖ / ‖x‖ ^ 2))
        = c1 * (1 / 4 : ℝ) ^ (n + 1) := by
      simp only [c1]; ring
    have e4 : (1 / 4 : ℝ) ^ (n + 1) * (2 * (12 * ‖x - y‖ * ((4 / ‖x‖ ^ 2) * (1 / 2) ^ n)))
          + (1 / 4 : ℝ) ^ (n + 1) * (2 * (24 * ‖x‖ * ‖x - y‖ * ((16 / ‖x‖ ^ 4) * (1 / 2) ^ n)))
        = c2 * ((1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n) := by
      simp only [c2]
      field_simp
      ring
    have hsplit : (1 / 4 : ℝ) ^ (n + 1)
          * (2 * (5 * ‖x - y‖ / ‖x‖ ^ 2 + 12 * ‖x - y‖ * (32 ^ n / T n ^ 2)
              + 24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4)))
        = (1 / 4 : ℝ) ^ (n + 1) * (2 * (5 * ‖x - y‖ / ‖x‖ ^ 2))
          + (1 / 4 : ℝ) ^ (n + 1) * (2 * (12 * ‖x - y‖ * (32 ^ n / T n ^ 2)))
          + (1 / 4 : ℝ) ^ (n + 1) * (2 * (24 * ‖x‖ * ‖x - y‖ * (32 ^ n / T n ^ 4))) := by ring
    simp only [G]
    linarith [hsplit, e1, e2, e3, e4]
  have hGsumm : Summable G := by
    have h1 : Summable fun n : ℕ => c1 * (1 / 4 : ℝ) ^ (n + 1) :=
      summable_quarter_pow_succ.mul_left c1
    have h2 : Summable fun n : ℕ => c2 * ((1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n) :=
      summable_quarter_succ_mul_half.mul_left c2
    simpa only [G] using h1.add h2
  have hGtsum : (∑' n, G n) = c1 * (1 / 3) + c2 * (2 / 7) := by
    have h1 : Summable fun n : ℕ => c1 * (1 / 4 : ℝ) ^ (n + 1) :=
      summable_quarter_pow_succ.mul_left c1
    have h2 : Summable fun n : ℕ => c2 * ((1 / 4 : ℝ) ^ (n + 1) * (1 / 2) ^ n) :=
      summable_quarter_succ_mul_half.mul_left c2
    simp only [G]
    rw [Summable.tsum_add h1 h2, tsum_mul_left, tsum_mul_left, tsum_quarter_pow_succ,
      tsum_quarter_succ_mul_half]
  have hGle : (∑' n, G n) ≤ 64 * ‖x - y‖ / ‖x‖ ^ 2 := by
    rw [hGtsum]
    rw [le_div_iff₀ (pow_pos hAx 2)]
    simp only [c1, c2]
    field_simp
    nlinarith [hA, hδnn, norm_nonneg x, hAx]
  have hsumx : Summable fun n : ℕ => bottcherTerm x n x := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1))
      summable_quarter_pow_succ ?_
    intro n
    have hkey : bottcherTerm x n x
        = ((1 / 4 : ℝ) ^ (n + 1) : ℂ) * Complex.log (normFactor x (z n)) := by
      simp only [bottcherTerm]
      rw [show (pMap x)^[n] x = z n from rfl]
    rw [hkey, norm_mul, norm_quarter_pow n]
    have hlog : ‖Complex.log (normFactor x (z n))‖ ≤ 1 := by
      have h := norm_log_sub_log_le (a := normFactor x (z n)) (b := 1) (hnf1 n) (by norm_num)
      rw [Complex.log_one, sub_zero] at h
      linarith [h, hnf1 n]
    nlinarith [hlog, show (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (n + 1) by positivity]
  have hsumy : Summable fun n : ℕ => bottcherTerm y n y := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1))
      summable_quarter_pow_succ ?_
    intro n
    have hkey : bottcherTerm y n y
        = ((1 / 4 : ℝ) ^ (n + 1) : ℂ) * Complex.log (normFactor y (w n)) := by
      simp only [bottcherTerm]
      rw [show (pMap y)^[n] y = w n from rfl]
    rw [hkey, norm_mul, norm_quarter_pow n]
    have hlog : ‖Complex.log (normFactor y (w n))‖ ≤ 1 := by
      have h := norm_log_sub_log_le (a := normFactor y (w n)) (b := 1) (hnf2 n) (by norm_num)
      rw [Complex.log_one, sub_zero] at h
      linarith [h, hnf2 n]
    nlinarith [hlog, show (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (n + 1) by positivity]
  have hsub : (∑' n, bottcherTerm x n x) - (∑' n, bottcherTerm y n y)
      = ∑' n, (bottcherTerm x n x - bottcherTerm y n y) := (hsumx.tsum_sub hsumy).symm
  have h1 : ‖bottcherSeries x x - bottcherSeries y y‖
      = ‖∑' n, (bottcherTerm x n x - bottcherTerm y n y)‖ := by
    rw [show bottcherSeries x x = ∑' n, bottcherTerm x n x from rfl,
      show bottcherSeries y y = ∑' n, bottcherTerm y n y from rfl, ← hsub]
  rw [h1]
  have hsumF : Summable fun n : ℕ => ‖bottcherTerm x n x - bottcherTerm y n y‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hFG hGsumm
  calc ‖∑' n, (bottcherTerm x n x - bottcherTerm y n y)‖
      ≤ ∑' n, ‖bottcherTerm x n x - bottcherTerm y n y‖ := norm_tsum_le_tsum_norm hsumF
    _ ≤ ∑' n, G n := hsumF.tsum_le_tsum hFG hGsumm
    _ ≤ 64 * ‖x - y‖ / ‖x‖ ^ 2 := hGle

end

end Work.NAKANE.FarInj
