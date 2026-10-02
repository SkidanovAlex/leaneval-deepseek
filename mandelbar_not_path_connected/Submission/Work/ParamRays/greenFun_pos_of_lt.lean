/-
# Positivity of the Green function on the escaping set

For the antiholomorphic unicritical family `T_c(z) = (conj z)^2 + c` we prove that the
Green function `G_c(w) = limsup_n 2^{-n} log⁺ ‖T_c^[n] w‖` is strictly positive as soon as
the orbit of `w` escapes, i.e. as soon as `max 2 ‖c‖ < ‖w‖`.

The mathematical content is the classical doubly exponential growth of the orbit on the
escaping set: once `‖T_c^[n] w‖ ≥ max 4 (2 ‖c‖)` the reverse triangle inequality
`‖T_c u‖ ≥ ‖u‖² - ‖c‖` gives `‖T_c u‖ ≥ ‖u‖²/2 ≥ ‖u‖`, so the hypothesis of the
estimate is preserved and the norms square up to a factor `1/2` at each step.  Hence

`‖T_c^[N+k] w‖ ≥ 2 (‖T_c^[N] w‖ / 2)^{2^k}`,

and consequently `greenSeq c w (N+k) ≥ 2^{-N} log (‖T_c^[N] w‖ / 2) > 0` for every `k`.
A `limsup` is at least any value that is eventually a lower bound, and it is finite because
the orbit obeys the polynomial-type bound `‖T_c^[n] w‖ ≤ (2 (‖w‖ + ‖c‖ + 1))^{2^n}`.

## Main result

* `Work.ParamRays.greenFun_pos_of_lt` : `max 2 ‖c‖ < ‖w‖` implies `0 < greenFun c w`.
-/
import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Function Filter
open scoped Real Topology
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.ParamRays

/- Elementary growth estimates for orbits that have exceeded the threshold
`max 4 (2‖c‖)`.  These are the quantitative heart of the positivity of the Green
function, exposed for reuse by later parameter-ray arguments. -/
namespace GreenGrowth

/-- If `‖u‖ ≥ max 4 (2‖c‖)`, then the next point of the orbit still satisfies that
inequality, and `‖T_c u‖ ≥ ‖u‖² / 2`. -/
lemma orbit_step_ge (c u : ℂ) (hu : max 4 (2 * ‖c‖) ≤ ‖u‖) :
    max 4 (2 * ‖c‖) ≤ ‖Tantibar c u‖ ∧ ‖u‖ ^ 2 / 2 ≤ ‖Tantibar c u‖ := by
  have h4 : (4 : ℝ) ≤ ‖u‖ := le_trans (le_max_left _ _) hu
  have hc2 : 2 * ‖c‖ ≤ ‖u‖ := le_trans (le_max_right _ _) hu
  have hc : ‖c‖ ≤ ‖u‖ / 2 := by linarith
  have h1 : ‖u‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c u‖ := norm_sq_sub_le_norm_Tantibar c u
  have h2 : ‖u‖ ^ 2 / 2 ≤ ‖u‖ ^ 2 - ‖c‖ := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ ‖u‖ by linarith)
      (show (0 : ℝ) ≤ ‖u‖ - 1 by linarith)]
  refine ⟨?_, le_trans h2 h1⟩
  calc max 4 (2 * ‖c‖) ≤ ‖u‖ := hu
    _ ≤ ‖u‖ ^ 2 / 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ ‖u‖ by linarith)
          (show (0 : ℝ) ≤ ‖u‖ - 2 by linarith)]
    _ ≤ ‖Tantibar c u‖ := le_trans h2 h1

/-- **Doubly exponential growth.**  If `‖u‖ ≥ max 4 (2‖c‖)` then the orbit of `u` grows
at least like `2 (‖u‖/2)^{2^k}`, and the threshold is preserved at every step. -/
lemma orbit_growth (c u : ℂ) (hu : max 4 (2 * ‖c‖) ≤ ‖u‖) (k : ℕ) :
    2 * (‖u‖ / 2) ^ (2 ^ k) ≤ ‖orbit c u k‖ ∧ max 4 (2 * ‖c‖) ≤ ‖orbit c u k‖ := by
  induction k with
  | zero =>
    simp only [orbit_zero, pow_zero, pow_one]
    exact ⟨by linarith, hu⟩
  | succ k ih =>
    obtain ⟨ih2, ihA⟩ := ih
    obtain ⟨hA', hge⟩ := orbit_step_ge c (orbit c u k) ihA
    rw [orbit_succ]
    have hp : (‖u‖ / 2) ^ (2 ^ (k + 1)) = ((‖u‖ / 2) ^ (2 ^ k)) ^ 2 := by
      rw [pow_succ]
      exact pow_mul _ _ _
    refine ⟨?_, hA'⟩
    rw [hp]
    have hB0 : (0 : ℝ) ≤ (‖u‖ / 2) ^ (2 ^ k) := by positivity
    have hprod : 2 * ((‖u‖ / 2) ^ (2 ^ k)) ^ 2 ≤ ‖orbit c u k‖ ^ 2 / 2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ ‖orbit c u k‖ - 2 * (‖u‖ / 2) ^ (2 ^ k) by linarith)
        (show (0 : ℝ) ≤ ‖orbit c u k‖ + 2 * (‖u‖ / 2) ^ (2 ^ k) by linarith)]
    linarith

/-- **Upper bound for the orbit.**  Regardless of `c` and `w`, the `n`-th point of the
orbit is at most `(2 (‖w‖ + ‖c‖ + 1))^{2^n}`.  In particular the normalized logarithms
`greenSeq c w n` are bounded above, so `greenFun c w` is finite. -/
lemma orbit_norm_le_pow (c w : ℂ) (n : ℕ) :
    ‖orbit c w n‖ ≤ (2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ n) := by
  have hmain : ∀ n : ℕ, 2 * (‖orbit c w n‖ + (‖c‖ + 1))
      ≤ (2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := norm_nonneg (orbit c w n)
      have hc0 := norm_nonneg c
      have hstep : ‖orbit c w (n + 1)‖ ≤ (‖orbit c w n‖ + (‖c‖ + 1)) ^ 2 := by
        rw [orbit_succ]
        have h1 := norm_Tantibar_le c (orbit c w n)
        nlinarith [h1, mul_nonneg (show (0 : ℝ) ≤ ‖c‖ + 1 by linarith)
          (show (0 : ℝ) ≤ ‖c‖ + 1 - 1 by linarith)]
      have hZ : 2 * (‖orbit c w (n + 1)‖ + (‖c‖ + 1))
          ≤ (2 * (‖orbit c w n‖ + (‖c‖ + 1))) ^ 2 := by
        nlinarith [hstep, mul_nonneg (by linarith : (0 : ℝ) ≤ ‖orbit c w n‖ + (‖c‖ + 1))
          (show (0 : ℝ) ≤ ‖orbit c w n‖ + (‖c‖ + 1) - (‖c‖ + 1) by linarith)]
      have hsq : (2 * (‖orbit c w n‖ + (‖c‖ + 1))) ^ 2
          ≤ ((2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ n)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) ih 2
      have hp : ((2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ n)) ^ 2
          = (2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, show 2 ^ n * 2 = 2 ^ (n + 1) from by rw [pow_succ]]
      rw [hp] at hsq
      linarith
  have hfin : ‖orbit c w n‖ ≤ 2 * (‖orbit c w n‖ + (‖c‖ + 1)) := by
    linarith [norm_nonneg (orbit c w n), norm_nonneg c]
  exact le_trans hfin (hmain n)

/-- The normalized logarithms of an orbit are uniformly bounded above. -/
lemma greenSeq_le_log (c w : ℂ) (n : ℕ) :
    greenSeq c w n ≤ Real.log (2 * (‖w‖ + (‖c‖ + 1))) := by
  rw [greenSeq]
  have hK1 : (1 : ℝ) ≤ 2 * (‖w‖ + (‖c‖ + 1)) := by
    linarith [norm_nonneg w, norm_nonneg c]
  have hnorm := orbit_norm_le_pow c w n
  have h1 : Real.posLog ‖orbit c w n‖
      ≤ (2 : ℝ) ^ n * Real.log (2 * (‖w‖ + (‖c‖ + 1))) := by
    calc Real.posLog ‖orbit c w n‖
        ≤ Real.posLog ((2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ n)) :=
          Real.posLog_le_posLog (by linarith [norm_nonneg (orbit c w n)]) hnorm
      _ = Real.log ((2 * (‖w‖ + (‖c‖ + 1))) ^ (2 ^ n)) := by
          rw [Real.posLog_eq_log]
          rw [abs_of_nonneg (by positivity)]
          exact one_le_pow₀ hK1
      _ = (2 : ℝ) ^ n * Real.log (2 * (‖w‖ + (‖c‖ + 1))) := by
          rw [Real.log_pow, Nat.cast_pow]
          norm_num
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹)
  have h3 : ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * Real.log (2 * (‖w‖ + (‖c‖ + 1))))
      = Real.log (2 * (‖w‖ + (‖c‖ + 1))) := by
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  linarith

end GreenGrowth

/-! ## Positivity of the Green function -/

/-- **The Green function is positive on the escaping set.**  If `w` satisfies the escape
criterion `max 2 ‖c‖ < ‖w‖`, then the normalized logarithms `2^{-n} log⁺ ‖T_c^[n] w‖`
are eventually bounded below by a positive constant, hence so is their `limsup`
`greenFun c w`. -/
theorem greenFun_pos_of_lt (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    0 < Work.ParamRays.greenFun c w := by
  -- the orbit eventually exceeds the threshold `max 4 (2‖c‖)`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max 4 (2 * ‖c‖) ≤ ‖orbit c w N‖ := by
    have hesc := escaping_of_lt_norm c w h
    rw [Escaping, Filter.tendsto_atTop_atTop] at hesc
    obtain ⟨i, hi⟩ := hesc (max 4 (2 * ‖c‖))
    exact ⟨i, hi i le_rfl⟩
  have hX4 : (4 : ℝ) ≤ ‖orbit c w N‖ := le_trans (le_max_left (4 : ℝ) (2 * ‖c‖)) hN
  have hX2 : (2 : ℝ) ≤ ‖orbit c w N‖ / 2 := by linarith
  -- the guaranteed lower bound for the normalized logarithms
  have hkey : ∀ k : ℕ, ((2 : ℝ) ^ N)⁻¹ * Real.log (‖orbit c w N‖ / 2)
      ≤ greenSeq c w (N + k) := by
    intro k
    obtain ⟨hg2, -⟩ := GreenGrowth.orbit_growth c (orbit c w N) hN k
    have hgr : 2 * (‖orbit c w N‖ / 2) ^ (2 ^ k) ≤ ‖orbit c w (N + k)‖ := by
      rw [orbit_add]
      exact hg2
    have hA1 : (1 : ℝ) ≤ 2 * (‖orbit c w N‖ / 2) ^ (2 ^ k) := by
      have h1 : (1 : ℝ) ≤ (‖orbit c w N‖ / 2) ^ (2 ^ k) :=
        one_le_pow₀ (by linarith : (1 : ℝ) ≤ ‖orbit c w N‖ / 2)
      linarith
    have hple : Real.posLog (2 * (‖orbit c w N‖ / 2) ^ (2 ^ k))
        ≤ Real.posLog ‖orbit c w (N + k)‖ :=
      Real.posLog_le_posLog (by linarith [hA1]) hgr
    have hplog : Real.posLog (2 * (‖orbit c w N‖ / 2) ^ (2 ^ k))
        = Real.log 2 + (2 : ℝ) ^ k * Real.log (‖orbit c w N‖ / 2) := by
      rw [Real.posLog_eq_log (by rwa [abs_of_nonneg (by positivity)])]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_pow]
      norm_num
    have hstep : ((2 : ℝ) ^ (N + k))⁻¹ * (Real.log 2 + (2 : ℝ) ^ k * Real.log (‖orbit c w N‖ / 2))
        ≤ ((2 : ℝ) ^ (N + k))⁻¹ * Real.posLog ‖orbit c w (N + k)‖ :=
      mul_le_mul_of_nonneg_left (by rw [← hplog]; exact hple) (by positivity)
    have hexp : ((2 : ℝ) ^ (N + k))⁻¹ * (Real.log 2 + (2 : ℝ) ^ k * Real.log (‖orbit c w N‖ / 2))
        = ((2 : ℝ) ^ N)⁻¹ * (((2 : ℝ) ^ k)⁻¹ * Real.log 2 + Real.log (‖orbit c w N‖ / 2)) := by
      rw [pow_add]
      field_simp
    rw [greenSeq]
    calc ((2 : ℝ) ^ N)⁻¹ * Real.log (‖orbit c w N‖ / 2)
        ≤ ((2 : ℝ) ^ N)⁻¹ * (((2 : ℝ) ^ k)⁻¹ * Real.log 2 + Real.log (‖orbit c w N‖ / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ * Real.log 2 := by positivity
          linarith
      _ = ((2 : ℝ) ^ (N + k))⁻¹ * (Real.log 2 + (2 : ℝ) ^ k * Real.log (‖orbit c w N‖ / 2)) :=
          hexp.symm
      _ ≤ ((2 : ℝ) ^ (N + k))⁻¹ * Real.posLog ‖orbit c w (N + k)‖ := hstep
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((2 : ℝ) ^ N)⁻¹ * Real.log (‖orbit c w N‖ / 2) ≤ greenSeq c w n := by
    rw [Filter.eventually_atTop]
    exact ⟨N, fun n hn => by
      have hh := hkey (n - N)
      rwa [Nat.add_sub_of_le hn] at hh⟩
  have hB : ∀ n : ℕ, greenSeq c w n ≤ Real.log (2 * (‖w‖ + (‖c‖ + 1))) :=
    GreenGrowth.greenSeq_le_log c w
  -- a limsup dominates every eventual lower bound
  have hδle : ((2 : ℝ) ^ N)⁻¹ * Real.log (‖orbit c w N‖ / 2) ≤ greenFun c w := by
    rw [greenFun, Filter.limsup_eq]
    refine le_csInf ⟨Real.log (2 * (‖w‖ + (‖c‖ + 1))), Filter.Eventually.of_forall hB⟩ ?_
    intro b hb
    obtain ⟨n, hn1, hn2⟩ := (hev.and hb).exists
    exact le_trans hn1 hn2
  have hpos : 0 < ((2 : ℝ) ^ N)⁻¹ * Real.log (‖orbit c w N‖ / 2) := by
    have := Real.log_pos (by linarith : (1 : ℝ) < ‖orbit c w N‖ / 2)
    positivity
  linarith

end Work.ParamRays
