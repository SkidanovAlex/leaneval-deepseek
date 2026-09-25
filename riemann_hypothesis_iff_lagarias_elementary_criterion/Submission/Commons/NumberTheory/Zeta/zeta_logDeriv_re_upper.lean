import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound

noncomputable section
open Complex Filter Metric Set
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

/-!
# `zeta_logDeriv_re_upper` (upper bound for the real part of `−ζ′/ζ` above `Re = 1`)

**Target.**  There are `C > 0` and `H ≥ 2` such that for all `H ≤ |t|` and all
`1 < σ ≤ 2`, writing `s = σ + i·t`,

`Re(−ζ′(s)/ζ(s)) ≤ C·(log(|t| + 3) + 1)`.

**Proof structure.**  By the published "regular part" estimate
`Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound` (whose proof runs through the
Hadamard partial fraction of the completed zeta `ξ(s) = (1/2)·s·(s−1)·Λ(s)`, every zero
summand being non-negative on `Re s > 1`),

`Re(−ζ′(s)/ζ(s)) ≤ C₀ + ½·Re(ψ(1 + s/2))`   (`ψ = Γ′/Γ`).

The digamma term is bounded by the (published) vertical bound
`Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound`:
for `x = Re(1 + s/2) = 1 + σ/2 ∈ [3/2, 2] ⊂ [1/4, 8]` and `y = Im(1 + s/2) = t/2`,

`Re ψ(1 + s/2) ≤ ‖ψ(1 + s/2)‖ ≤ log(2 + |t|/2) + 8 ≤ log(|t| + 3) + 8`.

Substituting and rearranging (with `log(|t| + 3) + 1 ≥ 1`) yields
`Re(−ζ′(s)/ζ(s)) ≤ (C₀ + 8)·(log(|t| + 3) + 1)`.  All that remains below is bookkeeping.
-/

/-- real part of `s/2` is `s.re/2` -/
private lemma re_half (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/-- imaginary part of `s/2` is `s.im/2` -/
private lemma im_half (s : ℂ) : (s / 2).im = s.im / 2 := by
  rw [Complex.div_im]
  norm_num
  ring

/-- real part of `1 + (σ + i·t)/2` -/
private lemma psi_arg_re (σ t : ℝ) :
    (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)).re = 1 + σ / 2 := by
  rw [Complex.add_re, re_half]
  simp

/-- imaginary part of `1 + (σ + i·t)/2` -/
private lemma psi_arg_im (σ t : ℝ) :
    (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)).im = t / 2 := by
  rw [Complex.add_im, im_half]
  simp

/-- `log(2 + |t|/2) ≤ log(|t| + 3)` -/
private lemma log_sub_le (t : ℝ) : Real.log (2 + |t| / 2) ≤ Real.log (|t| + 3) := by
  apply Real.log_le_log
  · linarith [abs_nonneg t]
  · nlinarith [abs_nonneg t]

/-- **Uniform real-part upper bound for `−ζ′/ζ` above the line `Re = 1`.**

`Re(−ζ′(s)/ζ(s)) ≤ C·(log(|t| + 3) + 1)` for `s = σ + i·t`, `H ≤ |t|`, `1 < σ ≤ 2`. -/
theorem zeta_logDeriv_re_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
          C * (Real.log (|t| + 3) + 1) := by
  rcases zeta_logDeriv_re_regular_bound with ⟨C0, hC0pos, H0, hH0, hCore⟩
  let C : ℝ := C0 + 8
  refine ⟨C, by dsimp [C]; linarith, max H0 2, by exact le_trans hH0 (le_max_left H0 2), ?_⟩
  intro t ht σ hσ1 hσ2
  let x : ℝ := 1 + σ / 2
  let y : ℝ := t / 2
  have hxy : (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)) =
      (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [x, y]
  have hx1 : (1 / 4 : ℝ) ≤ x := by
    have hσpos : 0 < σ := by linarith
    dsimp [x]
    nlinarith
  have hx2 : x ≤ 8 := by
    dsimp [x]
    nlinarith
  have hpsi := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound x y hx1 hx2
  have hpsi_w : (Complex.digamma (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).re ≤
      Real.log (2 + |y|) + 8 := by
    calc
      (Complex.digamma (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).re
          ≤ ‖Complex.digamma (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))‖ :=
            Complex.re_le_norm _
      _ = ‖Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by rw [hxy]
      _ ≤ Real.log (2 + |y|) + 8 := hpsi
  have hpsi2 : (1 / 2) * (Complex.digamma (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).re ≤
      (1 / 2) * (Real.log (2 + |t| / 2) + 8) := by
    have hy : |y| = |t| / 2 := by
      dsimp [y]
      rw [abs_div]
      norm_num
    have hw : Real.log (2 + |y|) + 8 ≤ Real.log (2 + |t| / 2) + 8 := by rw [hy]
    exact mul_le_mul_of_nonneg_left (le_trans hpsi_w hw) (by norm_num)
  have hmain := hCore t (by exact le_trans (le_max_left H0 2) ht) σ hσ1 hσ2
  have hmain' : (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
      riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
      C0 + (1 / 2) * (Real.log (2 + |t| / 2) + 8) := by
    calc
      (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
          C0 + (1 / 2) * (Complex.digamma
            (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).re := by simpa using hmain
      _ ≤ C0 + (1 / 2) * (Real.log (2 + |t| / 2) + 8) := by
        exact add_le_add (le_rfl : C0 ≤ C0) hpsi2
  let L : ℝ := Real.log (|t| + 3) + 1
  have hL1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by nlinarith [abs_nonneg t])
    linarith
  have hA : C0 ≤ C0 * L := by
    exact le_mul_of_one_le_right (le_of_lt hC0pos) hL1
  have hlog : Real.log (2 + |t| / 2) + 8 ≤ Real.log (|t| + 3) + 9 := by
    have := log_sub_le t
    linarith
  have hB : (1 / 2) * (Real.log (2 + |t| / 2) + 8) ≤ (8 : ℝ) * L := by
    have hstep : (1 / 2) * (Real.log (|t| + 3) + 9) ≤ (8 : ℝ) * L := by
      dsimp [L]
      nlinarith
    calc
      (1 / 2) * (Real.log (2 + |t| / 2) + 8) ≤ (1 / 2) * (Real.log (|t| + 3) + 9) := by
        exact mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ ≤ (8 : ℝ) * L := hstep
  calc
    (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
        C0 + (1 / 2) * (Real.log (2 + |t| / 2) + 8) := hmain'
    _ ≤ C0 * L + (8 : ℝ) * L := by
      have hC0L : C0 ≤ C0 * L := hA
      nlinarith
    _ = (C0 + 8) * L := by ring
    _ = C * L := by rfl

end Commons.NumberTheory.Zeta
