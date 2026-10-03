/-
# `Submission.Work.FIArea5.HeckeZFR.GammaLogBound`

A **Stirling-type upper bound for `log ‖Γ(w)‖` on the whole half-plane `re w ≥ 1/2`**:

  `log ‖Γ w‖ ≤ C · (1 + (re w + 1)·(1 + log(2 + ‖w‖)))`,

with `C` absolute.  The sharp vertical bound `Gamma_vertical_upper_uniform_sharp` covers only
`1/2 ≤ re w ≤ 2`; for larger real part the recurrence `Γ(w) = Γ(w-k)·∏_{j<k}(w-1-j)` (with
`w - k ∈ [1/2, 3/2)`) reduces to that case at the cost of `k log(2 + ‖w‖)`, and `k ≤ re w`.

This is what turns the strip bounds for the Hecke `L`-function into the **circle growth** of the
completion `Λ(s) = (4d/π)^s Γ(s + m/2)L(s,ψ)` needed by the Hadamard partial fraction.
-/
import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea5.S16Hecke

open Complex
open scoped Real

noncomputable section

/-- The iterated recurrence `Γ(w) = Γ(w - k)·∏_{j<k}(w - 1 - j)`. -/
lemma Gamma_eq_Gamma_sub_mul_prod {w : ℂ} {k : ℕ}
    (hw : ∀ j : ℕ, j ≤ k → w - (j : ℂ) ≠ 0) :
    Complex.Gamma w = Complex.Gamma (w - (k : ℂ))
      * ∏ j ∈ Finset.range k, (w - 1 - (j : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : w - ((k + 1 : ℕ) : ℂ) ≠ 0 := hw (k + 1) (le_refl _)
    have hstep : Complex.Gamma (w - (k : ℂ))
        = (w - ((k + 1 : ℕ) : ℂ)) * Complex.Gamma (w - ((k + 1 : ℕ) : ℂ)) := by
      have h1 := Complex.Gamma_add_one (w - ((k + 1 : ℕ) : ℂ)) hne
      rw [show w - ((k + 1 : ℕ) : ℂ) + 1 = w - (k : ℂ) from by push_cast; ring] at h1
      exact h1
    rw [ih (fun j hj => hw j (le_trans hj (Nat.le_succ k))),
      Finset.prod_range_succ, hstep]
    push_cast
    ring

/-- **Stirling-type upper bound** `log ‖Γ w‖ ≤ C (1 + (re w + 1)(1 + log(2 + ‖w‖)))` on the
half-plane `re w ≥ 1/2`. -/
theorem Gamma_log_norm_le_vertical :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, (1 : ℝ) / 2 ≤ w.re →
      Real.log ‖Complex.Gamma w‖ ≤ C * (1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨2 * (C₀ + 4), by positivity, ?_⟩
  intro w hw
  set k : ℕ := ⌊w.re - 1 / 2⌋₊ with hk
  have hk1 : (k : ℝ) ≤ w.re - 1 / 2 := Nat.floor_le (by linarith)
  have hk2 : w.re - 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one (w.re - 1 / 2)
  have hvr : (1 : ℝ) / 2 ≤ w.re - (k : ℝ) := by linarith
  have hvr2 : w.re - (k : ℝ) < 3 / 2 := by linarith
  -- no zeros at the shifted points
  have hne : ∀ j : ℕ, j ≤ k → w - (j : ℂ) ≠ 0 := by
    intro j hjle hjzero
    have hre : w.re - (j : ℝ) = 0 := by simpa using congrArg Complex.re hjzero
    have hkR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjle
    linarith [hvr, hre]
  have hfac : Complex.Gamma w = Complex.Gamma (w - (k : ℂ))
      * ∏ j ∈ Finset.range k, (w - 1 - (j : ℂ)) := Gamma_eq_Gamma_sub_mul_prod hne
  -- the shifted Γ
  have hwkre : (w - (k : ℂ)).re = w.re - (k : ℝ) := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]
  have hwkim : (w - (k : ℂ)).im = w.im := by simp
  have hGk : ‖Complex.Gamma (w - (k : ℂ))‖
      ≤ C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)
        * Real.exp (-(Real.pi / 2) * |w.im|) := by
    have h := hC₀ (w.re - (k : ℝ)) w.im hvr (by linarith)
    rwa [show ((w.re - (k : ℝ) : ℝ) : ℂ) + (w.im : ℂ) * I = w - (k : ℂ) from by
      apply Complex.ext <;> simp [hwkre, hwkim]] at h
  -- the product of shift factors
  have hprod : ∀ z ∈ Finset.range k, ‖w - 1 - (z : ℂ)‖ ≤ 2 * (2 + ‖w‖) := by
    intro z hz
    rw [Finset.mem_range] at hz
    have hz0 : (z : ℝ) < (k : ℝ) := by exact_mod_cast hz
    have h1 : ‖w - 1 - (z : ℂ)‖ ≤ ‖w‖ + 1 + (z : ℝ) := by
      calc ‖w - 1 - (z : ℂ)‖ = ‖(w - 1) - (z : ℂ)‖ := by rw [sub_sub]
        _ ≤ ‖w - 1‖ + ‖(z : ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖w‖ + 1) + (z : ℝ) := by
            have h3 : ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w (1 : ℂ)
            rw [Complex.norm_natCast]
            linarith
    have h4 : ‖w‖ + 1 + (z : ℝ) ≤ 2 * (2 + ‖w‖) := by
      have h7 : (k : ℝ) ≤ w.re := by linarith
      have h8 : w.re ≤ ‖w‖ := Complex.re_le_norm w
      linarith
    linarith
  have hposfac : ∀ z ∈ Finset.range k, 0 < ‖w - 1 - (z : ℂ)‖ := by
    intro z hz
    rw [Finset.mem_range] at hz
    refine norm_pos_iff.mpr ?_
    intro hcontra
    exact hne (z + 1) (Nat.succ_le_of_lt hz) (by
      rw [show w - ((z + 1 : ℕ) : ℂ) = w - 1 - (z : ℂ) from by push_cast; ring]
      exact hcontra)
  -- the log of the product
  have h2 : Real.log (∏ j ∈ Finset.range k, ‖w - 1 - (j : ℂ)‖)
      ≤ (k : ℝ) * Real.log (2 * (2 + ‖w‖)) := by
    rw [Real.log_prod (fun z hz => ne_of_gt (hposfac z hz))]
    calc ∑ z ∈ Finset.range k, Real.log ‖w - 1 - (z : ℂ)‖
        ≤ ∑ _z ∈ Finset.range k, Real.log (2 * (2 + ‖w‖)) :=
          Finset.sum_le_sum (fun z hz => Real.log_le_log (hposfac z hz) (hprod z hz))
      _ = (k : ℝ) * Real.log (2 * (2 + ‖w‖)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hGpos : (0 : ℝ) < ‖Complex.Gamma (w - (k : ℂ))‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [hwkre]; linarith)
  have h1 : Real.log ‖Complex.Gamma (w - (k : ℂ))‖
      ≤ Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)
          * Real.exp (-(Real.pi/2) * |w.im|)) :=
    Real.log_le_log hGpos hGk
  have hlognorm : Real.log ‖Complex.Gamma w‖
      ≤ Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)
          * Real.exp (-(Real.pi/2) * |w.im|)) + (k : ℝ) * Real.log (2 * (2 + ‖w‖)) := by
    rw [hfac, norm_mul, norm_prod,
      Real.log_mul (ne_of_gt hGpos) (ne_of_gt (Finset.prod_pos hposfac))]
    linarith [h1, h2]
  -- final arithmetic
  have hkw : (k : ℝ) ≤ w.re := by linarith
  have hlogpos : (0 : ℝ) < Real.log (2 + ‖w‖) :=
    Real.log_pos (by have := norm_nonneg w; linarith)
  have hlog2 : (1 : ℝ) ≤ 1 + Real.log (2 + ‖w‖) := by linarith
  have hargpos : (0 : ℝ) < 2 * (2 + ‖w‖) := by have := norm_nonneg w; linarith
  have hlogd : Real.log (2 * (2 + ‖w‖)) ≤ 1 + Real.log (2 + ‖w‖) := by
    rw [Real.log_mul (by norm_num) (by have := norm_nonneg w; linarith)]
    have h9 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hprodle : (k : ℝ) * Real.log (2 * (2 + ‖w‖))
      ≤ (C₀ + 4) * (1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖))) := by
    have hL0 : (0 : ℝ) ≤ Real.log (2 * (2 + ‖w‖)) := Real.log_nonneg (by
      have := norm_nonneg w; linarith)
    have hwr : (0 : ℝ) ≤ w.re := le_trans (by norm_num) hw
    have hA : (0 : ℝ) ≤ 1 + Real.log (2 + ‖w‖) := by linarith
    have h1 : (k : ℝ) * Real.log (2 * (2 + ‖w‖)) ≤ w.re * (1 + Real.log (2 + ‖w‖)) := by
      calc (k : ℝ) * Real.log (2 * (2 + ‖w‖)) ≤ w.re * Real.log (2 * (2 + ‖w‖)) :=
            mul_le_mul_of_nonneg_right hkw hL0
        _ ≤ w.re * (1 + Real.log (2 + ‖w‖)) := mul_le_mul_of_nonneg_left hlogd hwr
    have h2 : w.re * (1 + Real.log (2 + ‖w‖))
        ≤ (w.re + 1) * (1 + Real.log (2 + ‖w‖)) :=
      mul_le_mul_of_nonneg_right (by linarith) hA
    have h3 : (1 : ℝ) ≤ 1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖)) := by
      have : (1 : ℝ) ≤ (w.re + 1) * (1 + Real.log (2 + ‖w‖)) := by
        have h4 : (1 : ℝ) ≤ w.re + 1 := by linarith
        have h5 : (1 : ℝ) ≤ 1 + Real.log (2 + ‖w‖) := by linarith
        nlinarith [h4, h5]
      linarith
    have hX : (w.re + 1) * (1 + Real.log (2 + ‖w‖))
        ≤ 1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖)) := by linarith
    nlinarith [h1, h2, h3, hX, hC₀pos]
  -- the Γ term
  have hΓle : Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)
        * Real.exp (-(Real.pi/2) * |w.im|))
      ≤ (C₀ + 4) * (1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖))) := by
    have hexp : Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)
          * Real.exp (-(Real.pi/2) * |w.im|))
        ≤ Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)) := by
      refine Real.log_le_log (by positivity) ?_
      refine mul_le_of_le_one_right (by positivity) ?_
      exact Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ |w.im| := abs_nonneg _
        nlinarith [Real.pi_pos])
    have hsplit : Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2))
        = Real.log C₀ + (w.re - (k : ℝ) - 1 / 2) * Real.log (1 + |w.im|) := by
      rw [Real.log_mul (ne_of_gt hC₀pos) (by positivity), Real.log_rpow (by positivity)]
    have hlogC₀ : Real.log C₀ ≤ C₀ := by
      have h1' : C₀ ≤ Real.exp C₀ := by have := Real.add_one_le_exp C₀; linarith
      have h2' : Real.log C₀ ≤ Real.log (Real.exp C₀) := Real.log_le_log hC₀pos h1'
      rwa [Real.log_exp] at h2'
    have hlog3 : Real.log (1 + |w.im|) ≤ Real.log (2 + ‖w‖) := by
      refine Real.log_le_log (by positivity) ?_
      have := Complex.abs_im_le_norm w
      linarith
    have hcoef : w.re - (k : ℝ) - 1 / 2 ≤ w.re + 1 := by linarith
    have hnn : (0 : ℝ) ≤ w.re - (k : ℝ) - 1 / 2 := by linarith
    have hlog30 : (0 : ℝ) ≤ Real.log (1 + |w.im|) := Real.log_nonneg (by
      have : (0:ℝ) ≤ |w.im| := abs_nonneg _
      linarith)
    have hkey : (w.re - (k : ℝ) - 1 / 2) * Real.log (1 + |w.im|)
        ≤ (w.re + 1) * (1 + Real.log (2 + ‖w‖)) := by
      have h4 : (w.re - (k : ℝ) - 1 / 2) * Real.log (1 + |w.im|)
          ≤ (w.re - (k : ℝ) - 1 / 2) * Real.log (2 + ‖w‖) :=
        mul_le_mul_of_nonneg_left hlog3 hnn
      have h5 : (w.re - (k : ℝ) - 1 / 2) * Real.log (2 + ‖w‖)
          ≤ (w.re + 1) * Real.log (2 + ‖w‖) :=
        mul_le_mul_of_nonneg_right hcoef (Real.log_nonneg (by
          have := norm_nonneg w; linarith))
      have hwr : (0 : ℝ) ≤ w.re := le_trans (by norm_num) hw
      nlinarith [h4, h5, hlogpos, hwr]
    have hwr : (0 : ℝ) ≤ w.re := le_trans (by norm_num) hw
    have hX1 : (1 : ℝ) ≤ 1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖)) := by
      have h4 : (1 : ℝ) ≤ w.re + 1 := by linarith
      have h5 : (1 : ℝ) ≤ 1 + Real.log (2 + ‖w‖) := by linarith
      nlinarith [h4, h5]
    nlinarith [hexp, hsplit.le, hsplit.ge, hlogC₀, hkey, hlogpos, hwr, hC₀pos, hX1]
  refine hlognorm.trans ?_
  calc Real.log (C₀ * (1 + |w.im|) ^ (w.re - (k : ℝ) - 1 / 2)
        * Real.exp (-(Real.pi/2) * |w.im|)) + (k : ℝ) * Real.log (2 * (2 + ‖w‖))
      ≤ (C₀ + 4) * (1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖)))
        + (C₀ + 4) * (1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖))) :=
        add_le_add hΓle hprodle
    _ = 2 * (C₀ + 4) * (1 + (w.re + 1) * (1 + Real.log (2 + ‖w‖))) := by ring

end

end Work.FIArea5.S16Hecke
