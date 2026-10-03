import Mathlib
import Submission.Work.Pert.V5.W2.Setup
import Submission.Work.Pert.I_mul_half_eta_mem_Qm

namespace Work.Pert.V5.W2

open Set Metric

noncomputable section

/-!
# `Work.Pert.V5.W2.bad_in_window`

The "bad" (`mgB`-small) piece of the corridor is the half-line at height `y₀ = z₀.im` to the left
of `ξ_B := |y₀| - Ξ - √2 Rde`.  We show that the whole window at that height, i.e. the whole
interval `[ξ_B, x]`, sits strictly inside the *window strip*

  `(Ξ - Re(1/α) + 1, -Ξ - 3)`

of the derivative estimate `deriv_sub_one_le_window` (`‖Φm' - 1‖ ≤ c₀`).

The right end is immediate from `x ≤ -(Ξ + 2 ^ 10)`.  The left end is the content: it only uses
the clearing hypothesis `hcl` at the pin, through `zo_margins`
(`mgA z₀ > 2 Rde + 2`, `mgB z₀ > 2 Rde + 2`), together with `Re(1/α) ≥ 16 √2 Ξ`
(`InF1 α` plus `‖α‖ ≤ 1/(32 (M+2+Ξ))`).

Concretely, with `A := Re(1/α)`, `B := Im(1/α)`, `y := |z₀.im|` and `m := Ξ + 2 Rde + 2`, the two
marginal inequalities read

  `z₀.re + A + |z₀.im + B| > m`,   `y - z₀.re > m`,

whence `A + |z₀.im + B| + y > 2m`, and since `|z₀.im + B| ≤ y + |B| ≤ y + A` we get

  `y > Ξ + 2 Rde + 2 - A`.   (★)

To reach the required `y > 2Ξ - A + 1 + √2 Rde` we split on `Ξ ≤ (2-√2) Rde + 1`:

* if `Ξ ≤ (2-√2) Rde + 1` then `Ξ + 2 Rde + 2 - A ≥ 2Ξ - A + 1 + √2 Rde` and (★) finishes;
* otherwise `(2-√2) Rde < Ξ - 1`, and since `√2 = (2-√2)(1+√2)`, multiplying by `1 + √2 > 0`
  gives `√2 Rde < (1+√2)(Ξ-1)`, so
  `2Ξ - A + 1 + √2 Rde < (3+√2) Ξ - A - √2 ≤ (3+√2)Ξ - 16√2 Ξ - √2 < 0 ≤ y`.
-/

/-- **`Re(1/α)` dominates `16 √2 Ξ`.**  `InF1 α` puts the inverted sector in itself
(`band_Qm_inv_re_lower`: `1/(√2 ‖α‖) ≤ Re(1/α)`), and `‖α‖ · 32 (M + 2 + Ξ) ≤ 1`. -/
lemma inv_re_ge_mul {Ξ M : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) :
    16 * Real.sqrt 2 * Ξ ≤ (1 / α).re := by
  have hM0 : (0 : ℝ) < M := by
    have h : (0 : ℝ) < 2 ^ 10 := by norm_num
    linarith
  have hX : 0 < M + 2 + Ξ := by linarith
  have hX32 : 0 < 32 * (M + 2 + Ξ) := by linarith
  have hne : α ≠ 0 := by
    have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
    intro h; rw [h] at hre; simp at hre
  have hnorm : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have h1 : 1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := Work.Pert.band_Qm_inv_re_lower hInF1
  have hmul : ‖α‖ * (32 * (M + 2 + Ξ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hα hX32.le
    rwa [one_div, inv_mul_cancel₀ hX32.ne'] at h
  have h2 : 16 * Real.sqrt 2 * (M + 2 + Ξ) ≤ 1 / (Real.sqrt 2 * ‖α‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2 * ‖α‖)]
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have heq : 16 * Real.sqrt 2 * (M + 2 + Ξ) * (Real.sqrt 2 * ‖α‖)
        = ‖α‖ * (32 * (M + 2 + Ξ)) := by
      calc 16 * Real.sqrt 2 * (M + 2 + Ξ) * (Real.sqrt 2 * ‖α‖)
          = 16 * (Real.sqrt 2 * Real.sqrt 2) * ((M + 2 + Ξ) * ‖α‖) := by ring
        _ = 16 * 2 * ((M + 2 + Ξ) * ‖α‖) := by rw [hs2]
        _ = ‖α‖ * (32 * (M + 2 + Ξ)) := by ring
    rw [heq]
    linarith
  have h3 : 16 * Real.sqrt 2 * Ξ ≤ 16 * Real.sqrt 2 * (M + 2 + Ξ) :=
    mul_le_mul_of_nonneg_left (by linarith : Ξ ≤ M + 2 + Ξ) (by positivity)
  linarith

/-- **The left edge of the window lies strictly below `ξ_B`.**  This is the inequality that makes
the whole interval `[ξ_B, x]` lie in the window strip. -/
lemma edge_lt_xiB {Ξ M Rde : ℝ} {α : ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α) :
    ((Ξ : ℂ) - 1 / α).re + 1 < |z₀.im| - Ξ - Real.sqrt 2 * Rde := by
  have hA : 16 * Real.sqrt 2 * Ξ ≤ (1 / α).re := inv_re_ge_mul hΞ hM hInF1 hα
  have hB : |(1 / α).im| ≤ (1 / α).re := Work.Pert.abs_im_one_div_le_re_one_div hInF1
  have hres : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by simp
  rw [hres]
  obtain ⟨hmA, hmB⟩ := zo_margins hRde hcl
  simp only [mgA] at hmA
  simp only [mgB] at hmB
  have hy : Ξ + 2 * Rde + 2 - (1 / α).re < |z₀.im| := by
    have htri : |z₀.im + (1 / α).im| ≤ |z₀.im| + |(1 / α).im| := abs_add_le _ _
    linarith
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hpos1 : 0 < 1 + Real.sqrt 2 := by linarith
  have hG : 2 * Ξ - (1 / α).re + 1 + Real.sqrt 2 * Rde < |z₀.im| := by
    rcases le_or_gt Ξ ((2 - Real.sqrt 2) * Rde + 1) with hcase | hcase
    · have hle : 2 * Ξ - (1 / α).re + 1 + Real.sqrt 2 * Rde
          ≤ Ξ + 2 * Rde + 2 - (1 / α).re := by nlinarith [hcase]
      linarith
    · have hcase' : (2 - Real.sqrt 2) * Rde < Ξ - 1 := by linarith
      have hident : (2 - Real.sqrt 2) * (1 + Real.sqrt 2) = Real.sqrt 2 := by
        nlinarith [hs2]
      have hR' : Real.sqrt 2 * Rde < (1 + Real.sqrt 2) * (Ξ - 1) := by
        have hm := mul_lt_mul_of_pos_right hcase' hpos1
        have heq : ((2 - Real.sqrt 2) * Rde) * (1 + Real.sqrt 2) = Real.sqrt 2 * Rde := by
          calc ((2 - Real.sqrt 2) * Rde) * (1 + Real.sqrt 2)
              = ((2 - Real.sqrt 2) * (1 + Real.sqrt 2)) * Rde := by ring
            _ = Real.sqrt 2 * Rde := by rw [hident]
        rw [heq] at hm
        linarith
      have hneg : 2 * Ξ - (1 / α).re + 1 + Real.sqrt 2 * Rde < 0 := by
        have hb : (3 + Real.sqrt 2) * Ξ - (1 / α).re - Real.sqrt 2 < 0 := by
          nlinarith [hA, hs2pos, hΞ, hs2]
        nlinarith [hR', hb, hs2]
      linarith [abs_nonneg z₀.im]
  linarith

theorem bad_in_window {Ξ M Rde : ℝ} {α : ℂ} {z₀ : ℂ} {x : ℝ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hxhi : x ≤ -(Ξ + 2 ^ 10)) (hx₀ : z₀.re ≤ x)
    (hxiB : |z₀.im| - Ξ - Real.sqrt 2 * Rde < x) :
    ∀ ξ ∈ Set.Icc (|z₀.im| - Ξ - Real.sqrt 2 * Rde) x,
      ((Ξ : ℂ) - 1 / α).re + 1 < ξ ∧ ξ < -Ξ - 3 := by
  have hedge := edge_lt_xiB hΞ hM hInF1 hα hRde hcl
  intro ξ hξ
  refine ⟨lt_of_lt_of_le hedge hξ.1, ?_⟩
  have hlt : -(Ξ + 2 ^ 10) < -Ξ - 3 := by
    have h : (2 : ℝ) ^ 10 = 1024 := by norm_num
    linarith
  exact lt_of_le_of_lt (le_trans hξ.2 hxhi) hlt

end

end Work.Pert.V5.W2
