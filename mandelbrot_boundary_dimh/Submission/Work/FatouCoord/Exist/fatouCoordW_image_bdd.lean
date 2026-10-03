import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Exist.fatouCoordW_differentiable
import Submission.Work.FatouCoord.Exist.fatouCoordW_deriv_close
import Submission.Work.FatouCoord.Exist.fatouCoordW_tsum_bound
import Submission.Work.FatouCoord.Exist.exists_eq_of_deriv_close
import Submission.Work.FatouCoord.Exist.exists_threshold_log_linear

namespace Work.FatouCoord.Exist

open Work.FatouCoord

/-!
# The Fatou coordinate in the chart is onto a right half-plane, with large preimages

For a parabolic germ `f z = z + z ^ 2 * h z` with `h 0 = 1` (quantified by `ParabolicBounds`)
we show that the Fatou coordinate in the chart `w = -1/z`,

`ψ w = fatouCoordW f (1 - a) w = w - (1 - a) log w + O(1/Re w)`,

takes every value `τ` of a truncated right half-plane `{Re τ > C}` whose imaginary part is
bounded by `B`, and that the preimage can be taken with `Re w` larger than any prescribed `R`.
In other words, for every `R` and `B` there is `C` such that

`{τ : |Im τ| ≤ B, Re τ > C} ⊆ ψ {Re w > R}`.

The mechanism is the classical fixed-point argument.  On a right half-plane the derivative of
`ψ` differs from `1` by at most `1/2` (`fatouCoordW_deriv_close`), so the map
`T w = w - (ψ w - τ)` is a `1/2`-contraction there, and `ψ w = τ` is exactly `T w = w`.  The
remainder of `ψ - id` is `O(1/Re w)` (`fatouCoordW_tsum_bound`), while the explicit term
`- (1 - a) log w` varies only by `O(log |τ|)` across the ball of radius `O(log |τ|)` around `τ`;
hence the contraction has a fixed point near `τ` as soon as `Re τ` is large enough, and that
fixed point still has real part `≥ Re τ - O(log Re τ)`, which tends to `+∞`.
-/

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Bound on the principal logarithm: for `‖z‖ ≥ 1`, `‖log z‖ ≤ log ‖z‖ + π`. -/
lemma norm_log_le (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have h2 : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
  have h3 : |(Complex.log z).im| ≤ Real.pi := by
    rw [Complex.log_im]; exact Complex.abs_arg_le_pi z
  have h4 : (0 : ℝ) ≤ Real.log ‖z‖ := Real.log_nonneg hz
  rw [h2, abs_of_nonneg h4] at h1
  linarith

theorem fatouCoordW_image_bdd {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∀ (R B : ℝ), ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ w : ℂ, R < w.re ∧ fatouCoordW f (1 - a) w = τ := by
  intro R B
  obtain ⟨Nd, hNdpos, hNdr, hdiffd⟩ := fatouCoordW_differentiable hb
  obtain ⟨Nc, hNcpos, hNcr, hderc⟩ := fatouCoordW_deriv_close hb
  obtain ⟨Nb, K, hNbpos, hNbr, hKnn, hbdd⟩ := fatouCoordW_tsum_bound hb
  set N : ℝ := max (max Nd Nc) Nb + 1 with hNdef
  have hNdN : Nd < N := by
    have h : Nd ≤ max (max Nd Nc) Nb := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hNdef]; linarith
  have hNcN : Nc < N := by
    have h : Nc ≤ max (max Nd Nc) Nb := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [hNdef]; linarith
  have hNbN : Nb < N := by
    have h : Nb ≤ max (max Nd Nc) Nb := le_max_right _ _
    rw [hNdef]; linarith
  have hNpos : 0 < N := by
    rw [hNdef]; positivity
  set c : ℝ := ‖(1 : ℂ) - a‖ with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; exact norm_nonneg _
  set c1 : ℝ := 2 * c + 4 with hc1def
  set c2 : ℝ := 2 * c * Real.pi + 4 * K + 100 with hc2def
  have hc1pos : 0 < c1 := by rw [hc1def]; linarith
  have hc2pos : 0 < c2 := by
    rw [hc2def]
    have h1 : 0 ≤ c * Real.pi := mul_nonneg hcnn Real.pi_pos.le
    linarith
  by_cases hBneg : B < 0
  · -- the strip is empty
    refine ⟨0, ?_⟩
    intro τ _ him
    have h0 : (0 : ℝ) ≤ |τ.im| := abs_nonneg _
    linarith
  · have hBnn : 0 ≤ B := not_lt.mp hBneg
    obtain ⟨C₀, hC₀⟩ :=
      exists_threshold_log_linear (B := B) (M := max N R + 3) (c := c) (K := K) hBnn hcnn hKnn
    refine ⟨max (max C₀ N) (max R 1), ?_⟩
    intro τ hτ him
    have hτC₀ : C₀ < τ.re :=
      lt_of_le_of_lt (le_trans (le_max_left C₀ N) (le_max_left (max C₀ N) (max R 1))) hτ
    have hτN : N < τ.re :=
      lt_of_le_of_lt (le_trans (le_max_right C₀ N) (le_max_left (max C₀ N) (max R 1))) hτ
    have hτ1 : 1 ≤ τ.re :=
      le_of_lt (lt_of_le_of_lt (le_trans (le_max_right R 1) (le_max_right (max C₀ N) (max R 1))) hτ)
    have hτpos : 0 < τ.re := lt_of_lt_of_le zero_lt_one hτ1
    have hnormτ_pos : 0 < ‖τ‖ := lt_of_lt_of_le hτpos (Complex.re_le_norm τ)
    have hnormτ_ge1 : 1 ≤ ‖τ‖ := le_trans hτ1 (Complex.re_le_norm τ)
    have hnormτ_le : ‖τ‖ ≤ τ.re + B := by
      have h := Complex.norm_le_abs_re_add_abs_im τ
      rw [abs_of_pos hτpos] at h
      linarith
    have hlogmono : Real.log ‖τ‖ ≤ Real.log (τ.re + B) := by
      refine Real.log_le_log hnormτ_pos ?_
      linarith
    have hlogτ_nn : 0 ≤ Real.log ‖τ‖ := Real.log_nonneg hnormτ_ge1
    have hlogle : ‖Complex.log τ‖ ≤ Real.log ‖τ‖ + Real.pi := norm_log_le τ hnormτ_ge1
    -- the radius of the ball on which we solve `ψ w = τ`
    set ρ : ℝ := c1 * Real.log ‖τ‖ + c2 with hρdef
    have hρpos : 0 < ρ := by
      have h1 : 0 ≤ c1 * Real.log ‖τ‖ := mul_nonneg (le_of_lt hc1pos) hlogτ_nn
      rw [hρdef]; linarith
    have hC₀' := hC₀ τ.re hτC₀
    rw [← hc1def, ← hc2def] at hC₀'
    have hρlt : ρ + (max N R + 3) < τ.re := by
      have h2 : c1 * Real.log ‖τ‖ ≤ c1 * Real.log (τ.re + B) :=
        mul_le_mul_of_nonneg_left hlogmono (le_of_lt hc1pos)
      rw [hρdef]; linarith
    have hMlt : max N R + 3 ≤ τ.re - ρ := by linarith [hρlt]
    -- `ψ τ` is within `ρ / 2` of `τ`
    have hKbd : ‖fatouCoordW f (1 - a) τ - approxCoord (1 - a) τ‖ ≤ K / τ.re :=
      hbdd τ (lt_trans hNbN hτN)
    have hsplit : fatouCoordW f (1 - a) τ - τ
        = (approxCoord (1 - a) τ - τ) + (fatouCoordW f (1 - a) τ - approxCoord (1 - a) τ) := by
      ring
    have hlinterm : approxCoord (1 - a) τ - τ = -((1 - a) * Complex.log τ) := by
      rw [approxCoord_apply]; ring
    have hbound1 : ‖fatouCoordW f (1 - a) τ - τ‖ ≤ c * ‖Complex.log τ‖ + K / τ.re := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [hlinterm, norm_neg, norm_mul, ← hcdef]
      linarith
    have hcK : c * ‖Complex.log τ‖ + K / τ.re ≤ c * (Real.log ‖τ‖ + Real.pi) + K := by
      have h1 : K / τ.re ≤ K := by
        rw [div_le_iff₀ hτpos]
        nlinarith [hKnn, hτ1]
      have h2 := mul_le_mul_of_nonneg_left hlogle hcnn
      linarith
    have hclog : c * (Real.log ‖τ‖ + Real.pi) + K ≤ ρ / 2 := by
      rw [hρdef, hc1def, hc2def]
      nlinarith [hlogτ_nn, hcnn, hKnn]
    have hclose : dist (fatouCoordW f (1 - a) τ) τ ≤ (1 - (1 / 2 : ℝ)) * ρ := by
      rw [dist_eq_norm]
      have h : ‖fatouCoordW f (1 - a) τ - τ‖ ≤ ρ / 2 := le_trans hbound1 (le_trans hcK hclog)
      nlinarith
    -- every point of the ball has large real part
    have hre_ge : ∀ w : ℂ, dist w τ ≤ ρ → τ.re - ρ ≤ w.re := by
      intro w hw
      have h1 : |(τ - w).re| ≤ ‖τ - w‖ := Complex.abs_re_le_norm _
      have h2 : (τ - w).re = τ.re - w.re := by simp
      have h3 : ‖τ - w‖ = dist w τ := by rw [dist_eq_norm, norm_sub_rev]
      rw [h2] at h1
      have h4 : (τ.re - w.re) ≤ |τ.re - w.re| := le_abs_self _
      have h5 : ‖τ - w‖ ≤ ρ := by rw [h3]; exact hw
      linarith [h1, h4, h5]
    have hdiff_ball : ∀ w : ℂ, dist w τ ≤ ρ → DifferentiableAt ℂ (fatouCoordW f (1 - a)) w := by
      intro w hw
      have hwre : Nd < w.re := by
        have h1 := hre_ge w hw
        have h2 : Nd < τ.re - ρ := by linarith [hMlt, hNdN, le_max_left N R]
        linarith
      exact (hdiffd w hwre).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hwre)
    have hbound_ball : ∀ w : ℂ, dist w τ ≤ ρ → ‖deriv (fatouCoordW f (1 - a)) w - 1‖ ≤ 1 / 2 := by
      intro w hw
      have hwre : Nc < w.re := by
        have h1 := hre_ge w hw
        have h2 : Nc < τ.re - ρ := by linarith [hMlt, hNcN, le_max_left N R]
        linarith
      exact hderc w hwre
    obtain ⟨w, hwρ, hwψ⟩ := exists_eq_of_deriv_close (ψ := fatouCoordW f (1 - a)) (τ := τ) (ρ := ρ)
      (q := 1 / 2) hρpos (by norm_num) (by norm_num) hdiff_ball hbound_ball hclose
    refine ⟨w, ?_, hwψ⟩
    have h1 := hre_ge w hwρ
    have h2 : R < τ.re - ρ := by linarith [hMlt, le_max_right N R]
    linarith

end

end Work.FatouCoord.Exist
