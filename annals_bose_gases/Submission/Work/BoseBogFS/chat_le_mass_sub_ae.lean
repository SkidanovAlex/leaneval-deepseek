import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBogFS.ChatChiFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# `chat_le_mass_sub_ae` — the support-localised quadratic bound on `Ŵ`

For a nonnegative, integrable `W` supported (a.e.) in the closed ball of radius `R`
around the origin,

`Ŵ(k) = ∫ W(y) cos⟪k,y⟫ dy ≥ (∫ W)(1 − R²‖k‖²/2)`

(the "trivial" side of the quadratic Fourier estimate, with the mass `∫ W` on the
*support-localised* factor `1 − R²‖k‖²/2` rather than on the second moment
`∫ ‖y‖²W`).  The pointwise input is `cos t ≥ 1 − t²/2`
(`Real.one_sub_sq_div_two_le_cos`) together with `⟪k,y⟫² ≤ ‖k‖²‖y‖² ≤ ‖k‖²R²`
(Cauchy–Schwarz plus the support condition): on the a.e. set where `W ≥ 0` and
`R < ‖y‖ → W y = 0`, every `y` with `W y > 0` satisfies `‖y‖ ≤ R`, whence

`1 − R²‖k‖²/2 ≤ 1 − ⟪k,y⟫²/2 ≤ cos⟪k,y⟫`.

Multiplying by `W y ≥ 0` and integrating (with `chat = ∫ W cos`, the cosine form of
`Work.BoseFixR.chat`, `Work.BoseB7AK.W1low.chat_eq_integral_cos`) gives the claim.
No second-moment integrability and no evenness of `W` are needed.
-/

noncomputable section

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.BoseBogFS

theorem chat_le_mass_sub_ae {Wt : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hWint : MeasureTheory.Integrable Wt) (hR : 0 ≤ R)
    (hWnn : ∀ᵐ x, 0 ≤ Wt x) (hWsupp : ∀ᵐ x, R < ‖x‖ → Wt x = 0)
    (k : EuclideanSpace ℝ (Fin 3)) :
    (∫ x, Wt x) * (1 - R ^ 2 * ‖k‖ ^ 2 / 2) ≤ Work.BoseFixR.chat Wt k := by
  -- `chat` is the cosine transform
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hWint k]
  -- integrability of the cosine transform
  have hcosInt : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => Wt y * Real.cos (inner ℝ k y)) := by
    refine hWint.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  -- the pointwise bound, a.e.
  have hpt : ∀ᵐ y : EuclideanSpace ℝ (Fin 3),
      Wt y * (1 - R ^ 2 * ‖k‖ ^ 2 / 2) ≤ Wt y * Real.cos (inner ℝ k y) := by
    filter_upwards [hWnn, hWsupp] with y hnn hsupp
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · simp [← h0]
    · -- `W y > 0` forces `‖y‖ ≤ R` by the support condition
      have hle : ‖y‖ ≤ R :=
        le_of_not_gt (fun hlt => absurd (hsupp hlt) (ne_of_gt hpos))
      have htsq : (inner ℝ k y) ^ 2 ≤ ‖k‖ ^ 2 * ‖y‖ ^ 2 := by
        have h : |inner ℝ k y| ≤ ‖k‖ * ‖y‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) k y
        calc (inner ℝ k y) ^ 2 ≤ (‖k‖ * ‖y‖) ^ 2 := by
              rw [sq_le_sq]; simpa using h
          _ = ‖k‖ ^ 2 * ‖y‖ ^ 2 := by ring
      have hysq : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hle 2
      have hkey : 1 - R ^ 2 * ‖k‖ ^ 2 / 2 ≤ Real.cos (inner ℝ k y) := by
        have hc := Real.one_sub_sq_div_two_le_cos (x := inner ℝ k y)
        have h3 : ‖k‖ ^ 2 * ‖y‖ ^ 2 ≤ ‖k‖ ^ 2 * R ^ 2 :=
          mul_le_mul_of_nonneg_left hysq (sq_nonneg ‖k‖)
        have h2 : (inner ℝ k y) ^ 2 ≤ R ^ 2 * ‖k‖ ^ 2 := by nlinarith [htsq, h3]
        linarith
      exact mul_le_mul_of_nonneg_left hkey (le_of_lt hpos)
  -- integrate the pointwise bound
  have h := MeasureTheory.integral_mono_ae
    (hWint.mul_const (1 - R ^ 2 * ‖k‖ ^ 2 / 2)) hcosInt hpt
  rwa [MeasureTheory.integral_mul_const] at h

end Work.BoseBogFS
