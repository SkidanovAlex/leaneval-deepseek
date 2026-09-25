import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec

/-!
# A parametric smooth cutoff on `ℂ`

For `0 < a < b` the function `sharpCut a b : ℂ → ℂ` is smooth, equals `1` on `‖ζ‖ ≤ a`,
vanishes for `b ≤ ‖ζ‖` and takes values in the closed unit disc.  It is the tool used to
localise the one-variable Cauchy-type transforms `dbarTransform` to data supported in a
disc of *prescribed* radius, with the ratio of the two radii as close to `1` as needed
(which the fixed cutoffs of `Work.CR.Flat.Cauchy` do not allow).
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

/-- The radial profile: `sharpCut a b ζ = σ((b² - ‖ζ‖²)/(b² - a²))` with `σ = Real.smoothTransition`. -/
noncomputable def sharpCutReal (a b s : ℝ) : ℝ :=
  Real.smoothTransition ((b ^ 2 - s) / (b ^ 2 - a ^ 2))

/-- A smooth cutoff on `ℂ`, equal to `1` for `‖ζ‖ ≤ a` and to `0` for `b ≤ ‖ζ‖`. -/
noncomputable def sharpCut (a b : ℝ) (ζ : ℂ) : ℂ :=
  (sharpCutReal a b (Complex.normSq ζ) : ℂ)

lemma sharpCut_eq_profile (a b : ℝ) (ζ : ℂ) :
    sharpCut a b ζ = (sharpCutReal a b (Complex.normSq ζ) : ℂ) := rfl

lemma sharpCutReal_nonneg (a b s : ℝ) : 0 ≤ sharpCutReal a b s :=
  Real.smoothTransition.nonneg _

lemma sharpCutReal_le_one (a b s : ℝ) : sharpCutReal a b s ≤ 1 :=
  Real.smoothTransition.le_one _

lemma sharpCut_sq_sub_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : 0 < b ^ 2 - a ^ 2 := by
  nlinarith [sq_nonneg (b - a), sq_nonneg (b + a)]

lemma sharpCutReal_eq_one {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : s ≤ a ^ 2) :
    sharpCutReal a b s = 1 := by
  rw [sharpCutReal, Real.smoothTransition.one_of_one_le]
  rw [le_div_iff₀ (sharpCut_sq_sub_pos ha hab)]
  linarith

lemma sharpCutReal_eq_zero {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : b ^ 2 ≤ s) :
    sharpCutReal a b s = 0 := by
  rw [sharpCutReal, Real.smoothTransition.zero_of_nonpos]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (sharpCut_sq_sub_pos ha hab).le
  linarith

lemma contDiff_sharpCutReal {a b : ℝ} : ContDiff ℝ ∞ (sharpCutReal a b) := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => (b ^ 2 - s) / (b ^ 2 - a ^ 2)) := by
    have h' : (fun s : ℝ => (b ^ 2 - s) / (b ^ 2 - a ^ 2))
        = fun s : ℝ => (b ^ 2 - s) * (b ^ 2 - a ^ 2)⁻¹ := by
      funext s; rw [div_eq_mul_inv]
    rw [h']; fun_prop
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h

lemma contDiff_normSq' : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
  have h : (fun ζ : ℂ => Complex.normSq ζ)
      = fun ζ : ℂ => Complex.reCLM ζ * Complex.reCLM ζ + Complex.imCLM ζ * Complex.imCLM ζ := by
    funext ζ; rw [Complex.normSq_apply]; rfl
  rw [h]; fun_prop

lemma contDiff_sharpCut {a b : ℝ} : ContDiff ℝ ∞ (sharpCut a b) := by
  rw [show sharpCut a b = fun ζ : ℂ => (sharpCutReal a b (Complex.normSq ζ) : ℂ) from rfl]
  exact (Complex.ofRealCLM.contDiff).comp
    ((contDiff_sharpCutReal).comp contDiff_normSq')

lemma sharpCut_eq_one {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {ζ : ℂ} (h : ‖ζ‖ ≤ a) :
    sharpCut a b ζ = 1 := by
  have hs : Complex.normSq ζ ≤ a ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg ζ) h 2
  rw [sharpCut, sharpCutReal_eq_one ha hab hs, Complex.ofReal_one]

lemma sharpCut_eq_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {ζ : ℂ} (h : b ≤ ‖ζ‖) :
    sharpCut a b ζ = 0 := by
  have hb : 0 ≤ b := le_trans ha hab.le
  have hs : b ^ 2 ≤ Complex.normSq ζ := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ hb h 2
  rw [sharpCut, sharpCutReal_eq_zero ha hab hs, Complex.ofReal_zero]

lemma norm_sharpCut_le_one (a b : ℝ) (ζ : ℂ) : ‖sharpCut a b ζ‖ ≤ 1 := by
  rw [sharpCut, Complex.norm_real, Real.norm_of_nonneg (sharpCutReal_nonneg a b _)]
  exact sharpCutReal_le_one a b _

lemma hasCompactSupport_sharpCut {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    HasCompactSupport (sharpCut a b) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : ℂ) b)
    (isCompact_closedBall (0 : ℂ) b) ?_
  intro ζ hζ
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hζ (sharpCut_eq_zero ha hab (le_of_lt (not_le.mp h)))

end Work.NN.Core
