import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_decay_gen
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `p ↦ ‖p‖ ‖kinFT g p‖²` for smooth compactly supported `g`

`Submission.BoseGases.kinFT g` is the `p`-convention Fourier transform of `g`; for `g` smooth
with compact support it is (as a function of `p`) a Schwartz function, so in dimension three the
weighted square `‖p‖ ‖kinFT g p‖²` decays like `‖p‖^{-5}` at infinity and is bounded near the
origin.  Both halves are already in the corpus:

* `Work.BoseBoxFock.SqrtKin.kinFT_decay_gen` (polynomial decay `‖kinFT g p‖ ≤ K (1+‖p‖)^{-3}`),
* `Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable` (continuity, hence measurability).

The domination is then by the radial profile `K² (1 + ‖p‖)^{-5}`, which is integrable in
dimension three by Mathlib's `integrable_one_add_norm`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.SqrtKin

/-- Pointwise domination of the weighted square by the radial profile `(1 + ‖p‖)^{-5}`,
using only the cubic decay `‖kinFT g p‖ ≤ K (1 + ‖p‖)^{-3}`. -/
private lemma weight_le_decay {g : EuclideanSpace ℝ (Fin 3) → ℂ} {K : ℝ}
    (hdec : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT g p‖ ≤ K / (1 + ‖p‖) ^ 3)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤ K ^ 2 * (1 + ‖p‖) ^ (-5 : ℝ) := by
  have hu_pos : (0 : ℝ) < 1 + ‖p‖ := by positivity
  -- the squared decay `‖kinFT g p‖² ≤ K²/(1+‖p‖)⁶`
  have hA : ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤ K ^ 2 / (1 + ‖p‖) ^ 6 := by
    have h1 := hdec p
    have h2 : ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤ (K / (1 + ‖p‖) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : ((1 + ‖p‖) ^ 3) ^ 2 = (1 + ‖p‖) ^ 6 := by ring
    rwa [div_pow, h3] at h2
  have hle : ‖p‖ ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
  have hrpow : (1 + ‖p‖) ^ (-5 : ℝ) = ((1 + ‖p‖) ^ 5)⁻¹ := by
    rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu_pos.le, Real.rpow_natCast]
  calc ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      ≤ ‖p‖ * (K ^ 2 / (1 + ‖p‖) ^ 6) := mul_le_mul_of_nonneg_left hA (norm_nonneg p)
    _ ≤ (1 + ‖p‖) * (K ^ 2 / (1 + ‖p‖) ^ 6) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = K ^ 2 / (1 + ‖p‖) ^ 5 := by field_simp
    _ = K ^ 2 * (1 + ‖p‖) ^ (-5 : ℝ) := by rw [hrpow, div_eq_mul_inv]

theorem kinFT_weight_integrable {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  -- `g` is integrable, hence `kinFT g` is continuous
  have hgint : Integrable g volume :=
    hg.continuous.integrable_of_hasCompactSupport (μ := volume) hgc
  have hcont : Continuous (Submission.BoseGases.kinFT g) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hgint
  -- cubic decay of `kinFT g`
  obtain ⟨K, _hK, hdec⟩ := kinFT_decay_gen hg hgc 3
  -- the dominating radial profile is integrable in dimension three
  have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) < 5 := by
    rw [finrank_euclideanSpace]; norm_num
  have hdom : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => K ^ 2 * (1 + ‖p‖) ^ (-5 : ℝ)) volume :=
    (integrable_one_add_norm (μ := volume) (E := EuclideanSpace ℝ (Fin 3)) hfin).const_mul (K ^ 2)
  refine hdom.mono' ?_ ?_
  · exact (continuous_norm.mul (hcont.norm.pow 2)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (by positivity)]
    exact weight_le_decay hdec p

end Work.BoseBoxFock.SqrtKin
