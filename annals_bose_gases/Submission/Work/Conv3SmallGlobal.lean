import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Commons.Analysis.Convolution.abs_integral_mul_sub_le_integral_sq
import Submission.Work.Conv3SmallTaylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A5 — the global quadratic deviation of `conv3Small M` (dropping the `‖t‖ ≤ 1` restriction)

Completes the stage-A programme (`conv3Small_quadratic_dev`): the
convolution `conv3Small M = χ_M ⋆ χ_M` (with `∫χ_M² = 1`) satisfies

    |conv3Small M t − 1| ≤ C·‖t‖²      for ALL `t : ℝ³`   (3 ≤ M),

with `C := max C_local 2`, where `C_local` is the local constant of
`conv3Small_quadratic_dev_local` (module `Conv3SmallTaylor`).

The global ingredient is the sup bound `|conv3Small M x| ≤ 1` for all `x`
(any `1 ≤ M`): by Cauchy–Schwarz / `2|ab| ≤ a² + b²` applied to the integral
defining the convolution,

    |∫_y χ(y)χ(x−y)| ≤ ∫_y |χ(y)||χ(x−y)| ≤ ½∫χ² + ½∫χ(x−·)² = ½ + ½ = 1,

using `chiSmall_L2` (`∫χ_M² = 1`) and translation invariance of Lebesgue
measure (`integral_sub_right_eq_self` + evenness of `chiSmall`).  Hence
`|conv3Small x − 1| ≤ 2` everywhere, which is `≤ 2‖t‖²` once `‖t‖ ≥ 1`. -/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff
namespace Submission
set_option autoImplicit false
set_option linter.unusedVariables false
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `(χ_M)²` is integrable (`M ≥ 1`); continuity + compact support. -/
lemma chiSmall_sq_integrable {M : ℕ} (hM : 1 ≤ M) :
    Integrable (fun z : ℝ³ => (chiSmall M z) ^ 2) volume := by
  have hcont : Continuous (fun z : ℝ³ => (chiSmall M z) ^ 2) := (chiSmall_continuous hM).pow 2
  have hsupp : HasCompactSupport (fun z : ℝ³ => (chiSmall M z) ^ 2) :=
    (chiSmall_hasCompactSupport hM).mono (fun z hz => by
      rw [Function.mem_support] at hz ⊢
      intro h
      exact hz (by simp [h]))
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- The reflection about `x`, `y ↦ x − y`, preserves Lebesgue measure on `ℝ³`
(`y ↦ y − x` is a translation and `z ↦ −z` is a measure-preserving reflection). -/
lemma measurePreserving_sub_swap (x : ℝ³) :
    MeasurePreserving (fun y : ℝ³ => x - y) volume volume := by
  have h : (fun y : ℝ³ => x - y) = (fun y => -(y - x)) := by
    funext y
    abel
  rw [h]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ³)).comp
    (measurePreserving_sub_right x)

/-- **Sup bound for the cosine-`M` self-convolution**: `|(χ_M ⋆ χ_M)(x)| ≤ 1`
for every `x` and every `1 ≤ M`. -/
lemma conv3Small_abs_le_one {M : ℕ} (hM : 1 ≤ M) (x : ℝ³) : |conv3Small M x| ≤ 1 := by
  have hcont : Continuous (chiSmall M) := chiSmall_continuous hM
  -- integrability of the two squares
  have hint1 : Integrable (fun z : ℝ³ => (chiSmall M z) ^ 2) volume := chiSmall_sq_integrable hM
  have hg_aes : AEStronglyMeasurable (fun z : ℝ³ => (chiSmall M z) ^ 2) volume :=
    (hcont.pow 2).aestronglyMeasurable
  have hint2 : Integrable (fun y : ℝ³ => (chiSmall M (x - y)) ^ 2) volume :=
    ((measurePreserving_sub_swap x).integrable_comp (ν := volume)
      (f := fun y : ℝ³ => x - y) (g := fun z : ℝ³ => (chiSmall M z) ^ 2) hg_aes).mpr hint1
  -- pointwise `2|ab| ≤ a² + b²`
  have hpt : ∀ y : ℝ³, |chiSmall M y| * |chiSmall M (x - y)|
      ≤ (1 / 2 : ℝ) * (chiSmall M y) ^ 2 + (1 / 2 : ℝ) * (chiSmall M (x - y)) ^ 2 := by
    intro y
    have h2 : 2 * |chiSmall M y| * |chiSmall M (x - y)|
        ≤ (chiSmall M y) ^ 2 + (chiSmall M (x - y)) ^ 2 := by
      have h := sq_nonneg (|chiSmall M y| - |chiSmall M (x - y)|)
      rw [sub_sq, sq_abs, sq_abs] at h
      nlinarith
    linarith
  have hGint : Integrable (fun y : ℝ³ =>
      ((1 / 2 : ℝ) * (chiSmall M y) ^ 2 + (1 / 2 : ℝ) * (chiSmall M (x - y)) ^ 2)) volume :=
    (hint1.const_mul (1 / 2 : ℝ)).add (hint2.const_mul (1 / 2 : ℝ))
  have hFint : Integrable (fun y : ℝ³ => |chiSmall M y| * |chiSmall M (x - y)|) volume := by
    refine Integrable.mono' hGint ?_ ?_
    · have hcx : Continuous (fun y : ℝ³ => x - y) := continuous_const.sub continuous_id
      exact (hcont.abs.mul (hcont.abs.comp hcx)).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact hpt y
  -- the value of the bounding integral
  have h2val : ∫ y : ℝ³, (chiSmall M (x - y)) ^ 2 = 1 := by
    have hstep : ∫ y : ℝ³, (chiSmall M (x - y)) ^ 2
        = ∫ z : ℝ³, (chiSmall M (-z)) ^ 2 := by
      rw [← integral_sub_right_eq_self (μ := volume)
        (f := fun z : ℝ³ => (chiSmall M (-z)) ^ 2) x]
      apply integral_congr_ae
      filter_upwards with y
      have hy : x - y = -(y - x) := by abel
      rw [hy]
    have heven : ∫ z : ℝ³, (chiSmall M (-z)) ^ 2 = ∫ z : ℝ³, (chiSmall M z) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with z
      rw [chiSmall_even hM]
    rw [hstep, heven, chiSmall_L2 hM]
  have hGval : ∫ y : ℝ³,
      ((1 / 2 : ℝ) * (chiSmall M y) ^ 2 + (1 / 2 : ℝ) * (chiSmall M (x - y)) ^ 2) = 1 := by
    rw [integral_add (hint1.const_mul (1 / 2 : ℝ)) (hint2.const_mul (1 / 2 : ℝ)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, chiSmall_L2 hM, h2val]
    norm_num
  calc |conv3Small M x|
      = ‖∫ y : ℝ³, chiSmall M y * chiSmall M (x - y)‖ := by
          rw [Real.norm_eq_abs]
          rfl
    _ ≤ ∫ y : ℝ³, ‖chiSmall M y * chiSmall M (x - y)‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ y : ℝ³, |chiSmall M y| * |chiSmall M (x - y)| := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul]
    _ ≤ ∫ y : ℝ³,
          ((1 / 2 : ℝ) * (chiSmall M y) ^ 2 + (1 / 2 : ℝ) * (chiSmall M (x - y)) ^ 2) :=
          integral_mono_ae hFint hGint (Filter.Eventually.of_forall hpt)
    _ = 1 := hGval

/-- **Global quadratic deviation of `conv3Small M`** (`3 ≤ M`): there is
`C ≥ 0` with `‖conv3Small M t − 1‖ ≤ C·‖t‖²` for EVERY `t : ℝ³`.
`C := max C_local 2`: the local bound (`conv3Small_quadratic_dev_local`)
handles `‖t‖ ≤ 1`, while for `‖t‖ ≥ 1` the sup bound
`|conv3Small M t| ≤ 1` gives `|conv3Small M t − 1| ≤ 2 ≤ 2‖t‖²`. -/
theorem conv3Small_quadratic_dev {M : ℕ} (hM : 3 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ³, ‖conv3Small M t - 1‖ ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨C, hC0, hCloc⟩ := conv3Small_quadratic_dev_local hM
  refine ⟨max C 2, le_trans hC0 (le_max_left C 2), fun t => ?_⟩
  rw [Real.norm_eq_abs]
  by_cases ht : ‖t‖ ≤ 1
  · calc |conv3Small M t - 1| ≤ C * ‖t‖ ^ 2 := hCloc t ht
      _ ≤ max C 2 * ‖t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left C 2) (sq_nonneg _)
  · have ht1 : 1 ≤ ‖t‖ := le_of_not_ge ht
    have hsq : 1 ≤ ‖t‖ ^ 2 := by nlinarith [norm_nonneg t]
    have habs : |conv3Small M t| ≤ 1 := conv3Small_abs_le_one (by omega : 1 ≤ M) t
    have h2 : |conv3Small M t - 1| ≤ 2 := by
      have h := abs_sub_le (conv3Small M t) 0 1
      rw [sub_zero, zero_sub, abs_neg, abs_one] at h
      linarith
    calc |conv3Small M t - 1| ≤ 2 := h2
      _ = 2 * 1 := by ring
      _ ≤ max C 2 * ‖t‖ ^ 2 :=
            mul_le_mul (le_max_right C 2) hsq (by norm_num)
              (le_trans hC0 (le_max_left C 2))

/-- **A global quadratic-deviation constant for `conv3Small M`** (choice of
`conv3Small_quadratic_dev`): `0` in the degenerate case `M < 3`.  Giving the
constant a name lets downstream lemmas state their error bounds with an
explicit (problem-independent) constant. -/
noncomputable def convDevC (M : ℕ) : ℝ :=
  if h : 3 ≤ M then Classical.choose (conv3Small_quadratic_dev h) else 0

lemma convDevC_nonneg (M : ℕ) : 0 ≤ convDevC M := by
  rw [convDevC]
  by_cases h : 3 ≤ M
  · rw [dif_pos h]
    exact (Classical.choose_spec (conv3Small_quadratic_dev h)).1
  · rw [dif_neg h]

/-- The defining bound of `convDevC`: `‖conv3Small M t − 1‖ ≤ convDevC M·‖t‖²`
for every `t`, when `3 ≤ M`. -/
lemma convDevC_bound {M : ℕ} (hM : 3 ≤ M) (t : ℝ³) :
    ‖conv3Small M t - 1‖ ≤ convDevC M * ‖t‖ ^ 2 := by
  rw [convDevC, dif_pos hM]
  exact (Classical.choose_spec (conv3Small_quadratic_dev hM)).2 t


/-- **Independent re-derivation of `conv3Small_abs_le_one`** from the general
commons `L²` self-convolution bound
`Commons.Analysis.Convolution.abs_integral_mul_sub_le_integral_sq`
(`|∫ y, f y · f (x − y)| ≤ ∫ f²` for `f ∈ L²` of a translation- and
negation-invariant measure) — a cross-check of the hand-rolled
Cauchy–Schwarz proof above, with `∫χ_M² = 1` (`chiSmall_L2`). -/
lemma conv3Small_abs_le_one' {M : ℕ} (hM : 1 ≤ M) (x : ℝ³) : |conv3Small M x| ≤ 1 := by
  have hmem : MemLp (chiSmall M) 2 volume :=
    (chiSmall_continuous hM).memLp_of_hasCompactSupport (chiSmall_hasCompactSupport hM)
  have h := Commons.Analysis.Convolution.abs_integral_mul_sub_le_integral_sq
    (μ := (volume : Measure ℝ³)) hmem x
  rw [chiSmall_L2 hM] at h
  simpa [conv3Small] using h


end BoseGases
end Submission
