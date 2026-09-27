import Mathlib
import Submission.Work.EKLRelCross.PeriodFunsDefs
import Submission.Work.EKLRelCross.tent_iSup_ofReal_formula
import Submission.Work.EKLRelCross.integrable_tent_formula

/-!
# The mass of an interval as the supremum of the integrals of the tent functions

For `a < b` the tent functions `tentFun a b n` (see `Submission/Work/EKLRelCross/PeriodFunsDefs.lean`)

`tentFun a b n t = max 0 (min 1 (min (n (t - a)) (n (b - t))))`

increase pointwise with `n` to the indicator of the open interval `(a, b)`.  Consequently,
for every measure on `ℝ` which is finite on compact sets,

`μ (Ioo a b) = ⨆ n, ENNReal.ofReal (∫ t, tentFun a b n t ∂μ)`.

The proof is monotone convergence in its `ℝ≥0∞` form: the `lintegral`s of the (nonnegative)
tents converge to the `lintegral` of their pointwise supremum, which is the indicator of
`(a, b)`; the Bochner integrals agree with the `lintegral`s because the tents are integrable
(they are continuous, bounded by `1` and supported in the compact set `[a, b]`, which has
finite measure).
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

/-! ## Elementary pointwise properties of the tent functions -/

theorem tentFun_measurable (a b : ℝ) (n : ℕ) :
    Measurable fun t : ℝ => ENNReal.ofReal (tentFun a b n t) :=
  ENNReal.continuous_ofReal.measurable.comp (continuous_tentFun a b n).measurable

theorem tentFun_eq_zero_of_le (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t ≤ a) : tentFun a b n t = 0 := by
  have h1 : (n : ℝ) * (t - a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
  have h2 : min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)) ≤ 0 := le_trans (min_le_left _ _) h1
  have h3 : min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))) ≤ 0 :=
    le_trans (min_le_right _ _) h2
  simp only [tentFun_apply]
  rw [max_eq_left h3]

theorem tentFun_eq_zero_of_ge (a b : ℝ) (n : ℕ) {t : ℝ} (ht : b ≤ t) : tentFun a b n t = 0 := by
  have h1 : (n : ℝ) * (b - t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
  have h2 : min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)) ≤ 0 := le_trans (min_le_right _ _) h1
  have h3 : min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))) ≤ 0 :=
    le_trans (min_le_right _ _) h2
  simp only [tentFun_apply]
  rw [max_eq_left h3]

theorem tentFun_eq_zero_of_outside (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t ≤ a ∨ b ≤ t) :
    tentFun a b n t = 0 := by
  rcases ht with h | h
  · exact tentFun_eq_zero_of_le a b n h
  · exact tentFun_eq_zero_of_ge a b n h

/-- The tent functions of slope `n` are pointwise nondecreasing in `n`. -/
theorem tentFun_mono_n (a b : ℝ) (t : ℝ) : Monotone fun n : ℕ => tentFun a b n t := by
  intro n m hnm
  change tentFun a b n t ≤ tentFun a b m t
  rcases lt_or_ge t a with hta | hta
  · rw [tentFun_eq_zero_of_le a b n (le_of_lt hta), tentFun_eq_zero_of_le a b m (le_of_lt hta)]
  · rcases lt_or_ge b t with hbt | hbt
    · rw [tentFun_eq_zero_of_ge a b n (le_of_lt hbt), tentFun_eq_zero_of_ge a b m (le_of_lt hbt)]
    · simp only [tentFun_apply]
      have hn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have h1 : (n : ℝ) * (t - a) ≤ (m : ℝ) * (t - a) :=
        mul_le_mul_of_nonneg_right hn (by linarith)
      have h2 : (n : ℝ) * (b - t) ≤ (m : ℝ) * (b - t) :=
        mul_le_mul_of_nonneg_right hn (by linarith)
      exact max_le_max le_rfl (min_le_min le_rfl (min_le_min h1 h2))

/-- The pointwise supremum over `n` of the tents `tentFun a b n` is the indicator of `(a,b)`. -/
theorem tentFun_iSup_ofReal_eq (a b : ℝ) (hab : a < b) (t : ℝ) :
    (⨆ n : ℕ, ENNReal.ofReal (tentFun a b n t))
      = (Set.Ioo a b).indicator (fun _ => (1 : ENNReal)) t := by
  simpa only [tentFun_apply] using tent_iSup_ofReal_formula hab t

/-- The tents are integrable for a measure which is finite on compact sets: they are
continuous, bounded by `1` and supported in the compact set `[a, b]`.  (This is the lemma
`Work.EKLRelCross.integrable_tent_formula`, transported to `tentFun`.) -/
theorem integrable_tentFun (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] (a b : ℝ) (n : ℕ) :
    Integrable (tentFun a b n) μ := by
  show Integrable (fun t : ℝ => tentFun a b n t) μ
  simpa only [tentFun_apply] using integrable_tent_formula μ a b n

/-! ## The main identity -/

theorem tent_interval_measure {a b : ℝ} (hab : a < b) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] :
    μ (Set.Ioo a b) =
      ⨆ n : ℕ, ENNReal.ofReal (∫ t, Work.EKLRelCross.tentFun a b n t ∂μ) := by
  -- each of the functions `t ↦ ofReal (tentFun a b n t)` is measurable
  have hmeas : ∀ n : ℕ, Measurable fun t : ℝ => ENNReal.ofReal (tentFun a b n t) :=
    fun n => tentFun_measurable a b n
  -- and they are pointwise nondecreasing in `n`
  have hmono : Monotone fun n : ℕ => fun t : ℝ => ENNReal.ofReal (tentFun a b n t) :=
    fun n m hnm t => ENNReal.ofReal_le_ofReal (tentFun_mono_n a b t hnm)
  -- monotone convergence, in its `ℝ≥0∞` form
  have hMCT : ∫⁻ t, (⨆ n : ℕ, ENNReal.ofReal (tentFun a b n t)) ∂μ
      = ⨆ n : ℕ, ∫⁻ t, ENNReal.ofReal (tentFun a b n t) ∂μ := lintegral_iSup hmeas hmono
  -- the pointwise supremum of the tents is the indicator of `(a, b)`
  have hpoint : ∀ t : ℝ, (⨆ n : ℕ, ENNReal.ofReal (tentFun a b n t))
      = (Set.Ioo a b).indicator (fun _ => (1 : ENNReal)) t :=
    fun t => tentFun_iSup_ofReal_eq a b hab t
  calc μ (Set.Ioo a b)
      = ∫⁻ t, (Set.Ioo a b).indicator (fun _ => (1 : ENNReal)) t ∂μ :=
        (lintegral_indicator_one measurableSet_Ioo).symm
    _ = ∫⁻ t, (⨆ n : ℕ, ENNReal.ofReal (tentFun a b n t)) ∂μ :=
        (lintegral_congr hpoint).symm
    _ = ⨆ n : ℕ, ∫⁻ t, ENNReal.ofReal (tentFun a b n t) ∂μ := hMCT
    _ = ⨆ n : ℕ, ENNReal.ofReal (∫ t, tentFun a b n t ∂μ) :=
        iSup_congr fun n => (ofReal_integral_eq_lintegral_ofReal
          (integrable_tentFun μ a b n) (Eventually.of_forall (tentFun_nonneg a b n))).symm

end

end Work.EKLRelCross
