/-
# The `vol` API: Lebesgue measure of subsets of `ℝ` as a real number

`vol s = (volume s).toReal`.  All the density bookkeeping of the low-entropy method
(Steps 7, 8, 9 of `ROUTE_LEAD.md` §5, i.e. EKL Lemma 4.5 and its uses) is phrased with
`vol`, so that `T - (measure of a subset)` is ordinary real subtraction.

Because `ENNReal.toReal` is not monotone at `⊤`, the lemmas that need monotonicity carry
an explicit finiteness hypothesis `volume t ≠ ⊤`; in every application the set is bounded,
and `volume_ne_top_of_subset_Icc` discharges that hypothesis.
-/
import Submission.Work.EKLC8Core.Basic

noncomputable section

namespace Work.EKLC8Core

open MeasureTheory
open scoped ENNReal

theorem vol_def (s : Set ℝ) : vol s = (volume s).toReal := rfl

theorem vol_empty : vol (∅ : Set ℝ) = 0 := by simp [vol]

/-- `vol` of an interval. -/
theorem vol_Icc {a b : ℝ} (h : a ≤ b) : vol (Set.Icc a b) = b - a := by
  rw [vol, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr h)]

/-- `vol` of an interval, unconditionally. -/
theorem vol_Icc_eq_max {a b : ℝ} : vol (Set.Icc a b) = max (b - a) 0 := by
  by_cases h : a ≤ b
  · rw [vol_Icc h, max_eq_left (sub_nonneg.mpr h)]
  · rw [Set.Icc_eq_empty h, vol_empty, max_eq_right (by push_neg at h; linarith)]

/-- `vol` is monotone on sets of finite measure. -/
theorem vol_mono {s t : Set ℝ} (h : s ⊆ t) (ht : volume t ≠ ⊤) : vol s ≤ vol t :=
  ENNReal.toReal_mono ht (measure_mono h)

theorem vol_nonneg (s : Set ℝ) : 0 ≤ vol s := ENNReal.toReal_nonneg


/-- Measure of a difference, for `s ⊆ t` with `t` of finite measure. -/
theorem vol_sdiff {s t : Set ℝ} (h : s ⊆ t) (hs : MeasurableSet s) (ht : volume t ≠ ⊤) :
    vol (t \ s) = vol t - vol s :=
  (MeasureTheory.measureReal_sdiff (μ := (volume : Measure ℝ)) h hs ht).trans (by
    simp only [MeasureTheory.measureReal_def, vol])

/-- Additivity for a disjoint union of a finite-measure measurable set and any set. -/
theorem vol_union {s t : Set ℝ} (h : Disjoint s t) (ht : MeasurableSet t) (hs : volume s ≠ ⊤)
    (ht' : volume t ≠ ⊤) : vol (s ∪ t) = vol s + vol t := by
  rw [vol, vol, vol, measure_union h ht, ENNReal.toReal_add hs ht']

/-- A set contained in an interval has finite measure. -/
theorem volume_ne_top_of_subset_Icc {s : Set ℝ} {a b : ℝ} (h : s ⊆ Set.Icc a b) :
    volume s ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono h)

theorem vol_le_of_subset_Icc {s : Set ℝ} {a b : ℝ} (h : s ⊆ Set.Icc a b) (hab : a ≤ b) :
    vol s ≤ b - a := by
  rw [← vol_Icc hab]
  exact vol_mono h (volume_ne_top_of_subset_Icc (subset_rfl : Set.Icc a b ⊆ Set.Icc a b))

/-- Scaling: `vol (a ⁻¹' s) = |a|⁻¹ * vol s` for the map `x ↦ a * x`, `a ≠ 0`. -/
theorem vol_preimage_mul_left {a : ℝ} (ha : a ≠ 0) (s : Set ℝ) :
    vol ((a * ·) ⁻¹' s) = |a|⁻¹ * vol s := by
  have h := Real.volume_preimage_mul_left (a := a) ha s
  simp only [vol, h, ENNReal.toReal_mul]
  simp

/-- Translation invariance of `vol`. -/
theorem vol_preimage_add_right (b : ℝ) (s : Set ℝ) : vol ((· + b) ⁻¹' s) = vol s := by
  rw [vol, vol, measure_preimage_add_right (volume : Measure ℝ) b s]

/-- Affine change of variables: for `a ≠ 0`, `vol {x : a * x + b ∈ s} = |a|⁻¹ * vol s`. -/
theorem vol_preimage_affine {a b : ℝ} (ha : a ≠ 0) (s : Set ℝ) :
    vol ((fun x : ℝ => a * x + b) ⁻¹' s) = |a|⁻¹ * vol s := by
  have h1 : (fun x : ℝ => a * x + b) ⁻¹' s
      = (fun x : ℝ => a * x) ⁻¹' ((fun y : ℝ => y + b) ⁻¹' s) := rfl
  rw [h1, vol_preimage_mul_left ha, vol_preimage_add_right]

end Work.EKLC8Core
