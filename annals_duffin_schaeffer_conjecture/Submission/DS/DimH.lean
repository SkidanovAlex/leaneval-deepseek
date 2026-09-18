import Mathlib.Topology.MetricSpace.HausdorffDimension

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open MeasureTheory.Measure

/-!
# Hausdorff dimension of sets of positive Lebesgue measure

Bridge results between Lebesgue measure and Hausdorff dimension in `ℝ`, needed in the
`corollary_3` assembly.  Once the Duffin–Schaeffer theorem supplies
`volume (𝒜 ψ) = 1`, the full-measure set `𝒜 ψ ⊆ [0,1]` automatically has Hausdorff
dimension `1`, so `dimH (𝒜 ψ) = min (s_inf ψ) 1` whenever `1 ≤ s_inf ψ`.

Key ingredients (all from Mathlib):
* `hausdorffMeasure_real : (μH[1] : Measure ℝ) = volume` (the 1-dimensional Hausdorff
  measure on `ℝ` is the Lebesgue measure);
* the classical dichotomy `hausdorffMeasure_zero_or_top` (for `d < 1`, either
  `μH[1] s = 0` or `μH[d] s = ∞`).

All statements are machine-checked and use only the permitted axioms.
-/

namespace Submission.DS

/-- A set of positive Lebesgue measure in `ℝ` has Hausdorff dimension `1`.

(No measurability hypothesis is needed: `volume` and the Hausdorff measures act on
arbitrary sets.) -/
lemma dimH_eq_one_of_volume_pos (A : Set ℝ) (hvol : (0 : ℝ≥0∞) < volume A) : dimH A = 1 := by
  classical
  apply le_antisymm
  · calc
      dimH A ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ A)
      _ = 1 := Real.dimH_univ
  · by_contra h
    have hlt : dimH A < (1 : ℝ≥0∞) := lt_of_not_ge h
    have hne : dimH A ≠ (⊤ : ℝ≥0∞) := ne_of_lt (lt_trans hlt ENNReal.coe_lt_top)
    let x : NNReal := (dimH A).toNNReal
    have hx : (x : ℝ≥0∞) = dimH A := ENNReal.coe_toNNReal hne
    have hx1 : x < 1 := by
      rw [← hx] at hlt
      exact ENNReal.coe_lt_coe.mp hlt
    rcases exists_between hx1 with ⟨d, hxd, hd1⟩
    have hμ1 : μH[1] A ≠ 0 := by
      rw [hausdorffMeasure_real]
      exact ne_of_gt hvol
    have hdich := hausdorffMeasure_zero_or_top (d₁ := (d : ℝ)) (d₂ := (1 : ℝ))
      (by exact_mod_cast hd1) A
    rcases hdich with hz | htop'
    · exact False.elim (hμ1 hz)
    · have hge : (d : ℝ≥0∞) ≤ dimH A := le_dimH_of_hausdorffMeasure_eq_top htop'
      have hxd : dimH A < (d : ℝ≥0∞) := by
        rw [← hx]
        exact ENNReal.coe_lt_coe.mpr hxd
      exact (not_lt_of_ge hge) hxd

/-- A subset of `[0,1]` of full Lebesgue measure has Hausdorff dimension `1`. -/
lemma dimH_eq_one_of_subset_Icc_volume_eq_one {A : Set ℝ}
    (_hA : A ⊆ Set.Icc (0 : ℝ) 1) (hvol : volume A = 1) : dimH A = 1 :=
  dimH_eq_one_of_volume_pos A (by rw [hvol]; norm_num)

/-- A subset of `[0,1]` has Hausdorff dimension at most `1`. -/
lemma dimH_le_one_of_subset_Icc {A : Set ℝ} (hA : A ⊆ Set.Icc (0 : ℝ) 1) : dimH A ≤ 1 := by
  calc
    dimH A ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ A)
    _ = 1 := Real.dimH_univ

/-- For `d < 1`, the `d`-dimensional Hausdorff measure of a non-degenerate interval is
infinite (the interval already carries positive `1`-dimensional measure). -/
lemma hausdorffMeasure_Icc_eq_top_of_lt_one {x y : ℝ} (hxy : x < y) {d : ℝ} (hd : d < 1) :
    μH[d] (Set.Icc x y) = ∞ := by
  have hμ1 : μH[1] (Set.Icc x y) ≠ 0 := by
    rw [hausdorffMeasure_real, Real.volume_Icc]
    have hpos : 0 < y - x := by linarith
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  rcases hausdorffMeasure_zero_or_top (d₁ := d) (d₂ := (1 : ℝ)) hd (Set.Icc x y) with hz | ht
  · exact False.elim (hμ1 hz)
  · exact ht

/-- Dimension from below: if every exponent `d < m` (with `m : ℝ≥0`) already makes the
`d`-dimensional Hausdorff measure infinite, then `dimH s ≥ m`. -/
lemma le_dimH_of_forall_lt_hausdorffMeasure_eq_top {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} {m : ℝ≥0}
    (h : ∀ d : ℝ≥0, d < m → μH[↑d] s = ∞) : (m : ℝ≥0∞) ≤ dimH s := by
  classical
  by_contra hc
  have hlt : dimH s < (m : ℝ≥0∞) := lt_of_not_ge hc
  have hne : dimH s ≠ (⊤ : ℝ≥0∞) := by
    exact ne_of_lt (lt_trans hlt (ENNReal.coe_lt_top : (m : ℝ≥0∞) < ⊤))
  let x : NNReal := (dimH s).toNNReal
  have hx : (x : ℝ≥0∞) = dimH s := ENNReal.coe_toNNReal hne
  have hxm : x < m := by
    rw [← hx] at hlt
    exact ENNReal.coe_lt_coe.mp hlt
  rcases exists_between hxm with ⟨d, hxd, hdm⟩
  have htop : μH[↑d] s = ∞ := h d hdm
  have hge : (d : ℝ≥0∞) ≤ dimH s := le_dimH_of_hausdorffMeasure_eq_top htop
  have hxd' : dimH s < (d : ℝ≥0∞) := by
    rw [← hx]
    exact ENNReal.coe_lt_coe.mpr hxd
  exact (not_lt_of_ge hge) hxd'

/-- Dimension from below at the value `1`: if every `d < 1` has infinite `d`-dimensional
Hausdorff measure, then `dimH s ≥ 1`. -/
lemma one_le_dimH_of_forall_lt_hausdorffMeasure_eq_top {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X}
    (h : ∀ d : ℝ≥0, d < 1 → μH[↑d] s = ∞) : (1 : ℝ≥0∞) ≤ dimH s := by
  simpa using le_dimH_of_forall_lt_hausdorffMeasure_eq_top (m := 1) h

end Submission.DS
