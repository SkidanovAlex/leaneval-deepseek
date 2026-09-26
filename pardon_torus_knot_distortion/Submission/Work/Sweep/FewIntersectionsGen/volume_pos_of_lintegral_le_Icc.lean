import Mathlib
import Submission.Work.Sweep.FewIntersections.volume_pos_of_lintegral_le

namespace Work.Sweep.FewIntersectionsGen

open MeasureTheory Set
open scoped ENNReal

/-- Arithmetic core of the Markov-type bound, general interval form.

For `a < b` and `c = C/(b-a)`, the first natural number `⌊c⌋₊ + 1` strictly above `c`,
multiplied by the length `b - a`, exceeds `C`:
`(⌊C/(b-a)⌋₊ + 1) · (b-a) > C`.  Written in `ℝ≥0∞`, this says
`ofReal C < (⌊C/(b-a)⌋₊ + 1) * ofReal (b-a)`. -/
lemma ofReal_lt_natCast_floor_add_one_mul {C a b : ℝ} (hab : a < b) :
    ENNReal.ofReal C <
      ((⌊C / (b - a)⌋₊ + 1 : ℕ) : ENNReal) * ENNReal.ofReal (b - a) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hne : b - a ≠ 0 := ne_of_gt hba
  have hfl : C / (b - a) < ((⌊C / (b - a)⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hC : C < ((⌊C / (b - a)⌋₊ + 1 : ℕ) : ℝ) * (b - a) := by
    have h := mul_lt_mul_of_pos_right hfl hba
    rwa [div_mul_cancel₀ _ hne] at h
  have hpos : (0 : ℝ) < ((⌊C / (b - a)⌋₊ + 1 : ℕ) : ℝ) * (b - a) :=
    mul_pos (by positivity) hba
  calc ENNReal.ofReal C
      < ENNReal.ofReal (((⌊C / (b - a)⌋₊ + 1 : ℕ) : ℝ) * (b - a)) :=
        (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hC
    _ = ENNReal.ofReal ((⌊C / (b - a)⌋₊ + 1 : ℕ) : ℝ) * ENNReal.ofReal (b - a) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ((⌊C / (b - a)⌋₊ + 1 : ℕ) : ENNReal) * ENNReal.ofReal (b - a) := by
        rw [ENNReal.ofReal_natCast]

/-- **Markov-type positivity for `ℕ∞`-valued functions, general interval form.**

Let `g : ℝ → ℕ∞` and `a < b`.  If the upper integral of `(g r : ℝ≥0∞)` over `Icc a b`
is at most `ofReal C`, then the set of `r ∈ Icc a b` with
`(g r : ℝ≥0∞) ≤ ofReal (C/(b-a))` has positive Lebesgue measure.

The threshold `C/(b-a)` is exactly the average of `g` over the interval, so the
statement says that an `ℕ∞`-valued function cannot be strictly above its average on
almost all of the interval (here "above" is upgraded from `> average` to
`≥ ⌊average⌋₊+1` by integrality).  No measurability of `g` is assumed: the proof
upgrades a possibly non-measurable null set to a measurable null superset and works
throughout with the measurable superset. -/
theorem volume_pos_of_lintegral_le_Icc {g : ℝ → ℕ∞} {a b C : ℝ} (hab : a < b)
    (hint : ∫⁻ r in Set.Icc a b, (g r : ENNReal) ≤ ENNReal.ofReal C) :
    0 < MeasureTheory.volume {r ∈ Set.Icc a b |
      (g r : ENNReal) ≤ ENNReal.ofReal (C / (b - a))} := by
  set c : ℝ := C / (b - a) with hc
  set A : ℕ := ⌊c⌋₊ + 1 with hA
  set bb : ENNReal := ENNReal.ofReal c with hb
  set F : ℝ → ENNReal := fun r => (g r : ENNReal) with hF
  set E : Set ℝ := {r ∈ Set.Icc a b | F r ≤ bb} with hE
  by_contra hlt
  have hE0 : MeasureTheory.volume E = 0 :=
    le_antisymm (le_of_not_gt hlt) (show (0 : ENNReal) ≤ MeasureTheory.volume E by positivity)
  -- Upgrade `E` to a measurable null superset.
  obtain ⟨T, hET, hTmeas, hT0⟩ := MeasureTheory.exists_measurable_superset_of_null hE0
  set T' : Set ℝ := T ∩ Set.Icc a b with hT'def
  have hT'meas : MeasurableSet T' := hTmeas.inter measurableSet_Icc
  have hEsub : E ⊆ Set.Icc a b := fun r hr => by rw [hE] at hr; exact hr.1
  have hET' : E ⊆ T' := fun r hr => ⟨hET hr, hEsub hr⟩
  have hT'0 : MeasureTheory.volume T' = 0 := by
    rw [hT'def]
    exact measure_mono_null Set.inter_subset_left hT0
  -- The complement `S` of `T'` inside the interval is measurable, of full measure,
  -- and `F > bb` on it.
  set S : Set ℝ := Set.Icc a b \ T' with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Icc.diff hT'meas
  have hSsub : S ⊆ Set.Icc a b := Set.sdiff_subset
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (b - a) := by
    rw [hSdef, measure_sdiff_null hT'0, Real.volume_Icc]
  have hFS : ∀ r ∈ S, bb < F r := by
    intro r hr
    have hrI : r ∈ Set.Icc a b := hSsub hr
    have hrE : r ∉ E := fun hmem => hr.2 (hET' hmem)
    rw [hE] at hrE
    exact lt_of_not_ge (fun hle => hrE ⟨hrI, hle⟩)
  -- On `S`, the `ℕ∞`-valued function is at least `A`.
  have hFS' : ∀ r ∈ S, (A : ENNReal) ≤ F r := by
    intro r hr
    have h1 : ENNReal.ofReal c < (g r : ENNReal) := by
      have := hFS r hr
      simp only [hb, hF] at this
      exact this
    have h2 : ((⌊c⌋₊ + 1 : ℕ) : ENNReal) ≤ (g r : ENNReal) :=
      Work.Sweep.FewIntersections.natCast_floor_add_one_le_of_ofReal_lt h1
    simp only [hA, hF]
    exact h2
  -- Hence `A · 1_S ≤ F` pointwise, and integrating over `Icc a b` bounds `A · vol S`.
  have hle : (fun r => S.indicator (fun _ => (A : ENNReal)) r) ≤ F := by
    intro r
    change S.indicator (fun _ => (A : ENNReal)) r ≤ F r
    by_cases hr : r ∈ S
    · rw [Set.indicator_of_mem hr]; exact hFS' r hr
    · rw [Set.indicator_of_notMem hr]; exact (show (0 : ENNReal) ≤ F r by positivity)
  have hmono : ∫⁻ r in Set.Icc a b, S.indicator (fun _ => (A : ENNReal)) r
      ≤ ∫⁻ r in Set.Icc a b, F r := lintegral_mono hle
  have h_int_eq : ∫⁻ r in Set.Icc a b, S.indicator (fun _ => (A : ENNReal)) r
      = (A : ENNReal) * MeasureTheory.volume S := by
    rw [MeasureTheory.setLIntegral_indicator hSmeas]
    rw [MeasureTheory.setLIntegral_const]
    congr 1
    rw [Set.inter_eq_left.mpr hSsub]
  have hkey : (A : ENNReal) * MeasureTheory.volume S ≤ ENNReal.ofReal C := by
    rw [← h_int_eq]
    exact le_trans hmono hint
  -- But `A · ofReal (b-a) > ofReal C`, while `vol S = ofReal (b-a)`: contradiction.
  have harith : ENNReal.ofReal C < (A : ENNReal) * ENNReal.ofReal (b - a) := by
    rw [hA, hc]
    exact ofReal_lt_natCast_floor_add_one_mul hab
  rw [hvolS] at hkey
  exact absurd hkey (not_le.mpr harith)

end Work.Sweep.FewIntersectionsGen
