import Mathlib

namespace Work.Sweep.FewIntersections

open MeasureTheory Set
open scoped ENNReal

/-- If a function `x : ℕ∞` satisfies `ENNReal.ofReal t < (x : ℝ≥0∞)`, then it dominates the
first natural number strictly above `t`, namely `⌊t⌋₊ + 1`.

This is the "integrality" step: the level set `{x > t}` of an `ℕ∞`-valued function is
contained in `{x ≥ ⌊t⌋₊ + 1}`. -/
lemma natCast_floor_add_one_le_of_ofReal_lt {t : ℝ} {x : ℕ∞}
    (h : ENNReal.ofReal t < (x : ENNReal)) :
    ((⌊t⌋₊ + 1 : ℕ) : ENNReal) ≤ (x : ENNReal) := by
  rw [← ENat.toENNReal_coe (⌊t⌋₊ + 1), ENat.toENNReal_le]
  cases x with
  | top => exact le_top
  | coe k =>
      simp only [ENat.toENNReal_coe] at h
      have hk : k ≠ 0 := by
        intro hk0
        rw [hk0, Nat.cast_zero] at h
        exact (not_lt_of_ge (show (0 : ENNReal) ≤ ENNReal.ofReal t by positivity)) h
      have ht : t < (k : ℝ) := (ENNReal.ofReal_lt_natCast hk).mp h
      have hfk : ⌊t⌋₊ < k := (Nat.floor_lt' hk).mpr ht
      have : ⌊t⌋₊ + 1 ≤ k := by omega
      exact_mod_cast this

/-- Arithmetic heart of the Markov-type bound: for `R > 0`, the number `⌊2C/R⌋₊ + 1` times
`R/2` exceeds `C`, written in `ℝ≥0∞`.  (It even exceeds it uniformly by `R/2`:
`(⌊2C/R⌋₊+1)·(R/2) > (2C/R)·(R/2) = C`.) -/
lemma ofReal_lt_natCast_floor_add_one_mul {C R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal C < ((⌊2 * C / R⌋₊ + 1 : ℕ) : ENNReal) * ENNReal.ofReal (R / 2) := by
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  have hfl : 2 * C / R < ((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hA : (0 : ℝ) < ((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ) := by positivity
  have hCR : (2 * C / R) * (R / 2) = C := by field_simp
  have hC : C < ((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ) * (R / 2) := by
    calc C = (2 * C / R) * (R / 2) := hCR.symm
      _ < ((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ) * (R / 2) := mul_lt_mul_of_pos_right hfl hR2
  have hq : (0 : ℝ) < ((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ) * (R / 2) := mul_pos hA hR2
  calc ENNReal.ofReal C
      < ENNReal.ofReal (((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ) * (R / 2)) :=
        (ENNReal.ofReal_lt_ofReal_iff hq).mpr hC
    _ = ENNReal.ofReal (((⌊2 * C / R⌋₊ + 1 : ℕ) : ℝ)) * ENNReal.ofReal (R / 2) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ((⌊2 * C / R⌋₊ + 1 : ℕ) : ENNReal) * ENNReal.ofReal (R / 2) := by
        rw [ENNReal.ofReal_natCast]

/-- **Markov-type positivity for `ℕ∞`-valued functions.**

Let `g : ℝ → ℕ∞` and `R > 0`.  If the upper integral of `(g r : ℝ≥0∞)` over `Icc (R/2) R`
is at most `ofReal C`, then the set of `r ∈ Icc (R/2) R` with
`(g r : ℝ≥0∞) ≤ ofReal (2C/R)` has positive Lebesgue measure.

The threshold `2C/R` is twice the average of `g` over the interval (whose length is `R/2`),
so the statement says that an `ℕ∞`-valued function cannot be above twice its average on
(almost) all of the interval.  No measurability of `g` is assumed: the proof upgrades a
possibly non-measurable null set to a measurable null superset and works with the
(outer) measure throughout. -/
theorem volume_pos_of_lintegral_le {g : ℝ → ℕ∞} {R C : ℝ} (hR : 0 < R)
    (hint : ∫⁻ r in Set.Icc (R / 2) R, (g r : ENNReal) ≤ ENNReal.ofReal C) :
    0 < MeasureTheory.volume {r ∈ Set.Icc (R / 2) R |
      (g r : ENNReal) ≤ ENNReal.ofReal (2 * C / R)} := by
  set A : ℕ := ⌊2 * C / R⌋₊ + 1 with hA
  set b : ENNReal := ENNReal.ofReal (2 * C / R) with hb
  set F : ℝ → ENNReal := fun r => (g r : ENNReal) with hF
  set E : Set ℝ := {r ∈ Set.Icc (R / 2) R | F r ≤ b} with hE
  by_contra hlt
  have hE0 : MeasureTheory.volume E = 0 :=
    le_antisymm (le_of_not_gt hlt) (show (0 : ENNReal) ≤ MeasureTheory.volume E by positivity)
  -- Upgrade `E` to a measurable null superset.
  obtain ⟨T, hET, hTmeas, hT0⟩ := MeasureTheory.exists_measurable_superset_of_null hE0
  set T' : Set ℝ := T ∩ Set.Icc (R / 2) R with hT'def
  have hT'meas : MeasurableSet T' := hTmeas.inter measurableSet_Icc
  have hEsub : E ⊆ Set.Icc (R / 2) R := by intro r hr; rw [hE] at hr; exact hr.1
  have hET' : E ⊆ T' := fun r hr => ⟨hET hr, hEsub hr⟩
  have hT'0 : MeasureTheory.volume T' = 0 := by
    rw [hT'def]
    exact measure_mono_null Set.inter_subset_left hT0
  -- The complement `S` of `T'` inside the interval is measurable, of full measure,
  -- and `F > b` on it.
  set S : Set ℝ := Set.Icc (R / 2) R \ T' with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Icc.diff hT'meas
  have hSsub : S ⊆ Set.Icc (R / 2) R := Set.sdiff_subset
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (R / 2) := by
    rw [hSdef, measure_sdiff_null hT'0, Real.volume_Icc]
    congr 1
    ring
  have hFS : ∀ r ∈ S, b < F r := by
    intro r hr
    have hrI : r ∈ Set.Icc (R / 2) R := hSsub hr
    have hrE : r ∉ E := fun hmem => hr.2 (hET' hmem)
    rw [hE] at hrE
    exact lt_of_not_ge (fun hle => hrE ⟨hrI, hle⟩)
  -- On `S`, the `ℕ∞`-valued function is at least `A`.
  have hFS' : ∀ r ∈ S, (A : ENNReal) ≤ F r := by
    intro r hr
    have h1 : ENNReal.ofReal (2 * C / R) < (g r : ENNReal) := by
      have := hFS r hr
      simp only [hb, hF] at this
      exact this
    have h2 : ((⌊2 * C / R⌋₊ + 1 : ℕ) : ENNReal) ≤ (g r : ENNReal) :=
      natCast_floor_add_one_le_of_ofReal_lt h1
    simp only [hA, hF]
    exact h2
  -- Hence `A · 1_S ≤ F` pointwise, and integrating over `Icc (R/2) R` bounds `A · vol S`.
  have hle : (fun r => S.indicator (fun _ => (A : ENNReal)) r) ≤ F := by
    intro r
    change S.indicator (fun _ => (A : ENNReal)) r ≤ F r
    by_cases hr : r ∈ S
    · rw [Set.indicator_of_mem hr]; exact hFS' r hr
    · rw [Set.indicator_of_notMem hr]; exact (show (0 : ENNReal) ≤ F r by positivity)
  have hmono : ∫⁻ r in Set.Icc (R / 2) R, S.indicator (fun _ => (A : ENNReal)) r
      ≤ ∫⁻ r in Set.Icc (R / 2) R, F r := lintegral_mono hle
  have h_int_eq : ∫⁻ r in Set.Icc (R / 2) R, S.indicator (fun _ => (A : ENNReal)) r
      = (A : ENNReal) * MeasureTheory.volume S := by
    rw [MeasureTheory.setLIntegral_indicator hSmeas]
    rw [MeasureTheory.setLIntegral_const]
    congr 1
    rw [Set.inter_eq_left.mpr hSsub]
  have hkey : (A : ENNReal) * MeasureTheory.volume S ≤ ENNReal.ofReal C := by
    rw [← h_int_eq]
    exact le_trans hmono hint
  -- But `A · ofReal (R/2) > ofReal C`, while `vol S = ofReal (R/2)`: contradiction.
  have harith : ENNReal.ofReal C < (A : ENNReal) * ENNReal.ofReal (R / 2) := by
    rw [hA]
    exact ofReal_lt_natCast_floor_add_one_mul hR
  rw [hvolS] at hkey
  exact absurd hkey (not_le.mpr harith)

end Work.Sweep.FewIntersections
