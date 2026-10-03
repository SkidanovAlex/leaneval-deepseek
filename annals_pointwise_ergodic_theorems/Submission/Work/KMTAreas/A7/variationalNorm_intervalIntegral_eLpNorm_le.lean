/-
# The variational norm of a time average, in `ℒᵠ(ℤ)`

If a family `X : ℝ → ℕ → ℤ → ℂ` has, for every `t` in `[1/2, 1]`, `ℒᵠ(ℤ)`-norm (counting measure)
of the variational norm of its `n`-family at most `C`, then the same holds for the family of
*time averages* `n ↦ ∫_{1/2}^1 X t n x dt`.

The proof has three ingredients.

* `Work.KMTAreas.A7.eLpNorm_lintegral_le` (Minkowski's integral inequality for the counting
  measure on `ℤ`): it is enough to bound `eLpNorm (fun x => ∫⁻ t, VN r (fun n => X t n x))`.
* The pointwise (in `x`) inequality `VN r (fun n => ∫_t X t n ·) ≤ ∫⁻ t, VN r (fun n => X t n ·)`,
  which is the Minkowski integral inequality for the variational norm of a Bochner integral
  (`Work.KMTAreas.A7.variationalNorm_integral_le`).
* The hypothesis, read pointwise in `x`: on the counting measure of `ℤ`, the `ℒᵠ`-norm dominates
  every single value (`le_eLpNorm_count`), so `VN r (fun n => X t n x) ≤ C` for all `t ∈ [1/2,1]`
  and all `x`, which in turn bounds every slice `t ↦ X t n x` by the constant `C` and hence makes
  each slice integrable (`X` is a.e. measurable in `t` by hypothesis, `hX`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.eLpNorm_lintegral_le
import Submission.Work.KMTAreas.A7.aemeasurable_slice_prod_count
import Submission.Work.KMTAreas.A7.variationalNorm_integral_le
import Submission.Port.Aesm

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- On `ℤ` with the counting measure every point has measure one, so the `ℒᵠ`-norm dominates each
value: `f x ≤ ‖f‖_{ℒᵠ(ℤ)}` for every `q ≥ 1`. -/
lemma le_eLpNorm_count {f : ℤ → ENNReal} {q : ENNReal} (hq : 1 ≤ q) (x : ℤ) :
    f x ≤ MeasureTheory.eLpNorm f q MeasureTheory.Measure.count := by
  rcases eq_or_ne q ⊤ with hqtop | hqtop
  · subst hqtop
    rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm), MeasureTheory.eLpNormEssSup_count]
    exact le_trans (le_of_eq (enorm_eq_self (f x))) (le_iSup (fun x => ‖f x‖ₑ) x)
  · have hq0 : q ≠ 0 := fun h0 => by rw [h0] at hq; exact absurd hq (by norm_num)
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqtop]
    simp only [enorm_eq_self]
    have h1 : f x ^ q.toReal ≤ ∫⁻ y, f y ^ q.toReal ∂MeasureTheory.Measure.count := by
      rw [MeasureTheory.lintegral_count]
      exact ENNReal.le_tsum (f := fun a : ℤ => f a ^ q.toReal) x
    have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
    calc f x = (f x ^ q.toReal) ^ (1 / q.toReal) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hqpos.ne', ENNReal.rpow_one]
      _ ≤ (∫⁻ y, f y ^ q.toReal ∂MeasureTheory.Measure.count) ^ (1 / q.toReal) :=
          ENNReal.rpow_le_rpow h1 (by positivity)

/-- Consequence of `le_eLpNorm_count` in the form used below. -/
lemma le_of_eLpNorm_count_le {f : ℤ → ENNReal} {q : ENNReal} (hq : 1 ≤ q) {C : ENNReal}
    (h : MeasureTheory.eLpNorm f q MeasureTheory.Measure.count ≤ C) (x : ℤ) : f x ≤ C :=
  le_trans (le_eLpNorm_count hq x) h

theorem variationalNorm_intervalIntegral_eLpNorm_le (r : NNReal) (hr : 1 ≤ r) (q : ENNReal)
    (hq : 1 ≤ q) (X : ℝ → ℕ → ℤ → ℂ) (C : ENNReal)
    (hX : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℤ => X p.1 n p.2)
      (MeasureTheory.volume.prod MeasureTheory.Measure.count))
    (h : ∀ t ∈ Set.Icc ((1:ℝ)/2) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x))
        q MeasureTheory.Measure.count ≤ C) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1:ℝ)/2)..1, X t n x)) q MeasureTheory.Measure.count ≤ C := by
  classical
  rcases eq_or_ne C ⊤ with hC | hCtop
  · rw [hC]; exact le_top
  -- Step 1: the hypothesis, read pointwise in `x`.
  have hslice : ∀ t ∈ Set.Icc ((1:ℝ)/2) 1, ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x) ≤ C :=
    fun t ht x => le_of_eLpNorm_count_le hq (h t ht) x
  -- Step 2: every slice of `X` is bounded by `C` on the interval, hence integrable.
  have hbd : ∀ t ∈ Set.Ioc ((1:ℝ)/2) 1, ∀ n : ℕ, ∀ x : ℤ, ‖X t n x‖ ≤ C.toReal := by
    intro t ht n x
    have h1 : ‖X t n x‖ₑ ≤ C :=
      le_trans (enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => X t n x) n)
        (hslice t (Set.Ioc_subset_Icc_self ht) x)
    rw [← ENNReal.ofReal_le_iff_le_toReal hCtop]
    rwa [ofReal_norm]
  have hint : ∀ n : ℕ, ∀ x : ℤ,
      Integrable (fun t : ℝ => X t n x) (MeasureTheory.volume.restrict (Set.Ioc ((1:ℝ)/2) 1)) := by
    intro n x
    refine Integrable.of_bound ?_ C.toReal ?_
    · exact ((aemeasurable_slice_prod_count n (hX n) x).restrict).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbd t ht n x
  -- Step 3: the pointwise (in `x`) Minkowski inequality for the variational norm.
  have hcrux : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∫ t in ((1:ℝ)/2)..1, X t n x)
      ≤ ∫⁻ t in Set.Ioc ((1:ℝ)/2) 1,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x) := by
    intro x
    have hA := variationalNorm_integral_le (r := r) hr
      (ν := MeasureTheory.volume.restrict (Set.Ioc ((1:ℝ)/2) 1)) (g := fun t n => X t n x)
      (fun n => hint n x)
    simpa only [intervalIntegral.integral_of_le (by norm_num : ((1:ℝ)/2) ≤ 1)] using hA
  -- Step 4: assemble, using Minkowski for the counting measure on `ℤ`.
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1:ℝ)/2)..1, X t n x)) q MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc ((1:ℝ)/2) 1,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x))
          q MeasureTheory.Measure.count := by
        refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
        simpa only [enorm_eq_self] using hcrux x
    _ ≤ C := eLpNorm_lintegral_le q hq (fun t x =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x)) C
        (fun t ht => h t (Set.Ioc_subset_Icc_self ht))

end Work.KMTAreas.A7
