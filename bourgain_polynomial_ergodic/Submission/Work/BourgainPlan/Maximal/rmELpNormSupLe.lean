import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstRademacherMenshov
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal

/-!
# The `Lᵖ` form of the Rademacher–Menshov reduction of a finite supremum

`mstRademacherMenshov.lean` proves the *pointwise* MST inequality: for a sequence `a : ℕ → E`,
`‖a j − a j₀‖ ≤ 2 · Σ_{i ≤ s} rmLevel s i a` whenever `j, j₀ ≤ 2^s`.

Here we integrate it.  For nonnegative functions `t j` and `1 ≤ p`,

`‖sup_{j ≤ 2^s} t j‖_{Lᵖ} ≤ ‖t 0‖_{Lᵖ} + 2 · Σ_{i ≤ s} ‖rmLevel s i (t ·)‖_{Lᵖ}`,

with the sup taken in `ℝ≥0∞` (via `ENNReal.ofReal`) so that the finitely many values `t j x` are
compared in the complete lattice `ℝ≥0∞`.  The proof is purely pointwise plus the two
`ℝ≥0∞`-valued `Lᵖ` facts (Minkowski and homogeneity of `eLpNorm`), both of which already live in
`Submission.Commons.MeasureTheory.Lp`; the only real work is measurability of the dyadic block
square functions of `t`, which is where the hypotheses `ht` (measurablility of each `ofReal (t j ·)`)
and `ht0` (positivity of the `t j`) are used.

This is the step that transfers the pointwise MST inequality to the `Lᵖ` maximal inequality for the
Rademacher–Menshov square functions, i.e. the analytic content of Bourgain's §7.3 "levels" argument
in the form in which the `WindowWeakType` bootstrap consumes it.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators

theorem rmELpNormSupLe {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (s : ℕ) {p : ℝ} (hp : 1 ≤ p) (t : ℕ → X → ℝ)
    (ht : ∀ j, AEMeasurable (fun x => ENNReal.ofReal (t j x)) μ)
    (ht0 : ∀ j x, 0 ≤ t j x) :
    MeasureTheory.eLpNorm (fun x => (⨆ j ∈ Finset.range (2 ^ s + 1), ENNReal.ofReal (t j x)))
        (ENNReal.ofReal p) μ
      ≤ MeasureTheory.eLpNorm (fun x => ENNReal.ofReal (t 0 x)) (ENNReal.ofReal p) μ
        + ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
            MeasureTheory.eLpNorm (fun x => ENNReal.ofReal
              (Work.BourgainPlan.Maximal.rmLevel s i (fun j => t j x))) (ENNReal.ofReal p) μ := by
  -- Measurability of the level-`i` block square functions of `t`.
  have hRm : ∀ i, AEMeasurable (fun x => ENNReal.ofReal (rmLevel s i (fun j => t j x))) μ := fun i => by
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    unfold rmLevel
    apply AEMeasurable.sqrt
    apply Finset.aemeasurable_fun_sum
    intro m hm
    exact (((((ht ((m + 1) * 2 ^ i)).ennreal_toReal).congr
              (Filter.Eventually.of_forall (fun x => ENNReal.toReal_ofReal (ht0 _ x)))).sub
            (((ht (m * 2 ^ i)).ennreal_toReal).congr
              (Filter.Eventually.of_forall (fun x => ENNReal.toReal_ofReal (ht0 _ x))))).norm.pow_const 2)
  have hRae : AEMeasurable
      (fun x => ∑ i ∈ Finset.range (s + 1), ENNReal.ofReal (rmLevel s i (fun j => t j x))) μ :=
    Finset.aemeasurable_fun_sum _ (fun i _ => hRm i)
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hp0ne : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hp)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  -- The pointwise Rademacher–Menshov bound, in `ℝ≥0∞`.
  have hpoint : ∀ x, (⨆ j ∈ Finset.range (2 ^ s + 1), ENNReal.ofReal (t j x))
      ≤ ENNReal.ofReal (t 0 x)
        + ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
            ENNReal.ofReal (rmLevel s i (fun j => t j x)) := by
    intro x
    have hRnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (s + 1), rmLevel s i (fun j => t j x) :=
      Finset.sum_nonneg (fun i _ => rmLevel_nonneg s i (fun j => t j x))
    have hsup : (⨆ j ∈ Finset.range (2 ^ s + 1), ENNReal.ofReal (t j x))
        ≤ ENNReal.ofReal
            (t 0 x + 2 * ∑ i ∈ Finset.range (s + 1), rmLevel s i (fun j => t j x)) := by
      refine iSup₂_le (fun j hj => ?_)
      have hj' : j ≤ 2 ^ s := by
        have := Finset.mem_range.mp hj; omega
      have h := rm_le_sum_levels s (fun j => t j x) hj' (Nat.zero_le _)
      have h' : |t j x - t 0 x|
          ≤ 2 * ∑ i ∈ Finset.range (s + 1), rmLevel s i (fun j => t j x) := by
        simpa [Real.norm_eq_abs] using h
      have hle : t j x ≤ t 0 x + 2 * ∑ i ∈ Finset.range (s + 1), rmLevel s i (fun j => t j x) := by
        have := le_abs_self (t j x - t 0 x); linarith
      exact ENNReal.ofReal_le_ofReal hle
    refine hsup.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (ht0 0 x) (by linarith),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => rmLevel_nonneg s i (fun j => t j x))]
  -- Monotone transfer to `eLpNorm`.
  have h1 : MeasureTheory.eLpNorm
        (fun x => (⨆ j ∈ Finset.range (2 ^ s + 1), ENNReal.ofReal (t j x)))
        (ENNReal.ofReal p) μ
      ≤ MeasureTheory.eLpNorm
          (fun x => ENNReal.ofReal (t 0 x)
            + ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
                ENNReal.ofReal (rmLevel s i (fun j => t j x))) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_enorm
      (AEMeasurable.iSup fun j => AEMeasurable.iSup fun _ => ht j).aestronglyMeasurable
    intro x
    rw [enorm_eq_self, enorm_eq_self]
    exact hpoint x
  -- Minkowski.
  have h2 : MeasureTheory.eLpNorm
        (fun x => ENNReal.ofReal (t 0 x)
          + ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
              ENNReal.ofReal (rmLevel s i (fun j => t j x))) (ENNReal.ofReal p) μ
      ≤ MeasureTheory.eLpNorm (fun x => ENNReal.ofReal (t 0 x)) (ENNReal.ofReal p) μ
        + MeasureTheory.eLpNorm
            (fun x => ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
                ENNReal.ofReal (rmLevel s i (fun j => t j x))) (ENNReal.ofReal p) μ := by
    refine eLpNorm_add_le (f := fun x => ENNReal.ofReal (t 0 x))
      (g := fun x => ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
        ENNReal.ofReal (rmLevel s i (fun j => t j x))) hp1
  -- Homogeneity of `eLpNorm` in `ℝ≥0∞`.
  have hV : MeasureTheory.eLpNorm
        (fun x => ENNReal.ofReal 2 * ∑ i ∈ Finset.range (s + 1),
            ENNReal.ofReal (rmLevel s i (fun j => t j x))) (ENNReal.ofReal p) μ
      = ENNReal.ofReal 2 * MeasureTheory.eLpNorm
          (fun x => ∑ i ∈ Finset.range (s + 1), ENNReal.ofReal (rmLevel s i (fun j => t j x)))
          (ENNReal.ofReal p) μ :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
      (V := fun x => ∑ i ∈ Finset.range (s + 1), ENNReal.ofReal (rmLevel s i (fun j => t j x)))
      ENNReal.ofReal_ne_top hp0ne hptop
  -- Minkowski for the finite sum of level functions.
  have hsum : MeasureTheory.eLpNorm
        (fun x => ∑ i ∈ Finset.range (s + 1), ENNReal.ofReal (rmLevel s i (fun j => t j x)))
        (ENNReal.ofReal p) μ
      ≤ ∑ i ∈ Finset.range (s + 1),
          MeasureTheory.eLpNorm (fun x => ENNReal.ofReal (rmLevel s i (fun j => t j x)))
            (ENNReal.ofReal p) μ :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal hp1 (fun i _ => hRm i)
  exact (h1.trans h2).trans
    (add_le_add le_rfl ((le_of_eq hV).trans (mul_le_mul_right hsum (ENNReal.ofReal 2))))

end Work.BourgainPlan.Maximal
