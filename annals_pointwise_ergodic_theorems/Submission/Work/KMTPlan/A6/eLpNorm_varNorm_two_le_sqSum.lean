/-
# The `ℒ²`-bound for the variational norm

The lemma proved here is the `ℒ²`-form of the elementary bound relating the variational norm of
a sequence to its `ℓ²`-norm (`Work.KMTAreas.A7.variationalNorm_le_sqSum`, which itself is the
pointwise inequality

  `𝕍ʳ(a) ≤ (2 · 2^{1/r} + 1) · (∑'_n ‖a n‖ₑ²)^{1/2}`,  `2 ≤ r`).

Here the family `f : ℕ → ℤ → ℂ` is viewed as a family of sequences `(f n x)_n` indexed by the
points `x` of `ℤ` (equipped with the counting measure), and one integrates the pointwise bound
in `x`:

  `‖ 𝕍ʳ(f_·) ‖_{ℒ²(ℤ)} ≤ C · (∑'_n ‖f n‖_{ℒ²(ℤ)}²)^{1/2}`.

Two elementary facts make this exact:

* `eLpNorm_two_rpow_two_count`: for the counting measure on `ℤ`, the square of `eLpNorm · 2` is
  the sum of the squares of the extended norms;
* `eLpNorm_sqrt_tsum_count`: **`ℒ²` of an `ℓ²`-sum is the `ℓ²`-sum of the `ℒ²`-norms**, i.e.
  Tonelli's theorem for the counting measures on `ℤ` and `ℕ`, in `ℝ≥0∞` form:

  `‖ (∑'_n F n ·)^{1/2} ‖_{ℒ²(ℤ)} = (∑'_n ∫⁻_x F n x)^{1/2}`.

Consequently the constant is exactly the pointwise one, `2 · 2^{1/r} + 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum
import Submission.Port.Aesm

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

/-- `eLpNorm · 2` against the counting measure on `ℤ`, as a sum of squares (in `ℝ≥0∞`). -/
private lemma eLpNorm_two_rpow_two_count {ε : Type*} [TopologicalSpace ε] [ENorm ε] (g : ℤ → ε) :
    (eLpNorm g 2 (Measure.count : Measure ℤ)) ^ (2 : ℝ) = ∑' n : ℤ, ‖g n‖ₑ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num), lintegral_count,
    ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ≥0∞).toReal) * 2 = 1 by simp, ENNReal.rpow_one,
    show (2 : ℝ≥0∞).toReal = 2 by simp]

/-- Tonelli's theorem for the counting measures on `ℤ` and `ℕ`, in `ℝ≥0∞` form. -/
private lemma lintegral_tsum_count_comm (F : ℕ → ℤ → ℝ≥0∞) :
    (∫⁻ x : ℤ, ∑' n : ℕ, F n x ∂(Measure.count : Measure ℤ))
      = ∑' n : ℕ, ∫⁻ x : ℤ, F n x ∂(Measure.count : Measure ℤ) := by
  rw [lintegral_count, ENNReal.tsum_comm]
  exact tsum_congr fun n => (lintegral_count (F n)).symm

/-- **`ℒ²` of an `ℓ²`-sum is the `ℓ²`-sum of the `ℒ²`-norms** (for `ℝ≥0∞`-valued functions):
`‖ (∑'_n F n ·)^{1/2} ‖_{ℒ²(ℤ)} = (∑'_n ∫⁻_x F n x)^{1/2}`. -/
private lemma eLpNorm_sqrt_tsum_count (F : ℕ → ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => (∑' n : ℕ, F n x) ^ (1 / 2 : ℝ)) 2 (Measure.count : Measure ℤ)
      = (∑' n : ℕ, ∫⁻ x : ℤ, F n x ∂(Measure.count : Measure ℤ)) ^ (1 / 2 : ℝ) := by
  have hpt : ∀ x : ℤ, ‖(∑' n : ℕ, F n x) ^ (1 / 2 : ℝ)‖ₑ ^ (2 : ℝ) = ∑' n : ℕ, F n x := by
    intro x
    rw [enorm_eq_self, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      ENNReal.rpow_one]
  have hmain : (∫⁻ x : ℤ,
        ‖(∑' n : ℕ, F n x) ^ (1 / 2 : ℝ)‖ₑ ^ (2 : ℝ) ∂(Measure.count : Measure ℤ))
      = ∑' n : ℕ, ∫⁻ x : ℤ, F n x ∂(Measure.count : Measure ℤ) := by
    rw [lintegral_congr hpt, lintegral_tsum_count_comm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞).toReal = 2 by simp, hmain]

/-- **The `ℒ²`-bound for the variational norm.**  For `2 < r` there is `C > 0` with
`‖𝕍ʳ(f_·)‖_{ℒ²(ℤ)} ≤ C (∑'_n ‖f n‖_{ℒ²(ℤ)}²)^{1/2}` for every family `f : ℕ → ℤ → ℂ`.  The
constant is the pointwise one, `C = 2 · 2^{1/r} + 1`. -/
theorem eLpNorm_varNorm_two_le_sqSum (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => f n x)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            (∑' n : ℕ, (MeasureTheory.eLpNorm (f n) 2 MeasureTheory.Measure.count) ^ (2 : ℝ))
              ^ (1 / 2 : ℝ) := by
  refine ⟨2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1, ?_, ?_⟩
  · have h : 0 < (2 : ℝ) ^ (1 / (r : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  · intro f
    have hrle : (2 : NNReal) ≤ r := le_of_lt hr
    -- the pointwise variational bound, integrated in `x`
    have hmono : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => f n x)) 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
              ((∑' n : ℕ, ‖f n x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
      rw [enorm_eq_self, enorm_eq_self]
      exact Work.KMTAreas.A7.variationalNorm_le_sqSum hrle (fun n : ℕ => f n x)
    -- each `ℒ²`-norm squared is the sum of the squares of the extended norms
    have hkey : (∑' n : ℕ, ∫⁻ x : ℤ, ‖f n x‖ₑ ^ (2 : ℝ) ∂
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
        = ∑' n : ℕ, (MeasureTheory.eLpNorm (f n) 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) ^ (2 : ℝ) := by
      refine tsum_congr fun n => ?_
      rw [lintegral_count]
      exact (eLpNorm_two_rpow_two_count (f n)).symm
    calc MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => f n x)) 2
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
              ((∑' n : ℕ, ‖f n x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) 2
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := hmono
      _ = ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
            MeasureTheory.eLpNorm (fun x : ℤ => (∑' n : ℕ, ‖f n x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) 2
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
          Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
            (μ := (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
            (V := fun x : ℤ => (∑' n : ℕ, ‖f n x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
            (c := ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1))
            ENNReal.ofReal_ne_top (by norm_num) (by norm_num)
      _ = ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
            (∑' n : ℕ, (MeasureTheory.eLpNorm (f n) 2
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) ^ (2 : ℝ))
                ^ (1 / 2 : ℝ) := by
          rw [eLpNorm_sqrt_tsum_count (fun n x => ‖f n x‖ₑ ^ (2 : ℝ)), hkey]

end Work.KMTPlan.A6
