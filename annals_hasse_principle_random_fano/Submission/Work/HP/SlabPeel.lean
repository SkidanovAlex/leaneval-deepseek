import Mathlib
import Submission.Work.HP.SlabDefs

/-!
# The one-dimensional peeling lemma for slabs

`Work.HP.peel_prod` bounds the measure of a set `S ⊆ ℝ × X` which is contained in
`ℝ × B` and whose first coordinate satisfies `|c * t + g x| ≤ w` on `S`: the measure is at most
the measure of `B` times the width `2w/|c|` of the corresponding slab.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.HP

theorem peel_prod {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (S : Set (ℝ × X)) (hS : MeasurableSet S) (B : Set X) (hB : MeasurableSet B)
    (hSB : ∀ t x, (t, x) ∈ S → x ∈ B)
    (c : ℝ) (hc : c ≠ 0) (g : X → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hSc : ∀ p ∈ S, |c * p.1 + g p.2| ≤ w) :
    (volume.prod μ) S ≤ ENNReal.ofReal (2 * w / |c|) * μ B := by
  have hk : ENNReal.ofReal (2 * w / |c|) = ENNReal.ofReal |c⁻¹| * ENNReal.ofReal (2 * w) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg c⁻¹), abs_inv, div_eq_mul_inv, mul_comm]
  rw [Measure.prod_apply_symm hS]
  have hbound : ∀ x : X, volume ((fun t => (t, x)) ⁻¹' S) ≤
      ENNReal.ofReal (2 * w / |c|) * B.indicator (1 : X → ℝ≥0∞) x := by
    intro x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one, hk]
      have hsub : (fun t => (t, x)) ⁻¹' S ⊆
          (fun t => c * t) ⁻¹' Set.Icc (-w - g x) (w - g x) := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_Icc]
        have h := hSc (t, x) ht
        rw [abs_le] at h
        constructor <;> linarith [h.1, h.2]
      calc volume ((fun t => (t, x)) ⁻¹' S)
          ≤ volume ((fun t => c * t) ⁻¹' Set.Icc (-w - g x) (w - g x)) := measure_mono hsub
        _ = ENNReal.ofReal |c⁻¹| * ENNReal.ofReal ((w - g x) - (-w - g x)) := by
              rw [Real.volume_preimage_mul_left hc, Real.volume_Icc]
        _ = ENNReal.ofReal |c⁻¹| * ENNReal.ofReal (2 * w) := by
              rw [show (w - g x) - (-w - g x) = 2 * w by ring]
    · simp only [Set.indicator_of_notMem hx, mul_zero]
      refine le_of_eq (measure_mono_null ?_ (measure_empty))
      intro t ht
      exact absurd (hSB t x ht) hx
  calc ∫⁻ x, volume ((fun t => (t, x)) ⁻¹' S) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (2 * w / |c|) * B.indicator (1 : X → ℝ≥0∞) x ∂μ :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (2 * w / |c|) * ∫⁻ x, B.indicator (1 : X → ℝ≥0∞) x ∂μ :=
        lintegral_const_mul _ (measurable_const.indicator hB)
    _ = ENNReal.ofReal (2 * w / |c|) * μ B := by rw [lintegral_indicator_one hB]

end Work.HP
