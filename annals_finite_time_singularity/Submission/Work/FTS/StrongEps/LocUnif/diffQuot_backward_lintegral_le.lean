import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.DiffQuotFacts
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_pointwise_le
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_measure_null
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_lintegral_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The backward difference-quotient weighted `L²` bound

`diffQuot_backward_lintegral_le`: the weighted `L²`-norm of the backward difference quotient
`z ↦ (u z θ - u (z - h) θ)/h` over `[a', b'] × [c, d]` is bounded by `C` times the weighted
`L²`-norm of `∂_z u` over the larger rectangle `[a, b] × [c, d]`.

The proof is the standard local-uniformity computation: the fundamental theorem of calculus
writes the difference quotient as the mean of `∂_z u` over the window `[z - h, z]`, Cauchy–Schwarz
bounds the square of the mean by the mean of the squares, and the hypothesis `hCw` compares the
weight `w z θ` with `w (z - s) θ` inside the window.  The remaining task is measure-theoretic: the
sliding-window average must be exchanged with the outer integral, done with Tonelli
(`lintegral_lintegral_shift_le`) after replacing the (only a.e. measurable) integrand by a
measurable representative (`ae_lintegral_shift_eq`, from `ae_shift_measure_null`).
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The sliding-window average only sees a null set of parameters.** If `G` and `G'` agree
a.e. on `[a,b] × [c,d]`, then for a.e. `p` in the smaller rectangle `[a',b'] × [c,d]` the
`s`-integrals of `G (p.1 - s, p.2)` and `G' (p.1 - s, p.2)` over `(0, h]` coincide.

This is the a.e. form of "the shift `(p, s) ↦ (p.1 - s, p.2)` pushes a null set of
`[a,b] × [c,d]` to a null set" (`ae_shift_measure_null`); the hypotheses `h < a' - a` and
`b' < b` guarantee that every shifted point `(p.1 - s, p.2)` lies in the larger rectangle, so
the null set where `G ≠ G'` is exactly what has to be avoided. -/
theorem ae_lintegral_shift_eq {a b a' b' c d h : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a)
    {G G' : ℝ × ℝ → ENNReal}
    (hae : G =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)] G') :
    (fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2))
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)]
      (fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)) := by
  set N : Set (ℝ × ℝ) := {q : ℝ × ℝ | ¬ (G q = G' q)} with hNdef
  have hbad : (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) N = 0 := by
    rw [hNdef]; exact MeasureTheory.ae_iff.mp hae
  set B : Set (ℝ × ℝ) := MeasureTheory.toMeasurable
    (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) N with hBdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact measurableSet_toMeasurable _ _
  have hBnull : (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) B = 0 := by
    rw [hBdef, MeasureTheory.measure_toMeasurable]; exact hbad
  have hsub : N ⊆ B := by rw [hBdef]; exact MeasureTheory.subset_toMeasurable _ _
  refine (ae_shift_measure_null haa' hb'b hh hah hBmeas hBnull).mono fun p hp => ?_
  refine lintegral_congr_ae (MeasureTheory.ae_iff.mpr ?_)
  refine measure_mono_null (fun s hs => ?_) hp
  exact hsub hs

theorem diffQuot_backward_lintegral_le {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    (hu_sm : ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b))
    (hu_c : ∀ θ ∈ Set.Icc c d, ContinuousOn (fun z => u z θ) (Set.Icc a b))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2) := by
  set G : ℝ × ℝ → ENNReal :=
    fun q => ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) with hGdef
  have hGmeas : AEMeasurable G (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    hmeas
  obtain ⟨G', hG'meas, hG'ae⟩ := hGmeas
  have hcne : ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hh).ne')
  -- Step 1: the pointwise weighted Cauchy–Schwarz / Jensen bound, integrated.
  have hstep1 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := by
    rw [← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ =>
            ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)),
        ← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)),
        ← lintegral_const_mul' _ _ hcne]
    refine lintegral_mono fun p => ?_
    by_cases hp : p ∈ Set.Icc a' b' ×ˢ Set.Icc c d
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      exact diffQuot_pointwise_le haa' hb'b hh hah hC hw hCw hu_sm hp.1 hp.2
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  -- Step 2: replace `G` by the measurable representative `G'` (a.e. in `p`).
  have hstep2 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)
      = ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) :=
    lintegral_congr_ae (ae_lintegral_shift_eq haa' hb'b hh hah hG'ae)
  -- Step 3: Tonelli + translation invariance of Lebesgue measure.
  have hstep3 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
      ≤ ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q :=
    lintegral_lintegral_shift_le haa' hb'b hh hah hG'meas
  -- Step 4: back to `G` on the large rectangle.
  have hstep4 : ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q
      = ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q :=
    lintegral_congr_ae hG'ae.symm
  calc ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := hstep1
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) := by rw [hstep2]
    _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) :=
        mul_le_mul_right hstep3 _
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q) := by rw [hstep4]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q := by
        rw [mul_assoc, ← mul_assoc (ENNReal.ofReal h)⁻¹,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) := rfl

end Work.FTS.StrongEps.LocUnif
