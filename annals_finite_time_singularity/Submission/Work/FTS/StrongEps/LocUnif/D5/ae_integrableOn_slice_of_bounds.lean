import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. integrability of the slices of `w`, from two lintegral bounds

`Work.FTS.StrongEps.LocUnif.D5.ae_integrableOn_slice_of_bounds`: if on the rectangle
`Icc a b ×ˢ Icc c d` the `ENNReal.ofReal`-lintegrals of `W ^ 2` and of `|W - w|` are bounded
(by `M` and by `ε` respectively), then for almost every `θ ∈ Icc c d` the `z`-slice
`z ↦ w z θ` is integrable on `Icc a b`.

The proof needs no regularity beyond a.e. measurability.  The pointwise bound `|x| ≤ 1 + x ^ 2`
turns the two hypotheses into the finiteness of the `L¹`-norms of `W` and of `W - w` for the
product `(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))` (the restricted measures
are finite, so the constant `1` is integrable), whence `w = W - (W - w)` is integrable for that
product measure.  Tonelli/Fubini in the form `Integrable.prod_left_ae` then yields integrability
of the left slices for a.e. right coordinate.  Finally
`Measure.prod_restrict` identifies `(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))`
with `volume.restrict (Icc a b ×ˢ Icc c d)`.
-/

set_option linter.unusedVariables false

open MeasureTheory

namespace Work.FTS.StrongEps.LocUnif.D5

/-- If the `ENNReal.ofReal`-lintegrals of `W ^ 2` and of `|W - w|` against a product of finite
measures are bounded, then `w`, viewed as a function on the product, is integrable; consequently
its left slices are a.e. integrable. -/
theorem integrable_uncurry_of_lintegral_bounds {μA μB : Measure ℝ} [SFinite μA] [SFinite μB]
    [IsFiniteMeasure μA] [IsFiniteMeasure μB]
    {W w : ℝ → ℝ → ℝ} {M ε : ℝ}
    (hWm : AEMeasurable (Function.uncurry W) (μA.prod μB))
    (hwm : AEMeasurable (Function.uncurry w) (μA.prod μB))
    (hW2 : ∫⁻ p, ENNReal.ofReal ((W p.1 p.2) ^ 2) ∂(μA.prod μB) ≤ ENNReal.ofReal M)
    (hdiff : ∫⁻ p, ENNReal.ofReal |W p.1 p.2 - w p.1 p.2| ∂(μA.prod μB)
      ≤ ENNReal.ofReal ε) :
    ∀ᵐ θ ∂μB, Integrable (fun z => w z θ) μA := by
  -- `W ^ 2` is integrable for the product measure
  have hsq_meas : AEMeasurable (fun p : ℝ × ℝ => (W p.1 p.2) ^ 2) (μA.prod μB) :=
    Measurable.comp_aemeasurable (g := fun x : ℝ => x ^ 2) (by fun_prop) hWm
  have hIntV2 : Integrable (fun p : ℝ × ℝ => (W p.1 p.2) ^ 2) (μA.prod μB) := by
    refine ⟨hsq_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
    exact lt_of_le_of_lt hW2 ENNReal.ofReal_lt_top
  -- `|W - w|` is integrable for the product measure
  have hdiff_meas : AEMeasurable (fun p : ℝ × ℝ => |W p.1 p.2 - w p.1 p.2|) (μA.prod μB) :=
    Measurable.comp_aemeasurable (g := fun x : ℝ => |x|) (by fun_prop) (hWm.sub hwm)
  have hIntD : Integrable (fun p : ℝ × ℝ => |W p.1 p.2 - w p.1 p.2|) (μA.prod μB) := by
    refine ⟨hdiff_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => abs_nonneg _)]
    exact lt_of_le_of_lt hdiff ENNReal.ofReal_lt_top
  -- `W` is integrable for the product measure, by `|x| ≤ 1 + x ^ 2`
  have hIntW : Integrable (fun p : ℝ × ℝ => W p.1 p.2) (μA.prod μB) := by
    refine Integrable.mono (g := fun p : ℝ × ℝ => 1 + (W p.1 p.2) ^ 2)
      ((integrable_const 1).add hIntV2) hWm.aestronglyMeasurable ?_
    filter_upwards with p
    have h1 : 0 ≤ 1 + (W p.1 p.2) ^ 2 := by nlinarith [sq_nonneg (W p.1 p.2)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1]
    nlinarith [abs_nonneg (W p.1 p.2), sq_nonneg (|W p.1 p.2| - 1 / 2), sq_abs (W p.1 p.2)]
  have hIntWdiff : Integrable (fun p : ℝ × ℝ => W p.1 p.2 - w p.1 p.2) (μA.prod μB) :=
    ⟨(hWm.sub hwm).aestronglyMeasurable,
      hIntD.hasFiniteIntegral.mono (Filter.Eventually.of_forall fun p => by
        simp [Real.norm_eq_abs])⟩
  -- `w = W - (W - w)`
  have hIntw : Integrable (fun p : ℝ × ℝ => w p.1 p.2) (μA.prod μB) := by
    refine (hIntW.sub hIntWdiff).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply]
    ring
  exact hIntw.prod_left_ae

theorem ae_integrableOn_slice_of_bounds {a b c d M ε : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) {W : ℝ → ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hWm : AEMeasurable (Function.uncurry W)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable (Function.uncurry w)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hW2 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal ((W p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (hdiff : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal |W p.1 p.2 - w p.1 p.2| ≤ ENNReal.ofReal ε) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
      MeasureTheory.IntegrableOn (fun z => w z θ) (Set.Icc a b) MeasureTheory.volume := by
  -- the product of the restrictions is the restriction of the product measure
  have hμ : (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))
      = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := Measure.prod_restrict _ _
  have h := integrable_uncurry_of_lintegral_bounds
    (μA := volume.restrict (Set.Icc a b)) (μB := volume.restrict (Set.Icc c d))
    (by rw [hμ]; exact hWm) (by rw [hμ]; exact hwm)
    (by rw [hμ]; exact hW2) (by rw [hμ]; exact hdiff)
  simpa only [MeasureTheory.IntegrableOn] using h

end Work.FTS.StrongEps.LocUnif.D5
