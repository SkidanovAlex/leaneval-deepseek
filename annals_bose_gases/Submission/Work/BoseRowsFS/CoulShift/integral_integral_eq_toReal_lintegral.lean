import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Iterated Lebesgue integral of a nonnegative kernel equals the `toReal` of the
iterated Lebesgue (lower) integral

For a nonnegative, a.e.-measurable kernel `g` on `ℝ³ × ℝ³` whose iterated `∫⁻` is finite, the
iterated Bochner integral of `g` is the `toReal` of the iterated `∫⁻` of `ENNReal.ofReal g`.

The proof goes through the product measure `volume.prod volume`:

* `g` is integrable on the product: its `‖·‖ₑ`-integral is the `∫⁻` of `ENNReal.ofReal g`, which
  is computed by Tonelli (`MeasureTheory.lintegral_prod`) and is finite by hypothesis;
* `MeasureTheory.integral_prod` rewrites the iterated integral as the integral on the product;
* `MeasureTheory.integral_eq_lintegral_of_nonneg_ae` rewrites the latter as `.toReal` of the
  product `∫⁻`, which Tonelli turns back into the iterated `∫⁻`.
-/

namespace Work.BoseRowsFS.CoulShift

theorem integral_integral_eq_toReal_lintegral {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg0 : ∀ x y, 0 ≤ g x y)
    (hgm : AEMeasurable (Function.uncurry g) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y)) ≠ ⊤) :
    (∫ x, ∫ y, g x y) = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y)).toReal := by
  have hlin : (∫⁻ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Function.uncurry g z) ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y)) := by
    rw [MeasureTheory.lintegral_prod _ hgm.ennreal_ofReal]
    simp [Function.uncurry]
  have hfin' : (∫⁻ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Function.uncurry g z) ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≠ ⊤ := by
    rw [hlin]; exact hfin
  have hHFI : MeasureTheory.HasFiniteIntegral (Function.uncurry g)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    rw [show (∫⁻ z, ‖Function.uncurry g z‖ₑ ∂(MeasureTheory.volume.prod MeasureTheory.volume))
        = (∫⁻ z, ENNReal.ofReal (Function.uncurry g z)
            ∂(MeasureTheory.volume.prod MeasureTheory.volume)) from
      MeasureTheory.lintegral_congr (fun z => Real.enorm_eq_ofReal (hg0 z.1 z.2))]
    exact lt_top_iff_ne_top.mpr hfin'
  have hInt : MeasureTheory.Integrable (Function.uncurry g)
      (MeasureTheory.volume.prod MeasureTheory.volume) := ⟨hgm.aestronglyMeasurable, hHFI⟩
  have hprod : (∫ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        Function.uncurry g z ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      = (∫ x, ∫ y, g x y) := by
    rw [MeasureTheory.integral_prod (Function.uncurry g) hInt]
    simp [Function.uncurry]
  rw [← hprod]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := MeasureTheory.volume.prod MeasureTheory.volume)
      (f := Function.uncurry g)
      (Filter.Eventually.of_forall (fun z => hg0 z.1 z.2)) hgm.aestronglyMeasurable]
  rw [hlin]

end Work.BoseRowsFS.CoulShift
