import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixR.FarLatDefs
import Submission.Work.BoseFixR.LatGreen.integrableOn_period
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.cellProdLintegralSplit`

Tonelli/Fubini splitting of a two-variable `lintegral` over the product cell
`cell ℓ ×ˢ cell ℓ` into an iterated integral over `cell ℓ`:

`∫⁻ p in (cell ℓ ×ˢ cell ℓ), F p.1 * F p.2 * Φ (p.1 - p.2)
   = ∫⁻ x in cell ℓ, F x * ∫⁻ y in cell ℓ, F y * Φ (x - y)`.

The only content beyond Mathlib's Tonelli theorem for set integrals (`setLIntegral_prod`) is

* the a.e. measurability of the pair integrand `(x,y) ↦ F x * F y * Φ (x - y)`: the difference
  map `(x,y) ↦ x - y` is quasi-measure-preserving for Lebesgue measure (it is the second
  projection composed with the measure-preserving shear `(x,y) ↦ (y, x - y)`);
* pulling the constant `F x` out of the inner integral (`lintegral_mul_const''`), which needs
  `y ↦ F y * Φ (x - y)` to be a.e. measurable; for fixed `x` the map `y ↦ x - y` is
  quasi-measure-preserving (a translation composed with the negation).
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixR.FarLat

/-- The difference map `(x, y) ↦ x - y` is quasi-measure-preserving for Lebesgue measure on
`ℝ³ × ℝ³`: it is `Prod.snd` composed with the measure-preserving shear `(x,y) ↦ (y, x - y)`. -/
private lemma subPair_aemeasurable {f : EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hf : AEMeasurable f (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f (p.1 - p.2))
      (volume : Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) := by
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.1 - p.2)
      (volume : Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))).comp
      ((measurePreserving_prod_sub_swap (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))).quasiMeasurePreserving)
  exact hf.comp_quasiMeasurePreserving hqmp

/-- For fixed `x`, the map `y ↦ x - y` is quasi-measure-preserving for Lebesgue measure: it is
the translation `y ↦ x + y` composed with the negation `y ↦ -y`, both of which preserve
Lebesgue measure (up to absolute continuity). -/
private lemma subAemeasurable_fixed (x : EuclideanSpace ℝ (Fin 3))
    {f : EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hf : AEMeasurable f (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) => f (x - y))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hneg : Measure.QuasiMeasurePreserving (fun y : EuclideanSpace ℝ (Fin 3) => -y)
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
    refine ⟨measurable_neg, ?_⟩
    rw [Measure.map_neg_eq_self]
  have hsub : Measure.QuasiMeasurePreserving (fun y : EuclideanSpace ℝ (Fin 3) => x - y)
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (quasiMeasurePreserving_add_left (volume : Measure (EuclideanSpace ℝ (Fin 3))) x).comp hneg
  exact hf.comp_quasiMeasurePreserving hsub

theorem cellProdLintegralSplit {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F Φ : EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hF : AEMeasurable F MeasureTheory.volume)
    (hΦ : AEMeasurable Φ MeasureTheory.volume) :
    (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        F p.1 * F p.2 * Φ (p.1 - p.2))
      = ∫⁻ x in Work.BoseFixR.cell ℓ,
          F x * ∫⁻ y in Work.BoseFixR.cell ℓ, F y * Φ (x - y) := by
  -- the pair integrand is a.e. measurable on the product
  have hg : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        F p.1 * F p.2 * Φ (p.1 - p.2)) (volume.prod volume) :=
    (hF.comp_fst.mul hF.comp_snd).mul (subPair_aemeasurable hΦ)
  -- Tonelli for the set integral `cell ℓ ×ˢ cell ℓ`
  have h1 : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        F p.1 * F p.2 * Φ (p.1 - p.2))
      = ∫⁻ x in Work.BoseFixR.cell ℓ,
          ∫⁻ y in Work.BoseFixR.cell ℓ, F x * F y * Φ (x - y) := by
    refine setLIntegral_prod (f := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        F p.1 * F p.2 * Φ (p.1 - p.2)) ?_
    exact hg.mono_measure Measure.restrict_le_self
  rw [h1]
  -- pull the constant `F x` out of the inner integral
  refine lintegral_congr fun x => ?_
  have hfm : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) => F y * Φ (x - y))
      (volume.restrict (Work.BoseFixR.cell ℓ)) :=
    (hF.restrict).mul ((subAemeasurable_fixed x hΦ).restrict)
  rw [show (∫⁻ y in Work.BoseFixR.cell ℓ, F x * F y * Φ (x - y))
      = ∫⁻ y in Work.BoseFixR.cell ℓ, (F y * Φ (x - y)) * F x from by
        refine lintegral_congr fun y => ?_
        ac_rfl]
  rw [lintegral_mul_const'' (F x) hfm, mul_comm]

end Work.BoseFixR.FarLat
