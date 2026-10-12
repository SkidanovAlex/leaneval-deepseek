import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseFixR.FarLat

-- imports used below: Submission.Work.BoseFixR.FarLatDefs
-- (and, through it, `Work.BoseFixR.period_nonneg_ae`; the sibling
--  `Work.BoseFixR.LatGreen.integrableOn_period` is *not* needed here).
--
-- PROOF ROUTE.  Write `P := period W ℓ` and `F p := P p.1 * P p.2 * (latDistL ℓ (p.1 - p.2))⁻¹`.
--  * `hWnn` makes `P ≥ 0` a.e. on the whole space (`period_nonneg_ae`); pushing that a.e.
--    statement through the two projections (quasi-measure-preserving for the product measure)
--    and restricting to the double cell gives `0 ≤ F` a.e. on `cell ℓ ×ˢ cell ℓ`.
--  * `P` is a.e. measurable -- it is a pointwise `tsum` of translates of the integrable `W`
--    (`AEMeasurable.tsum`) -- and `p ↦ (latDistL ℓ (p.1 - p.2))⁻¹` is measurable
--    (`measurable_infDist`), so `F` is a.e. strongly measurable on the restricted product measure.
--  * On the a.e. set where `F ≥ 0`, `‖F p‖ₑ = ENNReal.ofReal (F p)` (`Real.enorm_of_nonneg`),
--    so `HasFiniteIntegral F` is *equivalent* to the finiteness of
--    `∫⁻ p in (cell ℓ ×ˢ cell ℓ), ofReal (F p)` (`hasFiniteIntegral_iff_ofReal`), which is exactly
--    the hypothesis `hfin`.
theorem integrableOn_latDistL_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (hfin : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1
          * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤) :
    MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ) := by
  classical
  -- ## a.e. measurability of the periodisation
  have hPae : AEMeasurable (Work.BoseFixR.LatGreen.period W ℓ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
    change AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => ∑' n : Fin 3 → ℤ, W (x - Work.BoseFixR.lat ℓ n))
      MeasureTheory.volume
    refine AEMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (f := fun n x => W (x - Work.BoseFixR.lat ℓ n)) ?_
    intro n
    exact ((hW.comp_sub_right (Work.BoseFixR.lat ℓ n)).aestronglyMeasurable).aemeasurable
  -- ## a.e. nonnegativity of the periodisation
  have hPnn : 0 ≤ᵐ[MeasureTheory.volume] Work.BoseFixR.LatGreen.period W ℓ :=
    Work.BoseFixR.period_nonneg_ae hWnn
  -- ## push it to the product measure and restrict to the double cell
  have hP1 : ∀ᵐ p ∂(MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))),
      0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))).ae hPnn
  have hP2 : ∀ᵐ p ∂(MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))),
      0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.2 :=
    (Measure.quasiMeasurePreserving_snd
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))).ae hPnn
  have hP1c : ∀ᵐ p ∂(MeasureTheory.volume.restrict
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)),
      0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 :=
    hP1.filter_mono (MeasureTheory.ae_restrict_le
      (s := Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ))
  have hP2c : ∀ᵐ p ∂(MeasureTheory.volume.restrict
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)),
      0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.2 :=
    hP2.filter_mono (MeasureTheory.ae_restrict_le
      (s := Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ))
  -- ## a.e. nonnegativity of the integrand on the double cell
  have hFnn : 0 ≤ᵐ[MeasureTheory.volume.restrict
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)]
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by
    filter_upwards [hP1c, hP2c] with p hp1 hp2
    exact mul_nonneg (mul_nonneg hp1 hp2)
      (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ (p.1 - p.2)))
  -- ## a.e. strong measurability of the integrand
  have hld : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by
    have h : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.latDistL ℓ z) :=
      measurable_infDist
    exact (h.comp (measurable_fst.sub measurable_snd)).inv
  have hFae : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
        * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) :=
    (hPae.comp_fst.mul hPae.comp_snd).mul hld.aemeasurable
  refine ⟨hFae.mono_measure Measure.restrict_le_self |>.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hFnn]
  exact hfin

end Work.BoseFixR.FarLat
