import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixR.FarLatDefs
import Submission.Work.BoseFixR.LatGreen.integrableOn_period
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.FarLat

open MeasureTheory Filter
open scoped ENNReal BigOperators

-- imports used below: Submission.Work.BoseFixR.FarLatDefs, Submission.Work.BoseFixR.LatGreen.integrableOn_period,
-- Submission.Work.BoseFixR.LatGreen.LatGreenAutocorrAux (abs_latGreen_le)
-- NOTE: `hWnn` has been added as advised by review 1 (`ofReal` discards the negative part, so the
-- finiteness hypothesis alone would control only the positive part of the product).
--
-- PROOF ROUTE.  Write `P := period W ℓ` (the ℓ-periodisation of `W`) and `F` for the integrand.
--  * `hWnn` makes `P ≥ 0` a.e.: for a.e. `x` every summand `W (x - ℓn)` is `≥ 0`, so the
--    `tsum` defining `P x` is `≥ 0` (`tsum_nonneg`).
--  * `integrableOn_period` gives `P ∈ L¹(cell ℓ)`, so `∫⁻_{cell} ofReal P = ofReal (∫_{cell} P) < ⊤`.
--  * The sharp two-sided bound `abs_latGreen_le` on the lattice Green's function together with the
--    scaling `latDistL ℓ z = ℓ · latDist (ℓ⁻¹ • z)` gives, on the a.e. set where `P ≥ 0` in both
--    variables,
--      `|P x P y (ℓ² latGreen (ℓ⁻¹(x-y)))| ≤ C₁ · P x P y (latDistL ℓ (x-y))⁻¹ + C₂ · P x P y`
--    with the *nonnegative* constants `C₁ = ℓ³(4π)⁻¹`, `C₂ = ℓ² latGreenLB`.
--  * `ofReal` turns this into an `ENNReal` bound; integrating over the product cell,
--    `∫⁻ ofReal(P x P y (latDistL)⁻¹)` is `< ⊤` by `hfin` and
--    `∫⁻ ofReal(P x) ofReal(P y) = (∫⁻_{cell} ofReal P)² < ⊤` by Tonelli (the product of the two
--    restricted cell measures).  Hence `F` has finite integral and is integrable on the double cell.
theorem latGreen_period_integrable {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (hfin : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1
          * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤) :
    MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ) := by
  classical
  set P : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseFixR.LatGreen.period W ℓ with hP
  set F : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ :=
    (fun p => |P p.1 * P p.2 * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|) with hF
  set C1 : ℝ := ℓ ^ 2 * (4 * Real.pi)⁻¹ * ℓ with hC1
  set C2 : ℝ := ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreenLB with hC2
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  have hC2nn : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (sq_nonneg ℓ) Work.BoseFixR.LatGreen.latGreenLB_nonneg
  -- ## a.e. nonnegativity of the periodisation
  have hWnn' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), 0 ≤ W x := hWnn
  have hPnn : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), 0 ≤ P x := by
    rw [hP]
    have h : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), ∀ n : Fin 3 → ℤ, 0 ≤ W (x - Work.BoseFixR.lat ℓ n) := by
      rw [MeasureTheory.ae_all_iff]
      intro n
      exact (MeasureTheory.measurePreserving_sub_right volume (Work.BoseFixR.lat ℓ n)).quasiMeasurePreserving.ae hWnn'
    filter_upwards [h] with x hx
    exact tsum_nonneg hx
  have hPnn_cell : ∀ᵐ x ∂(volume.restrict (Work.BoseFixR.cell ℓ)), 0 ≤ P x :=
    hPnn.filter_mono MeasureTheory.ae_restrict_le
  -- ## `P` is integrable on the cell
  have hPint : MeasureTheory.Integrable P (volume.restrict (Work.BoseFixR.cell ℓ)) := by
    rw [hP]
    exact Work.BoseFixR.LatGreen.integrableOn_period hℓ hW hper
  -- ## the double cell carries the product of the two restricted cell measures
  have hμ : volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)
      = (volume.restrict (Work.BoseFixR.cell ℓ)).prod (volume.restrict (Work.BoseFixR.cell ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hPnn_prod : ∀ᵐ p ∂((volume.restrict (Work.BoseFixR.cell ℓ)).prod
      (volume.restrict (Work.BoseFixR.cell ℓ))), 0 ≤ P p.1 ∧ 0 ≤ P p.2 := by
    have h1 : ∀ᵐ p ∂((volume.restrict (Work.BoseFixR.cell ℓ)).prod
        (volume.restrict (Work.BoseFixR.cell ℓ))), 0 ≤ P p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hPnn_cell
    have h2 : ∀ᵐ p ∂((volume.restrict (Work.BoseFixR.cell ℓ)).prod
        (volume.restrict (Work.BoseFixR.cell ℓ))), 0 ≤ P p.2 :=
      Measure.quasiMeasurePreserving_snd.ae hPnn_cell
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩
  -- ## the finiteness hypothesis, in terms of `P`
  have hfin' : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
      ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤ := by
    rw [hP]
    exact hfin
  -- ## the scaling identity for the lattice distance
  have hlat : ∀ z : EuclideanSpace ℝ (Fin 3),
      (Work.BoseFixR.LatGreen.latDist (ℓ⁻¹ • z))⁻¹ = ℓ * (Work.BoseFixR.latDistL ℓ z)⁻¹ := by
    intro z
    have h := Work.BoseFixR.latDistL_eq_mul_latDist hℓ z
    have hz : Work.BoseFixR.LatGreen.latDist (ℓ⁻¹ • z) = ℓ⁻¹ * Work.BoseFixR.latDistL ℓ z := by
      rw [h]; field_simp
    rw [hz, mul_inv]; simp
  -- ## measurability of `P` and of the integrand
  have hPae : AEMeasurable P volume := by
    rw [hP]
    refine AEMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (f := fun n x => W (x - Work.BoseFixR.lat ℓ n)) ?_
    intro n
    exact ((hW.comp_sub_right (Work.BoseFixR.lat ℓ n)).aestronglyMeasurable).aemeasurable
  have hP1 : AEMeasurable (P ∘ Prod.fst) volume :=
    AEMeasurable.comp_quasiMeasurePreserving hPae
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))))
  have hP2 : AEMeasurable (P ∘ Prod.snd) volume :=
    AEMeasurable.comp_quasiMeasurePreserving hPae
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))))
  have hG : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) :=
    (Work.BoseFixR.LatGreen.measurable_latGreen.comp
      ((measurable_fst.sub measurable_snd).const_smul (ℓ⁻¹))).const_mul (ℓ ^ 2)
  have hFae : AEMeasurable F volume := ((hP1.mul hP2).mul hG.aemeasurable).abs
  have hFsm : AEStronglyMeasurable F (volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)) :=
    (hFae.mono_measure Measure.restrict_le_self).aestronglyMeasurable
  have hld : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by
    have h : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.latDistL ℓ z) :=
      measurable_infDist
    exact (h.comp (measurable_fst.sub measurable_snd)).inv
  -- ## everything is now stated w.r.t. the product measure `μ2`
  set μ2 : Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
    (volume.restrict (Work.BoseFixR.cell ℓ)).prod (volume.restrict (Work.BoseFixR.cell ℓ)) with hμ2
  have hA : AEMeasurable (fun x : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (P x))
      (volume.restrict (Work.BoseFixR.cell ℓ)) := hPint.1.aemeasurable.ennreal_ofReal
  have hP1c : AEMeasurable (P ∘ Prod.fst) μ2 :=
    AEMeasurable.comp_quasiMeasurePreserving hPint.1.aemeasurable
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Work.BoseFixR.cell ℓ))
        (ν := volume.restrict (Work.BoseFixR.cell ℓ)))
  have hP2c : AEMeasurable (P ∘ Prod.snd) μ2 :=
    AEMeasurable.comp_quasiMeasurePreserving hPint.1.aemeasurable
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Work.BoseFixR.cell ℓ))
        (ν := volume.restrict (Work.BoseFixR.cell ℓ)))
  have hK : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) μ2 :=
    (hP1c.mul hP2c).mul hld.aemeasurable
  have hAEMK : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) μ2 := hK.ennreal_ofReal
  have hAEML : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2)) μ2 :=
    (hP1c.ennreal_ofReal).mul (hP2c.ennreal_ofReal)
  have hAEMA : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal C1 * ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) μ2 :=
    hAEMK.const_mul _
  have hfin2 : (∫⁻ p, ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) ∂μ2) < ⊤ := by
    rw [← hμ]
    exact hfin'
  -- ## Tonelli: the product of the two cell integrals
  have hton : (∫⁻ p, ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2) ∂μ2)
      = (∫⁻ x in Work.BoseFixR.cell ℓ, ENNReal.ofReal (P x))
        * (∫⁻ y in Work.BoseFixR.cell ℓ, ENNReal.ofReal (P y)) := by
    rw [hμ2]
    rw [MeasureTheory.lintegral_prod
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2)) hAEML]
    rw [lintegral_congr (fun x => lintegral_const_mul'' (ENNReal.ofReal (P x)) hA)]
    rw [lintegral_mul_const'' _ hA]
  -- ## the pointwise `ENNReal` bound
  have hbound : ∀ᵐ p ∂μ2, ‖F p‖ₑ
      ≤ ENNReal.ofReal C1 * ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
        + ENNReal.ofReal C2 * (ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2)) := by
    filter_upwards [hPnn_prod] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hpp : 0 ≤ P p.1 * P p.2 := mul_nonneg hp1 hp2
    have habs : |P p.1 * P p.2| = P p.1 * P p.2 := by
      rw [abs_mul, abs_of_nonneg hp1, abs_of_nonneg hp2]
    have hreal : F p ≤ C1 * (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
        + C2 * (P p.1 * P p.2) := by
      show |P p.1 * P p.2 * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))| ≤ _
      calc |P p.1 * P p.2 * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|
          = P p.1 * P p.2 * |ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))| := by
            rw [abs_mul, habs]
        _ = P p.1 * P p.2 * (ℓ ^ 2 * |Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))|) := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg ℓ)]
        _ ≤ P p.1 * P p.2 * (ℓ ^ 2 * ((4 * Real.pi)⁻¹ *
              (Work.BoseFixR.LatGreen.latDist (ℓ⁻¹ • (p.1 - p.2)))⁻¹
              + Work.BoseFixR.LatGreen.latGreenLB)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Work.BoseFixR.LatGreen.abs_latGreen_le _) (sq_nonneg ℓ)) hpp
        _ = P p.1 * P p.2 * (ℓ ^ 2 * ((4 * Real.pi)⁻¹ *
              (ℓ * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
              + Work.BoseFixR.LatGreen.latGreenLB)) := by
            rw [hlat]
        _ = C1 * (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) + C2 * (P p.1 * P p.2) := by
            rw [hC1, hC2]; ring
    calc ‖F p‖ₑ = ENNReal.ofReal ‖F p‖ := (ofReal_norm (F p)).symm
      _ = ENNReal.ofReal (F p) := by rw [Real.norm_of_nonneg (abs_nonneg _)]
      _ ≤ ENNReal.ofReal (C1 * (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
            + C2 * (P p.1 * P p.2)) := ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal (C1 * (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹))
            + ENNReal.ofReal (C2 * (P p.1 * P p.2)) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal C1 * ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
            + ENNReal.ofReal C2 * ENNReal.ofReal (P p.1 * P p.2) := by
            rw [ENNReal.ofReal_mul hC1nn, ENNReal.ofReal_mul hC2nn]
      _ = ENNReal.ofReal C1 * ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
            + ENNReal.ofReal C2 * (ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2)) := by
            rw [ENNReal.ofReal_mul hp1]
  -- ## assembly
  refine ⟨hFsm, ?_⟩
  show (∫⁻ p, ‖F p‖ₑ ∂(volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ))) < ⊤
  rw [hμ]
  calc (∫⁻ p, ‖F p‖ₑ ∂μ2)
      ≤ ∫⁻ p, (ENNReal.ofReal C1 * ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
          + ENNReal.ofReal C2 * (ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2))) ∂μ2 :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal C1 * (∫⁻ p, ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) ∂μ2)
          + ENNReal.ofReal C2 * (∫⁻ p, ENNReal.ofReal (P p.1) * ENNReal.ofReal (P p.2) ∂μ2) := by
        rw [lintegral_add_left' hAEMA, lintegral_const_mul'' _ hAEMK, lintegral_const_mul'' _ hAEML]
    _ = ENNReal.ofReal C1 * (∫⁻ p, ENNReal.ofReal (P p.1 * P p.2 * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) ∂μ2)
          + ENNReal.ofReal C2 * ((∫⁻ x in Work.BoseFixR.cell ℓ, ENNReal.ofReal (P x))
              * (∫⁻ y in Work.BoseFixR.cell ℓ, ENNReal.ofReal (P y))) := by
        rw [hton]
    _ < ⊤ := by
        have hB : (∫⁻ x in Work.BoseFixR.cell ℓ, ENNReal.ofReal (P x)) < ⊤ := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hPint hPnn_cell]
          exact ENNReal.ofReal_lt_top
        exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin2,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hB hB)⟩

end Work.BoseFixR.FarLat
