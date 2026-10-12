import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
import Submission.Work.BoseFixR.LatGreen.integrableOn_period
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.latGreen_le_latDistL_pair`

The pair-form (integrated) version of the sharp scaled nearest-image bound
`Work.BoseFixR.latGreen_scaled_le`:

    ∫∫_{cell ℓ × cell ℓ} P x P y · ℓ² G(ℓ⁻¹(x−y))  ≤  (ℓ³/4π) ∫∫_{cell ℓ × cell ℓ} P x P y · d(x−y)⁻¹

where `P = LatGreen.period W ℓ` is the `ℓ`-periodisation of a nonnegative integrable charge `W`,
`G = LatGreen.latGreen` is the `ℤ³`-lattice Coulomb Green's function and
`d = latDistL ℓ` is the distance to the `ℓ`-lattice.

The proof is a direct `integral_mono_ae`: the pointwise bound `latGreen_scaled_le` is multiplied
by the nonnegative weight `P x · P y` (a.e. nonnegative because `W ≥ 0` a.e., hence so is its
periodisation, `period_nonneg_ae`) and integrated.  The two integrability inputs are exactly the
hypotheses: `hB` gives the integrability of the left-hand integrand and `hfin` the a.e. finiteness
of the right-hand one — the latter converted into `Integrable` via
`lintegral_ofReal_ne_top_iff_integrable`, which needs the a.e. strong measurability of the
integrand (`period` as a pointwise `tsum` of translates of `W`, `Real.inv`, and the continuity of
`Metric.infDist`).

Nothing about the size of the cell enters: the statement is purely the pair form of the sharp
pointwise nearest-image bound, and the `hfin` hypothesis is what makes the right-hand side a
legitimate (finite) Bochner integral.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixR.FarLat

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `ℓ`-periodisation `Σ'_n W (· − ℓn)` of an integrable charge is a.e. strongly measurable:
it is a pointwise `tsum` of translates of `W`, and `AEMeasurable.tsum` requires no summability
hypothesis (the summation filter is the unconditional one). -/
private lemma aestronglyMeasurable_period {ℓ : ℝ} {W : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) :
    AEStronglyMeasurable (Work.BoseFixR.LatGreen.period W ℓ) (volume : Measure E3) := by
  have h : AEMeasurable (Work.BoseFixR.LatGreen.period W ℓ) (volume : Measure E3) := by
    unfold Work.BoseFixR.LatGreen.period
    exact AEMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (f := fun n (x : E3) => W (x - Work.BoseFixR.lat ℓ n))
      (fun n => (hW.comp_sub_right (Work.BoseFixR.lat ℓ n)).aestronglyMeasurable.aemeasurable)
  exact h.aestronglyMeasurable

-- imports used below: Submission.Work.BoseFixR.FarLatDefs (which contains `latGreen_scaled_le`,
-- `period_nonneg_ae`), Submission.Work.BoseFixR.LatGreen.integrableOn_period
-- `latGreen_scaled_le hℓ z : ℓ^2 * latGreen (ℓ⁻¹ • z) ≤ (ℓ^3/(4*Real.pi)) * (latDistL ℓ z)⁻¹`
theorem latGreen_le_latDistL_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (hB : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ))
    (hfin : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1
          * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤) :
    (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
      ≤ (ℓ ^ 3 / (4 * Real.pi)) *
          ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
              * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹ := by
  -- The `ℓ`-periodisation `P = Σ'_n W (· - ℓn)`.
  have hPasm : AEStronglyMeasurable (Work.BoseFixR.LatGreen.period W ℓ) (volume : Measure E3) :=
    aestronglyMeasurable_period hW
  have hPnn : 0 ≤ᵐ[(volume : Measure E3)] Work.BoseFixR.LatGreen.period W ℓ :=
    period_nonneg_ae hWnn
  -- a.e. nonnegativity of the pair weight `P x · P y` for the *product* Lebesgue measure
  -- (`volume` on `E3 × E3` is `volume.prod volume` definitionally).
  have h12 : ∀ᵐ p ∂(volume : Measure (E3 × E3)),
      0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2 := by
    have h1 : ∀ᵐ p ∂(volume : Measure (E3 × E3)),
        0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure E3))
        (ν := (volume : Measure E3))).ae hPnn
    have h2 : ∀ᵐ p ∂(volume : Measure (E3 × E3)),
        0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure E3))
        (ν := (volume : Measure E3))).ae hPnn
    filter_upwards [h1, h2] with p hp1 hp2
    exact mul_nonneg hp1 hp2
  have h12c : ∀ᵐ p ∂(volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)),
      0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2 :=
    ae_restrict_of_ae h12
  -- the sharp pointwise nearest-image bound, multiplied by the nonnegative pair weight
  have hle : ∀ᵐ p ∂(volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)),
      Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))
        ≤ (ℓ ^ 3 / (4 * Real.pi)) *
          (Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
            * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [h12] with p hp
    have h := latGreen_scaled_le hℓ (p.1 - p.2)
    calc Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))
        ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * ((ℓ ^ 3 / (4 * Real.pi)) * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) :=
          mul_le_mul_of_nonneg_left h hp
      _ = (ℓ ^ 3 / (4 * Real.pi)) *
          (Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
            * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by ring
  -- strong measurability of the two pair integrands
  have hP1 : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.1)
      (volume : Measure (E3 × E3)) :=
    hPasm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure E3))
        (ν := (volume : Measure E3)))
  have hP2 : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.2)
      (volume : Measure (E3 × E3)) :=
    hPasm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure E3))
        (ν := (volume : Measure E3)))
  have hG : AEStronglyMeasurable
      (fun p : E3 × E3 => ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))
      (volume : Measure (E3 × E3)) := by
    have hcont : Continuous (fun p : E3 × E3 => ℓ⁻¹ • (p.1 - p.2)) :=
      (continuous_fst.sub continuous_snd).const_smul ℓ⁻¹
    exact ((measurable_const.mul
      (Work.BoseFixR.LatGreen.measurable_latGreen.comp hcont.measurable))).aestronglyMeasurable
  have hd : AEStronglyMeasurable
      (fun p : E3 × E3 => (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      (volume : Measure (E3 × E3)) := by
    have hc : Continuous (fun z : E3 => Work.BoseFixR.latDistL ℓ z) := by
      unfold Work.BoseFixR.latDistL
      exact Metric.continuous_infDist_pt _
    exact ((hc.measurable.comp (measurable_fst.sub measurable_snd)).inv).aestronglyMeasurable
  have huasm : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.1
        * Work.BoseFixR.LatGreen.period W ℓ p.2
        * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
      (volume : Measure (E3 × E3)) := (hP1.mul hP2).mul hG
  have hvasm : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.1
        * Work.BoseFixR.LatGreen.period W ℓ p.2
        * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      (volume : Measure (E3 × E3)) := (hP1.mul hP2).mul hd
  -- a.e. nonnegativity of the weighted kernel `P x P y · d(x−y)⁻¹`
  have hvnn : 0 ≤ᵐ[volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)]
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.1
        * Work.BoseFixR.LatGreen.period W ℓ p.2
        * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [h12] with p hp
    exact mul_nonneg hp (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ (p.1 - p.2)))
  -- integrability of the right-hand integrand, from the finiteness hypothesis `hfin`
  have hInt_v : Integrable
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.1
        * Work.BoseFixR.LatGreen.period W ℓ p.2
        * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      (volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hvasm.mono_measure Measure.restrict_le_self) hvnn).mp hfin.ne
  -- integrability of the left-hand integrand, from `hB`
  have hInt_u : Integrable
      (fun p : E3 × E3 => Work.BoseFixR.LatGreen.period W ℓ p.1
        * Work.BoseFixR.LatGreen.period W ℓ p.2
        * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
      (volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)) :=
    (integrable_norm_iff (huasm.mono_measure Measure.restrict_le_self)).mp
      (by simpa only [Real.norm_eq_abs] using hB.integrable)
  -- assemble
  have hInt_cv : Integrable
      (fun p : E3 × E3 => (ℓ ^ 3 / (4 * Real.pi)) *
        (Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹))
      (volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)) :=
    hInt_v.const_mul _
  have hfinal : (∫ p : E3 × E3, (ℓ ^ 3 / (4 * Real.pi)) *
        (Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
        ∂(volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)))
      = (ℓ ^ 3 / (4 * Real.pi)) *
          ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
              * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹ :=
    integral_const_mul _ _
  exact le_trans (integral_mono_ae hInt_u hInt_cv hle) (le_of_eq hfinal)

end Work.BoseFixR.FarLat
