import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.CmpSupp.meas_bundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

open MeasureTheory Set

/-- **The three measurabilities of the level-`0` energy of the mode series**, for a general
source: the a.e.-measurability of the truncated angular energy `z ↦ ∫⁻_θ ofReal (Ψ_N² w² σ)`,
of the angular density at each `z ∈ Iz`, and of the outer `lintegral`.  The only input is the
a.e.-measurability of the radial coefficients `acoeff α m F`; no regularity of `F` itself is
needed (the angular factor of each summand is the fixed continuous `eFam m`).

This is `Work.FTS.ClassCHon.CmpSupp.meas_bundle` with its unused hypotheses (`hα`, `hα1`,
`horth`, `hsm`, `hL2`) dropped; its proof (which mentions none of them) applies verbatim. -/
theorem meas_bundle_open {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hacm : ∀ m : ℕ, AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    ∧ (∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- The proof is that of `Work.FTS.ClassCHon.CmpSupp.meas_bundle`, which mentions none of the
  -- hypotheses dropped here; we reuse its building blocks (`hkIntegrand_zero`, `measurable_w`,
  -- `measurable_sin_rpow_half`, `measurable_sEta`, `aemeasurable_psiSeries_uncurry`).
  have hzero : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ
      = (Work.FTS.PhiStar.Series.psiSeries α F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun z θ => CmpSupp.hkIntegrand_zero α F z θ
  -- the truncated series is jointly measurable on `Iz × Iθ`
  have hTrunc : ∀ N : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro N
    unfold Work.FTS.PhiStar.Series.psiTrunc
    refine Finset.aemeasurable_fun_sum _ (fun m _ => ?_)
    exact ((hacm m).comp_fst).mul
      (((Work.FTS.PhiStar.Series.continuous_eFam m).measurable.comp measurable_snd).aemeasurable)
  refine ⟨?_, ?_, ?_⟩
  · -- 1. the truncated angular energy, as a function of `z`
    intro N
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.sEta p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      refine ((hTrunc N).pow_const 2 |>.mul ?_ |>.mul ?_).ennreal_ofReal
      · exact ((CmpSupp.measurable_w.comp measurable_fst).aemeasurable).pow_const 2
      · exact (CmpSupp.measurable_sEta.comp measurable_snd).aemeasurable
    exact h1.lintegral_prod_right
  · -- 2. the angular level-`0` density, for fixed `z ∈ Iz`
    intro z _
    have hz' : AEMeasurable (fun θ : ℝ => Work.FTS.PhiStar.Series.psiSeries α F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h : AEMeasurable (fun θ : ℝ => ∑' m : ℕ,
          Work.FTS.PhiStar.Series.acoeff α m F z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine AEMeasurable.tsum (fun m => ?_)
        exact ((continuous_const.mul
          (Work.FTS.PhiStar.Series.continuous_eFam m)).measurable).aemeasurable
      exact h
    have heq : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
        = (fun θ : ℝ => ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) := by
      funext θ; rw [hzero]
    rw [heq]
    exact ((hz'.mul ((measurable_const.div
      (CmpSupp.measurable_sin_rpow_half.comp measurable_id)).aemeasurable)).pow_const 2).ennreal_ofReal
  · -- 3. the `z`-integral of the level-`0` density, on `(0,∞)`
    have hacm' : ∀ m : ℕ, AEMeasurable
        (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      intro m
      refine (hacm m).mono_measure ?_
      refine MeasureTheory.Measure.restrict_mono_set volume ?_
      intro z hz
      exact le_of_lt (show (0 : ℝ) < z from hz)
    have hfac : AEMeasurable (fun p : ℝ × ℝ =>
        Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((CmpSupp.measurable_w.comp measurable_fst).aemeasurable).div
        ((CmpSupp.measurable_sin_rpow_half.comp measurable_snd).aemeasurable)
    have hJ : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) p.1 p.2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have heq : (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (Work.FTS.PhiStar.Series.psiSeries α F) p.1 p.2))
          = (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F p.1 p.2
              * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)) := by
        funext p; rw [hzero]
      rw [heq]
      exact (((CmpSupp.aemeasurable_psiSeries_uncurry hacm').mul hfac).pow_const 2).ennreal_ofReal
    exact hJ.lintegral_prod_right

end Work.FTS.ClassCHon
