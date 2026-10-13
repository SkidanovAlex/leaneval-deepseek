import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.ClassC.lintegral_psiSeries_le_of_trunc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp

open MeasureTheory Set

/-! ## Measurability of the building blocks of the level-`0` energy

The three conjuncts of `meas_bundle` only ask for (a.e.) measurability of the truncated angular
energy, of the angular density of the level-`0` energy of `psiSeries`, and of the
corresponding `z`-integral.  Since `HkIntegrand α 0 f` involves only the single term
`(f · w / sin(2θ)^{η/2})²`, everything reduces to the joint (a.e.) measurability of the mode
series, which is a `tsum` of products of an `z`-measurable coefficient with a continuous
angular eigenfunction (`AEMeasurable.tsum`). -/

/-- At `k = 0` the `H^k`-integrand is the single weighted `L²`-term: all the mixed slots carry
the (impossible) condition `1 ≤ i` with `i ≤ k = 0`. -/
theorem hkIntegrand_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ
      = (Work.FTS.PhiStar.Series.psiSeries α F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The radial weight `w` is measurable (it is a totalised quotient of polynomials). -/
theorem measurable_w : Measurable Work.Spaces.w := by
  unfold Work.Spaces.w
  fun_prop

/-- The angular weight `sin(2θ)^{η/2}` appearing in the level-`0` energy is measurable. -/
theorem measurable_sin_rpow_half :
    Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
  (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- The angular weight `sin(2θ)^{-η}` is measurable (the file `StraightDefs` only gives the
definition; the measurability is recorded here for use in the product argument). -/
theorem measurable_sEta : Measurable Work.FTS.EllipticEst.sEta :=
  Work.FTS.ClassC.lplst_sEta_measurable

/-- **Joint measurability of the mode series.**  If every radial coefficient `acoeff α m F` is
a.e. measurable on `volume.restrict S`, then the mode series `psiSeries α F` is jointly a.e.
measurable on the product `(volume.restrict S) × (volume.restrict Iθ)`.  This is
`AEMeasurable.tsum` applied to the family `p ↦ acoeff α m F p.1 · eFam m p.2`, whose members are
products of an a.e. measurable function of the first variable with a continuous function of the
second. -/
theorem aemeasurable_psiSeries_uncurry {α : ℝ} {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hacm : ∀ m : ℕ, AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
      (MeasureTheory.volume.restrict S)) :
    AEMeasurable (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiSeries α F p.1 p.2)
      ((MeasureTheory.volume.restrict S).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h : AEMeasurable (fun p : ℝ × ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.acoeff α m F p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      ((MeasureTheory.volume.restrict S).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine AEMeasurable.tsum (fun m => ?_)
    exact ((hacm m).comp_fst).mul
      (((Work.FTS.PhiStar.Series.continuous_eFam m).measurable.comp measurable_snd).aemeasurable)
  exact h

theorem meas_bundle {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0)
    (hacm : ∀ m : ℕ, AEMeasurable
        (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    ∧ (∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- The analytic hypotheses (`hα`, `hα1`, `horth`, `hsm`, `hL2`) belong to the interface of the
  -- comparison/honesty argument; a.e. measurability of the mode series uses none of them (the
  -- only input is `hacm`, the a.e. measurability of the radial coefficients).  They are recorded
  -- here so that the proof mentions the full interface explicitly.
  have _hα : 0 < α := hα
  have _hac : α ≤ 1 := hα1
  have _hort : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0 := horth
  have _hsm : Work.FTS.EllipticEst.SmoothOpen F := hsm
  have _hL : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 := hL2
  have hzero : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ
      = (Work.FTS.PhiStar.Series.psiSeries α F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun z θ => hkIntegrand_zero α F z θ
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
      · exact ((measurable_w.comp measurable_fst).aemeasurable).pow_const 2
      · exact (measurable_sEta.comp measurable_snd).aemeasurable
    exact h1.lintegral_prod_right
  · -- 2. the angular level-`0` density, for fixed `z ∈ Iz`
    intro z hz
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
      (measurable_sin_rpow_half.comp measurable_id)).aemeasurable)).pow_const 2).ennreal_ofReal
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
      ((measurable_w.comp measurable_fst).aemeasurable).div
        ((measurable_sin_rpow_half.comp measurable_snd).aemeasurable)
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
      exact (((aemeasurable_psiSeries_uncurry hacm').mul hfac).pow_const 2).ennreal_ofReal
    exact hJ.lintegral_prod_right

end Work.FTS.ClassCHon.CmpSupp
