import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.meas_bundle =====
section

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


end Work.FTS.ClassCHon.CmpSupp
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassAux.integrable_prod_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Product integrability of `2 F ∂_z F · sin(2θ)^{-η}`

This is the Fubini ingredient of the continuity proof for the angular slice mass
`m F z = ∫_θ (F z θ)² sin(2θ)^{-η}` of `Work.FTS.ClassCHon.sliceMass_continuous`.

For `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, with both `F` and its weighted
radial derivative `z ∂_z F` in `ℋ⁰` (`Work.Spaces.HkMem α 0`), the function

`(z,θ) ↦ 2 F z θ ∂_zF z θ · sin(2θ)^{-η}`

is integrable for the product of the restrictions of Lebesgue measure to `Iz = [0,∞)` and
`Iθ = [0,π/2]`.

**Proof.** At `k = 0` the `ℋ`-integrand collapses to a single square,
`HkIntegrand α 0 G z θ = (G z θ · w z / sin(2θ)^{η/2})²`, and `HkMem α 0 G` is exactly the
integrability of `HkIntegrand α 0 G` (first over `θ` for every `z ∈ Iz`, then over `z`), hence,
by Tonelli (`Work.Spaces.integrable_prod_of_iterated`), the *product* integrability of
`HkIntegrand α 0 G` for `G = F` and for `G = z ∂_z F` (the smoothness on the open quadrant gives
a.e. strong measurability of the uncurried integrand, `Work.Spaces.aesm_of_continuousOn_Qd`).

The pointwise AM–GM estimate is
`2 |F ∂_zF| sEta ≤ HkIntegrand α 0 F + HkIntegrand α 0 (z ∂_z F)`:
with `s = sin(2θ) ≥ 0`, `w = w z` and `r = w/s^{η/2}` one has `r² = w² sEta` and
`(z r)² = (z w)² sEta`, while `w ≥ 1` and `z w ≥ (1+z)²/z ≥ 1` for `z > 0`; hence
`sEta ≤ r²` and `sEta ≤ (z r)²`, and `2|F ∂_zF| ≤ F² + (∂_zF)²` finishes the comparison.
The estimate holds a.e. in `z` (only `z = 0` is exceptional, where `w 0 = 0` kills both
`Hk`-integrands), and the domination is transferred with `MeasureTheory.Integrable.mono'`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.SliceMassAux

set_option maxHeartbeats 800000

/-! ## Elementary pointwise facts -/

/-- At `k = 0` the `ℋ`-integrand collapses to the single square
`(G z θ · w z / sin(2θ)^{η/2})²` (the mixed-derivative double sum is empty). -/
private lemma HkIntegrand_zero_eq (α : ℝ) (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 G z θ
      = (G z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The weight `sEta θ = sin(2θ)^{-η}` is continuous on the open quadrant (as a function of the
second variable). -/
private lemma continuousOn_sEta_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
    funext p; rfl
  rw [hfun]
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- `(sin(2θ)^{-η/2})² = sEta θ` on `Iθ`. -/
private lemma sq_sin_rpow_half_eta {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = Work.FTS.EllipticEst.sEta θ := by
  have hs_nn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast, ← Real.rpow_mul hs_nn]
  congr 1
  push_cast
  ring

/-- The square of the angular factor `w/s^{η/2}` is `w² sEta` (on `Iθ`). -/
private lemma sq_wdiv_eq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs_nn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [div_eq_mul_inv, ← Real.rpow_neg hs_nn (Work.Spaces.eta / 2), mul_pow]
  rw [sq_sin_rpow_half_eta hθ]

/-- `w z ≥ 1` for `z > 0` (so that `w z / sin(2θ)^{η/2} ≥ 1` on the open quadrant). -/
private lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
  exact one_le_pow₀ hw

/-- `z · w z ≥ 1` for `z > 0` (so that the radial factor in the weighted derivative of the
`ℋ⁰`-integrand of `z ∂_z F` beats `1/s^{η/2}`). -/
private lemma one_le_zw_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (z * Work.Spaces.w z) ^ 2 :=
  one_le_pow₀ (Work.Spaces.one_le_mul_w z hz)

/-! ## The pointwise AM–GM estimate -/

/-- **Pointwise domination.**  For `z > 0` and `θ ∈ Iθ`,
`2 |F ∂_zF| sEta ≤ HkIntegrand α 0 F + HkIntegrand α 0 (z ∂_z F)`.

Indeed `HkIntegrand α 0 F = (F w/s^{η/2})²` and `HkIntegrand α 0 (z∂_zF) = (z∂_zF · w/s^{η/2})²`,
and on `Iθ` the angular factor `w/s^{η/2}` has square `w² sEta`, with `w² ≥ 1` and
`(z w)² ≥ 1` for `z > 0`. -/
private lemma key_pointwise {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |2 * F z θ * Work.Spaces.pz F z θ * Work.FTS.EllipticEst.sEta θ|
      ≤ Work.Spaces.HkIntegrand α 0 F z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ := by
  have hsEta_nn : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _
  have hle1 : Work.FTS.EllipticEst.sEta θ
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [sq_wdiv_eq hθ]
    exact le_mul_of_one_le_left hsEta_nn (one_le_w_sq hz)
  have hle2 : Work.FTS.EllipticEst.sEta θ
      ≤ (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have h : (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (z * Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [mul_pow, sq_wdiv_eq hθ]; ring
    rw [h]
    exact le_mul_of_one_le_left hsEta_nn (one_le_zw_sq hz)
  have hA : (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ (F z θ) ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hle1 (sq_nonneg _)
      _ = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  have hB : (Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ ((z * Work.Spaces.pz F z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ (Work.Spaces.pz F z θ) ^ 2
            * (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_left hle2 (sq_nonneg _)
      _ = ((z * Work.Spaces.pz F z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  have hamgm : 2 * |F z θ * Work.Spaces.pz F z θ|
      ≤ (F z θ) ^ 2 + (Work.Spaces.pz F z θ) ^ 2 := by
    rw [abs_mul, ← sq_abs (F z θ), ← sq_abs (Work.Spaces.pz F z θ)]
    nlinarith [sq_nonneg (|F z θ| - |Work.Spaces.pz F z θ|)]
  have habs : |2 * F z θ * Work.Spaces.pz F z θ * Work.FTS.EllipticEst.sEta θ|
      = 2 * |F z θ * Work.Spaces.pz F z θ| * Work.FTS.EllipticEst.sEta θ := by
    simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hsEta_nn]
    ring
  calc |2 * F z θ * Work.Spaces.pz F z θ * Work.FTS.EllipticEst.sEta θ|
      = 2 * |F z θ * Work.Spaces.pz F z θ| * Work.FTS.EllipticEst.sEta θ := habs
    _ ≤ ((F z θ) ^ 2 + (Work.Spaces.pz F z θ) ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_right hamgm hsEta_nn
    _ = (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by ring
    _ ≤ (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + ((z * Work.Spaces.pz F z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := add_le_add hA hB
    _ = Work.Spaces.HkIntegrand α 0 F z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ := by
        simp only [Work.Spaces.HkIntegrand]
        norm_num

/-! ## Product integrability of the `ℋ⁰`-integrand -/

/-- **Tonelli for the level-`0` `ℋ`-integrand.**  If `G ∈ C^∞` on the open quadrant and
`HkMem α 0 G`, then the uncurried `HkIntegrand α 0 G` is integrable for the product measure. -/
private lemma integrable_prod_HkIntegrand_zero {α : ℝ} {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) (h : Work.Spaces.HkMem α 0 G) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α 0 G z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α 0)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 G z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact h.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 G z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := h.2
  exact (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α 0 G z θ) haesm hslice houter).1

/-! ## The theorem -/

theorem integrable_prod_mixed {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (h0 : Work.Spaces.HkMem α 0 F)
    (h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the two dominating `ℋ⁰`-integrands are product integrable
  have hA : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 F p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_prod_HkIntegrand_zero hsm h0
  have hB : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ)
        p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_prod_HkIntegrand_zero hsm.Dz h1
  -- a.e. strong measurability of the target, from continuity on the open quadrant
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn
    have hPc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.pz.continuousOn
    have hmain : ContinuousOn (fun p : ℝ × ℝ => 2 * F p.1 p.2 * Work.Spaces.pz F p.1 p.2
        * Work.FTS.EllipticEst.sEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hmain' : ContinuousOn ((((fun _ : ℝ × ℝ => (2 : ℝ)) * (fun p : ℝ × ℝ => F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        ((continuousOn_const.mul hFc).mul hPc).mul continuousOn_sEta_snd
      have hfun : ((((fun _ : ℝ × ℝ => (2 : ℝ)) * (fun p : ℝ × ℝ => F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2))
          = (fun p : ℝ × ℝ => 2 * F p.1 p.2 * Work.Spaces.pz F p.1 p.2
              * Work.FTS.EllipticEst.sEta p.2) := by
        funext p
        simp only [Pi.mul_apply]
      rwa [hfun] at hmain'
    have hgoal : (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ))
        = (fun p : ℝ × ℝ => 2 * F p.1 p.2 * Work.Spaces.pz F p.1 p.2
            * Work.FTS.EllipticEst.sEta p.2) := rfl
    rw [hgoal]
    exact hmain
  refine MeasureTheory.Integrable.mono' (hA.add hB) haesm ?_
  -- the pointwise domination holds almost everywhere (only `z = 0` is exceptional)
  have hz_ae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
    have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
      rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem (s := {p : ℝ × ℝ | 0 < p.1}) ?_).mpr ?_
    · exact (isOpen_Ioi.preimage continuous_fst).measurableSet
    · filter_upwards [hpos] with z hz
      exact Filter.Eventually.of_forall (fun θ => hz)
  have hθ_ae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : ℝ × ℝ | p.2 ∈ Work.Spaces.Iθ}) ?_).mpr ?_
    · exact measurableSet_Icc.preimage measurable_snd
    · exact Filter.Eventually.of_forall
        (fun _ => MeasureTheory.ae_restrict_mem measurableSet_Icc)
  filter_upwards [hz_ae, hθ_ae] with p hpz hpθ
  simpa only [Function.uncurry, Real.norm_eq_abs, Pi.add_apply] using
    key_pointwise (α := α) (F := F) hpz hpθ

end Work.FTS.ClassCHon.SliceMassAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.InterpTrace

set_option autoImplicit false
-- `hχ` is part of the (fixed) statement but is not needed: the bridge only uses the support
-- window `cA k ≤ cB k` of the cut-off, together with `0 < cA k`.
set_option linter.unusedVariables false

open MeasureTheory Set

theorem bridge_Iz_interval {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) (F : ℝ → ℝ)
    (hzero : ∀ z : ℝ, 0 < z → (z < Work.FTS.EllSol.PkgK5.cA k ∨ Work.FTS.EllSol.PkgK5.cB k < z) → F z = 0) :
    (∫ z in Work.Spaces.Iz, F z) = ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k), F z := by
  have ha : 0 < Work.FTS.EllSol.PkgK5.cA k := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- `[0,∞)` and `(0,∞)` differ by the null set `{0}`
  have h1 : (∫ z in Work.Spaces.Iz, F z) = ∫ z in Set.Ioi 0, F z := by
    rw [Work.Spaces.Iz]
    exact integral_Ici_eq_integral_Ioi
  -- `F` vanishes a.e. on `(0,∞) \ [cA k, cB k]`
  have h2 : (∫ z in Set.Ioi 0, F z) = ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k)
      (Work.FTS.EllSol.PkgK5.cB k), F z :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1, ha])
      (fun x hx => by
        have hx2 : x < Work.FTS.EllSol.PkgK5.cA k ∨ Work.FTS.EllSol.PkgK5.cB k < x := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hx.2
        exact hzero x hx.1 hx2)
  rw [h1, h2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

end Work.FTS.EllSol.PkgK5.InterpTrace
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.InterpTrace.continuousOn_mK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.InterpTrace

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The generic parameter-continuity lemma -/

/-- **Continuity in the parameter of an interval integral.**  If `F` is jointly continuous on the
open quadrant and `0 < a`, `a ≤ b`, then `θ ↦ ∫ z in a..b, F z θ` is continuous (within the open
interval `(0,π/2)`) at every interior point `θ₀`. -/
theorem continuousWithinAt_intervalIntegral_of_continuousOn
    {F : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousWithinAt (fun θ => ∫ z in a..b, F z θ) (Set.Ioo 0 (π / 2)) θ₀ := by
  -- a symmetric inner interval around `θ₀` contained in `(0,π/2)`
  set δ : ℝ := min θ₀ (π / 2 - θ₀) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : 0 < min θ₀ (π / 2 - θ₀) := lt_min hθ₀.1 (by linarith [hθ₀.2])
    linarith
  have hδ₁ : 2 * δ ≤ θ₀ := by
    rw [hδdef]; have := min_le_left θ₀ (π / 2 - θ₀); linarith
  have hδ₂ : 2 * δ ≤ π / 2 - θ₀ := by
    rw [hδdef]; have := min_le_right θ₀ (π / 2 - θ₀); linarith
  have hsub : Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ Set.Ioo 0 (π / 2) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- the compact rectangle
  set B : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (θ₀ - δ) (θ₀ + δ) with hBdef
  have hBsub : B ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    have hp1' : a ≤ p.1 := (Set.mem_Icc.mp hp1).1
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (lt_of_lt_of_le ha hp1'), hsub hp2⟩
  have hFB : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) B := hF.mono hBsub
  have hcomp : IsCompact B := isCompact_Icc.prod isCompact_Icc
  -- a uniform bound for the integrand on the rectangle
  set M : ℝ := sSup ((fun p : ℝ × ℝ => |F p.1 p.2|) '' B) with hMdef
  have hbdd : BddAbove ((fun p : ℝ × ℝ => |F p.1 p.2|) '' B) :=
    hcomp.bddAbove_image hFB.abs
  have hM : ∀ p ∈ B, |F p.1 p.2| ≤ M := fun p hp => le_csSup hbdd ⟨p, hp, rfl⟩
  -- the neighbourhood of `θ₀` on which both the bound and the measurability hold
  have hnbhd : ∀ᶠ θ in 𝓝[Set.Ioo 0 (π / 2)] θ₀, θ ∈ Set.Ioo (θ₀ - δ) (θ₀ + δ) :=
    Filter.mem_of_superset
      (nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩))
      (fun θ hθ => hθ)
  have hmemIcc : ∀ θ ∈ Set.Ioo (θ₀ - δ) (θ₀ + δ), θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ) :=
    fun θ hθ => Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hF_meas : ∀ᶠ θ in 𝓝[Set.Ioo 0 (π / 2)] θ₀,
      AEStronglyMeasurable (fun z => F z θ) (volume.restrict (Ι a b)) := by
    refine hnbhd.mono fun θ hθ => ?_
    rw [Set.uIoc_of_le hab]
    have hslice : ContinuousOn (fun z : ℝ => F z θ) (Set.Ioc a b) :=
      hFB.comp' (continuousOn_id.prodMk continuousOn_const)
        (fun z hz => Set.mem_prod.mpr
          ⟨Set.mem_Icc.mpr ⟨le_of_lt hz.1, hz.2⟩, hmemIcc θ hθ⟩)
    exact hslice.aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᶠ θ in 𝓝[Set.Ioo 0 (π / 2)] θ₀,
      ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Ι a b → ‖F z θ‖ ≤ M := by
    refine hnbhd.mono fun θ hθ => ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    rw [Set.uIoc_of_le hab] at hz
    rw [Real.norm_eq_abs]
    exact hM (z, θ) (Set.mem_prod.mpr
      ⟨Set.mem_Icc.mpr ⟨le_of_lt hz.1, hz.2⟩, hmemIcc θ hθ⟩)
  have h_cont : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Ι a b →
      ContinuousWithinAt (fun θ => F z θ) (Set.Ioo 0 (π / 2)) θ₀ := by
    refine Filter.Eventually.of_forall fun z hz => ?_
    rw [Set.uIoc_of_le hab] at hz
    have hzpos : 0 < z := lt_of_lt_of_le ha (le_of_lt hz.1)
    have hmem : (z, θ₀) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) :=
      Set.mem_prod.mpr ⟨hzpos, hθ₀⟩
    have hcontAt : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (z, θ₀) :=
      hF.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
    have : ContinuousAt (fun θ => F z θ) θ₀ :=
      hcontAt.comp (f := fun θ : ℝ => (z, θ)) (by fun_prop)
    exact this.continuousWithinAt
  exact intervalIntegral.continuousWithinAt_of_dominated_interval hF_meas h_bound
    intervalIntegrable_const h_cont

/-! ## The weighted cut-off factor `χ k z * w z ^ 2` -/

theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw : ContinuousOn (Work.Spaces.w) (Set.Ioi 0) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact hw.pow 2

theorem continuousOn_cutweight {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hχc : ContinuousOn (χ k) (Set.Ioi 0) := (hχ.sm k).continuousOn
  have hχQ : ContinuousOn (fun p : ℝ × ℝ => χ k p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hχc.comp' continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  have hwQ : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_w_sq.comp' continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  exact hχQ.mul hwQ

/-! ## The main statement -/

theorem continuousOn_mK {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    (k : ℕ) {ψ : ℝ → ℝ → ℝ} (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) :
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pthIter 2 ψ z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) with hQdef
  have ha : 0 < Work.FTS.EllSol.PkgK5.cA k := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- the weighted cut-off factor
  have hχw : ContinuousOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2) Q :=
    continuousOn_cutweight hχ k
  -- the smooth factors
  have hψQ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) Q := hψ.continuousOn
  have hψpthQ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.1 p.2) Q :=
    hψ.pth.continuousOn
  have hψ2Q : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 ψ p.1 p.2) Q := by
    have h : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 ψ) := by
      have := hψ.pth.pth
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using this
    exact h.continuousOn
  -- the four joint-continuity facts, in the exact shapes appearing in the statement
  have J1 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * ψ p.1 p.2 ^ 2) Q :=
    hχw.mul (hψQ.pow 2)
  have J2 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * ψ p.1 p.2 * Work.Spaces.pth ψ p.1 p.2) Q :=
    (hχw.mul hψQ).mul hψpthQ
  have J3 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2) Q :=
    hχw.mul (hψpthQ.pow 2)
  have J4 : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * ψ p.1 p.2 * Work.Spaces.pthIter 2 ψ p.1 p.2) Q :=
    (hχw.mul hψQ).mul hψ2Q
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J1 hθ₀
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J2 hθ₀
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J3 hθ₀
  · exact fun θ₀ hθ₀ =>
      continuousWithinAt_intervalIntegral_of_continuousOn ha hab J4 hθ₀

end Work.FTS.EllSol.PkgK5.InterpTrace
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.InterpTrace.cs_mK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllSol.PkgK5.InterpTrace

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Cauchy–Schwarz, discriminant form.**  If the quadratic `t ↦ A + 2*C*t + B*t^2` is
nonnegative for every real `t` and `B ≥ 0`, then `C^2 ≤ A*B`.  (The degenerate case `B = 0`
is handled separately: a nonnegative *linear* function `t ↦ A + 2Ct` forces `C = 0`.) -/
private theorem csQuad_aux {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * C * t + B * t ^ 2)
    (hB : 0 ≤ B) : C ^ 2 ≤ A * B := by
  by_cases hB0 : B = 0
  · have hC : C = 0 := by
      by_contra hC0
      have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero (by norm_num) hC0
      have hk := h (-(A + 1) / (2 * C))
      have hval : A + 2 * C * (-(A + 1) / (2 * C)) + B * (-(A + 1) / (2 * C)) ^ 2 = -1 := by
        rw [hB0]
        field_simp
        ring
      rw [hval] at hk
      norm_num at hk
    rw [hC, hB0]
    norm_num
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hkey := h (-(C / B))
    have hval : A + 2 * C * (-(C / B)) + B * (-(C / B)) ^ 2 = A - C ^ 2 / B := by
      field_simp
      ring
    rw [hval] at hkey
    have hle : C ^ 2 / B ≤ A := by linarith
    have heq : C ^ 2 = (C ^ 2 / B) * B := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hle hB

/-- The radial weight `w z = (1+z)^2/z^2` has a continuous square on `(0,∞)`. -/
private theorem continuousOn_w_sq_aux :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw : ContinuousOn (Work.Spaces.w) (Set.Ioi 0) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact hw.pow 2

/-- **Weighted Cauchy–Schwarz on an interval.**  For `a ≤ b`, a weight `ρ ≥ 0` on `(a,b]` and
`ρ u²`, `ρ v²`, `ρ u v` integrable on `(a,b]`,
`(∫_a^b ρ u v)² ≤ (∫_a^b ρ u²) * (∫_a^b ρ v²)`.

The proof integrates the pointwise identity
`ρ(u + t v)² = ρ u² + 2t·ρ u v + t²·ρ v²`, observes that the result is nonnegative (the weight is
nonnegative on `(a,b]`), and applies the discriminant lemma `csQuad_aux`. -/
private theorem cs_interval_weighted_aux {a b : ℝ} (hab : a ≤ b) {ρ u v : ℝ → ℝ}
    (hρ : ∀ x ∈ Set.Ioc a b, 0 ≤ ρ x)
    (h1 : IntegrableOn (fun x => ρ x * u x ^ 2) (Set.Ioc a b))
    (h2 : IntegrableOn (fun x => ρ x * v x ^ 2) (Set.Ioc a b))
    (h3 : IntegrableOn (fun x => ρ x * u x * v x) (Set.Ioc a b)) :
    (∫ x in a..b, ρ x * u x * v x) ^ 2 ≤
      (∫ x in a..b, ρ x * u x ^ 2) * (∫ x in a..b, ρ x * v x ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  have hB0 : 0 ≤ ∫ x in Set.Ioc a b, ρ x * v x ^ 2 :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun x hx => mul_nonneg (hρ x hx) (sq_nonneg (v x))))
  refine csQuad_aux ?_ hB0
  intro t
  have hpoly : (∫ x in Set.Ioc a b, ρ x * (u x + t * v x) ^ 2)
      = (∫ x in Set.Ioc a b, ρ x * u x ^ 2)
        + 2 * (∫ x in Set.Ioc a b, ρ x * u x * v x) * t
        + (∫ x in Set.Ioc a b, ρ x * v x ^ 2) * t ^ 2 := by
    have hmid : Integrable (fun x => (2 * t) * (ρ x * u x * v x))
        (volume.restrict (Set.Ioc a b)) := h3.const_mul (2 * t)
    have hlast : Integrable (fun x => t ^ 2 * (ρ x * v x ^ 2))
        (volume.restrict (Set.Ioc a b)) := h2.const_mul (t ^ 2)
    have hsum : Integrable (fun x => ρ x * u x ^ 2 + (2 * t) * (ρ x * u x * v x))
        (volume.restrict (Set.Ioc a b)) := h1.add hmid
    rw [show (fun x => ρ x * (u x + t * v x) ^ 2)
        = (fun x => ρ x * u x ^ 2 + (2 * t) * (ρ x * u x * v x) + t ^ 2 * (ρ x * v x ^ 2))
        from funext (fun x => by ring)]
    rw [integral_add hsum hlast, integral_add h1 hmid, integral_const_mul, integral_const_mul]
    ring
  rw [← hpoly]
  exact integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc
    (fun x hx => mul_nonneg (hρ x hx) (sq_nonneg (u x + t * v x))))

theorem cs_mK {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    (k : ℕ) {ψ : ℝ → ℝ → ℝ} (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ) ^ 2
      ≤ (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ) ^ 2) := by
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  set s : Set ℝ := Set.uIcc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) with hs
  have hsub : s ⊆ Set.Ioi 0 := by
    intro x hx
    rw [hs, Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hx.1
  have hχc : ContinuousOn (χ k) s := (hχ.sm k).continuousOn.mono hsub
  have hwc : ContinuousOn (fun x : ℝ => (Work.Spaces.w x) ^ 2) s :=
    continuousOn_w_sq_aux.mono hsub
  have hψc : ContinuousOn (fun x : ℝ => ψ x θ) s := (hψ.curry_z hθ).continuousOn.mono hsub
  have hpc : ContinuousOn (fun x : ℝ => Work.Spaces.pth ψ x θ) s :=
    ((hψ.pth).curry_z hθ).continuousOn.mono hsub
  have key : ∀ f : ℝ → ℝ, ContinuousOn f s →
      IntegrableOn f (Set.Ioc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)) :=
    fun f hf => (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf.intervalIntegrable
  refine cs_interval_weighted_aux hab
    (ρ := fun z => χ k z * (Work.Spaces.w z) ^ 2) (u := fun z => ψ z θ)
    (v := fun z => Work.Spaces.pth ψ z θ) ?_ ?_ ?_ ?_
  · intro x hx
    exact mul_nonneg
      (hχ.bnd k x (lt_trans (Work.FTS.EllSol.PkgK5.cA_pos k) hx.1)).1 (sq_nonneg _)
  · exact key _ ((hχc.mul hwc).mul (hψc.pow 2))
  · exact key _ ((hχc.mul hwc).mul (hpc.pow 2))
  · exact key _ (((hχc.mul hwc).mul hψc).mul hpc)

end Work.FTS.EllSol.PkgK5.InterpTrace
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.InterpTrace

set_option maxHeartbeats 800000

theorem mK_hasDerivAt {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (2 * ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀) θ₀ := by
  let a : ℝ := Work.FTS.EllSol.PkgK5.cA k
  let b : ℝ := Work.FTS.EllSol.PkgK5.cB k
  change HasDerivAt (fun θ => ∫ z in a..b, χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (2 * ∫ z in a..b, χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀) θ₀
  have ha : 0 < a := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : a ≤ b := Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- a small symmetric neighbourhood `s` of `θ₀` inside `(0,π/2)`
  let ε : ℝ := min (θ₀ / 2) ((Real.pi / 2 - θ₀) / 2)
  have hεpos : 0 < ε := lt_min (by linarith [hθ₀.1]) (by linarith [hθ₀.2, Real.pi_pos])
  have hεle1 : ε ≤ θ₀ / 2 := min_le_left _ _
  have hεle2 : ε ≤ (Real.pi / 2 - θ₀) / 2 := min_le_right _ _
  have hθ₀mε : 0 < θ₀ - ε := by linarith
  have hθ₀pε : θ₀ + ε < Real.pi / 2 := by linarith
  let s : Set ℝ := Set.Icc (θ₀ - ε) (θ₀ + ε)
  have hs : s ∈ 𝓝 θ₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hθ₀s : θ₀ ∈ s := ⟨by linarith, by linarith⟩
  have hs_sub : s ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have huIcc_sub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt_of_lt_of_le ha h1
    · exact lt_of_lt_of_le ha (le_trans hab h1)
  have hKQ0 : Set.uIcc a b ×ˢ s ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    exact ⟨huIcc_sub hz, hs_sub hx⟩
  -- the compact box on which the derivative integrand is bounded
  have hK : IsCompact (Set.uIcc a b ×ˢ s) := isCompact_uIcc.prod isCompact_Icc
  have hwc : ContinuousOn Work.Spaces.w (Set.Ioi (0:ℝ)) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      ((continuous_id.pow 2).continuousOn) (fun z hz => by
        simp only [Set.mem_Ioi] at hz
        positivity)
  have hχK : ContinuousOn (fun p : ℝ × ℝ => χ k p.1) (Set.uIcc a b ×ˢ s) :=
    ((hχ.sm k).continuousOn).comp continuousOn_fst (fun p hp => huIcc_sub hp.1)
  have hwK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.uIcc a b ×ˢ s) :=
    hwc.comp continuousOn_fst (fun p hp => huIcc_sub hp.1)
  have hψK : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (Set.uIcc a b ×ˢ s) :=
    hψ.continuousOn.mono hKQ0
  have hpthK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.1 p.2) (Set.uIcc a b ×ˢ s) :=
    (hψ.pth).continuousOn.mono hKQ0
  have hG : ContinuousOn (fun p : ℝ × ℝ =>
      χ k p.1 * (Work.Spaces.w p.1) ^ 2 * (2 * ψ p.1 p.2 * Work.Spaces.pth ψ p.1 p.2))
      (Set.uIcc a b ×ˢ s) :=
    (hχK.mul (hwK.pow 2)).mul ((continuousOn_const.mul hψK).mul hpthK)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG
  -- the parametric family and its formal `θ`-derivative
  let F : ℝ → ℝ → ℝ := fun θ z => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2
  let F' : ℝ → ℝ → ℝ := fun θ z =>
    χ k z * (Work.Spaces.w z) ^ 2 * (2 * ψ z θ * Work.Spaces.pth ψ z θ)
  have hslice_cont : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      ContinuousOn (fun z => F x z) (Set.uIcc a b) := by
    intro x hx
    show ContinuousOn (fun z => χ k z * (Work.Spaces.w z) ^ 2 * ψ z x ^ 2) (Set.uIcc a b)
    have hχ1 : ContinuousOn (χ k) (Set.uIcc a b) := ((hχ.sm k).continuousOn).mono huIcc_sub
    have hw1 : ContinuousOn Work.Spaces.w (Set.uIcc a b) := hwc.mono huIcc_sub
    have hψx : ContinuousOn (fun z => ψ z x) (Set.uIcc a b) :=
      ((hψ.curry_z hx).continuousOn).mono huIcc_sub
    exact (hχ1.mul (hw1.pow 2)).mul (hψx.pow 2)
  have hF_meas : ∀ᶠ x in 𝓝 θ₀,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hs] with x hx
    exact ((hslice_cont x (hs_sub hx)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  have hF_int : IntervalIntegrable (F θ₀) volume a b :=
    (hslice_cont θ₀ hθ₀).intervalIntegrable
  have hpthθ₀ : ContinuousOn (fun z => Work.Spaces.pth ψ z θ₀) (Set.uIcc a b) :=
    ((hψ.pth).curry_z hθ₀).continuousOn.mono huIcc_sub
  have hF'_meas : AEStronglyMeasurable (F' θ₀) (volume.restrict (Set.uIoc a b)) := by
    have hχ1 : ContinuousOn (χ k) (Set.uIcc a b) := ((hχ.sm k).continuousOn).mono huIcc_sub
    have hw1 : ContinuousOn Work.Spaces.w (Set.uIcc a b) := hwc.mono huIcc_sub
    have hψθ₀ : ContinuousOn (fun z => ψ z θ₀) (Set.uIcc a b) :=
      ((hψ.curry_z hθ₀).continuousOn).mono huIcc_sub
    have hcont : ContinuousOn (fun z => F' θ₀ z) (Set.uIcc a b) := by
      show ContinuousOn (fun z => χ k z * (Work.Spaces.w z) ^ 2 *
        (2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀)) (Set.uIcc a b)
      exact (hχ1.mul (hw1.pow 2)).mul ((continuousOn_const.mul hψθ₀).mul hpthθ₀)
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Set.uIoc a b →
      ∀ x ∈ s, ‖F' x z‖ ≤ (fun _ : ℝ => C) z := by
    refine Filter.Eventually.of_forall fun z hz x hx => ?_
    have hzK : z ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hz
    have h := hC (z, x) ⟨hzK, hx⟩
    simpa [F'] using h
  have h_diff : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Set.uIoc a b →
      ∀ x ∈ s, HasDerivAt (fun x => F x z) (F' x z) x := by
    refine Filter.Eventually.of_forall fun z hz x hx => ?_
    have hzpos : 0 < z := huIcc_sub (Set.uIoc_subset_uIcc hz)
    have hxIoo : x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := hs_sub hx
    have hd : HasDerivAt (fun θ => ψ z θ) (Work.Spaces.pth ψ z x) x := by
      have hcda : ContDiffAt ℝ Work.Stability.smoothOrder (fun θ => ψ z θ) x :=
        (hψ.curry_θ hzpos).contDiffAt (isOpen_Ioo.mem_nhds hxIoo)
      simpa only [Work.Spaces.pth] using
        (hcda.differentiableAt (by simp [Work.Stability.smoothOrder])).hasDerivAt
    have h1 : HasDerivAt (fun θ => ψ z θ ^ 2) (2 * ψ z x * Work.Spaces.pth ψ z x) x := by
      have hp : HasDerivAt ((fun θ => ψ z θ) ^ 2)
          (↑2 * ψ z x ^ (2 - 1) * Work.Spaces.pth ψ z x) x := hd.pow 2
      have heq : (fun θ => ψ z θ ^ 2) = ((fun θ => ψ z θ) ^ 2) := by
        funext θ; simp
      rw [heq]
      convert hp using 1
      ring
    have h2 : HasDerivAt (fun θ => (χ k z * (Work.Spaces.w z) ^ 2) * ψ z θ ^ 2)
        ((χ k z * (Work.Spaces.w z) ^ 2) * (2 * ψ z x * Work.Spaces.pth ψ z x)) x :=
      h1.const_mul (χ k z * (Work.Spaces.w z) ^ 2)
    show HasDerivAt (fun θ => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
        (χ k z * (Work.Spaces.w z) ^ 2 * (2 * ψ z x * Work.Spaces.pth ψ z x)) x
    exact h2
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := F) (F' := F') (bound := fun _ : ℝ => C)
    (x₀ := θ₀) (s := s)
    hs hF_meas hF_int hF'_meas h_bound (intervalIntegrable_const (c := C)) h_diff
  have hInt : (∫ z in a..b, F' θ₀ z)
      = 2 * ∫ z in a..b, χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀ := by
    have h2 : (2:ℝ) * ∫ z in a..b,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀
        = ∫ z in a..b,
            2 * (χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀) :=
      (intervalIntegral.integral_const_mul (μ := volume) (2:ℝ)
        (fun z => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pth ψ z θ₀)).symm
    rw [h2]
    refine intervalIntegral.integral_congr fun z hz => ?_
    simp only [F']
    ring
  rw [hInt] at hmain
  exact hmain

end Work.FTS.EllSol.PkgK5.InterpTrace
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.InterpTrace

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The radial weight `w²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq_Ioi : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2

/-- **Differentiation under the integral sign for the `m`-integrand.**

For a weight `c` continuous on `[a,b]` with `0 < a ≤ b`, and a datum `ψ` that is `C^∞` on the
open quadrant `(0,∞) × (0,π/2)`, the parametric integral
`θ ↦ ∫_a^b c z * ψ z θ * ∂_θψ z θ dz` is differentiable at `θ₀ ∈ (0,π/2)` with derivative
`∫_a^b c z (∂_θψ z θ₀)² dz + ∫_a^b c z ψ z θ₀ ∂_θ²ψ z θ₀ dz`. -/
theorem hasDerivAt_integral_mul_pth {c : ℝ → ℝ} {a b θ₀ : ℝ} {ψ : ℝ → ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn c (Set.uIcc a b))
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ => ∫ z in a..b, c z * ψ z θ * Work.Spaces.pth ψ z θ)
      ((∫ z in a..b, c z * (Work.Spaces.pth ψ z θ₀) ^ 2)
        + (∫ z in a..b, c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀)) θ₀ := by
  -- the open neighbourhood `(t₁,t₂) ∋ θ₀` and the open interval `(a,b)`
  set t₁ : ℝ := θ₀ / 2 with ht₁
  set t₂ : ℝ := (θ₀ + Real.pi / 2) / 2 with ht₂
  have hπ : 0 < Real.pi := Real.pi_pos
  have ht₁0 : 0 < t₁ := by rw [ht₁]; linarith [hθ₀.1]
  have ht₂π : t₂ < Real.pi / 2 := by rw [ht₂]; linarith [hθ₀.2]
  have hθ₀mem : θ₀ ∈ Set.Ioo t₁ t₂ :=
    ⟨by rw [ht₁]; linarith [hθ₀.1], by rw [ht₂]; linarith [hθ₀.2]⟩
  -- the interval endpoints lie in `(0,∞)`
  have hIocc : Set.uIoc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    have h1 : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le hab] at h1
    exact lt_of_lt_of_le ha h1.1
  -- slices of a smooth datum are continuous on the radial interval
  have sliceOf : ∀ {g : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen g →
      ∀ x ∈ Set.Ioo t₁ t₂, ContinuousOn (fun t : ℝ => g t x) (Set.uIcc a b) := by
    intro g hg x hx
    refine hg.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun t ht => ?_)
    have h1 : t ∈ Set.Icc a b := by rw [Set.uIcc_of_le hab] at ht; exact ht
    show (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
    exact ⟨lt_of_lt_of_le ha h1.1, lt_of_lt_of_le ht₁0 (le_of_lt hx.1), lt_trans hx.2 ht₂π⟩
  -- the integrand and its candidate `θ`-derivative
  set F : ℝ → ℝ → ℝ := fun x t => c t * ψ t x * Work.Spaces.pth ψ t x with hF
  set F' : ℝ → ℝ → ℝ := fun x t => c t * (Work.Spaces.pth ψ t x * Work.Spaces.pth ψ t x
    + ψ t x * Work.Spaces.pthIter 2 ψ t x) with hF'
  have hFcont : ∀ x ∈ Set.Ioo t₁ t₂, ContinuousOn (F x) (Set.uIcc a b) := by
    intro x hx
    change ContinuousOn (fun t : ℝ => c t * ψ t x * Work.Spaces.pth ψ t x) (Set.uIcc a b)
    exact (hc.mul (sliceOf hψ x hx)).mul (sliceOf hψ.pth x hx)
  have hF'cont : ∀ x ∈ Set.Ioo t₁ t₂, ContinuousOn (F' x) (Set.uIcc a b) := by
    intro x hx
    change ContinuousOn (fun t : ℝ => c t * (Work.Spaces.pth ψ t x * Work.Spaces.pth ψ t x
      + ψ t x * Work.Spaces.pthIter 2 ψ t x)) (Set.uIcc a b)
    exact hc.mul (((sliceOf hψ.pth x hx).mul (sliceOf hψ.pth x hx)).add
      ((sliceOf hψ x hx).mul (sliceOf ((hψ.pth).pth) x hx)))
  -- uniform bound for `F'` on the compact set `[t₁,t₂] × [a,b]`
  have hmemQ : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Set.uIcc a b,
      (p.2, p.1) ∈ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have h2 : p.2 ∈ Set.Icc a b := by rw [Set.uIcc_of_le hab] at hp2; exact hp2
    show (p.2, p.1) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
    exact ⟨lt_of_lt_of_le ha h2.1, lt_of_lt_of_le ht₁0 hp1.1, lt_of_le_of_lt hp1.2 ht₂π⟩
  have hbig : ContinuousOn (fun p : ℝ × ℝ =>
      c p.2 * (Work.Spaces.pth ψ p.2 p.1 * Work.Spaces.pth ψ p.2 p.1
        + ψ p.2 p.1 * Work.Spaces.pthIter 2 ψ p.2 p.1))
      (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) := by
    have hct : ContinuousOn (fun p : ℝ × ℝ => c p.2)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      hc.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hψ0 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2 p.1)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      hψ.continuousOn.comp continuous_swap.continuousOn hmemQ
    have hψ1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.2 p.1)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      hψ.pth.continuousOn.comp continuous_swap.continuousOn hmemQ
    have hψ2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 ψ p.2 p.1)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      ((hψ.pth).pth).continuousOn.comp continuous_swap.continuousOn hmemQ
    exact hct.mul ((hψ1.mul hψ1).add (hψ0.mul hψ2))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hbig
  -- the seven hypotheses of the dominated-convergence differentiation lemma
  have hmeas : ∀ᶠ x in 𝓝 θ₀,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ₀mem] with x hx
    exact (hFcont x hx).aestronglyMeasurable_of_subset_isCompact isCompact_uIcc
      measurableSet_uIoc Set.uIoc_subset_uIcc
  have hint : IntervalIntegrable (F θ₀) volume a b :=
    (hFcont θ₀ hθ₀mem).intervalIntegrable
  have hmeas' : AEStronglyMeasurable (F' θ₀) (volume.restrict (Set.uIoc a b)) :=
    (hF'cont θ₀ hθ₀mem).aestronglyMeasurable_of_subset_isCompact isCompact_uIcc
      measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo t₁ t₂,
      ‖F' x t‖ ≤ (fun _ : ℝ => max C 0) t := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have htu : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    have hmem : (x, t) ∈ Set.Icc t₁ t₂ ×ˢ Set.uIcc a b :=
      ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, htu⟩
    exact le_trans (hC (x, t) hmem) (le_max_left C 0)
  have hintb : IntervalIntegrable (fun _ : ℝ => max C 0) volume a b := intervalIntegrable_const
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo t₁ t₂,
      HasDerivAt (fun x => F x t) (F' x t) x := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have ht0 : 0 < t := by
      have h1 : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hab] at h1
      exact lt_of_lt_of_le ha h1.1
    have hxmem : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le ht₁0 (le_of_lt hx.1), lt_trans hx.2 ht₂π⟩
    have hd1 : HasDerivAt (fun y : ℝ => ψ t y) (Work.Spaces.pth ψ t x) x :=
      (((hψ.curry_θ ht0).contDiffAt (isOpen_Ioo.mem_nhds hxmem)).differentiableAt
        (by simp [Work.Stability.smoothOrder])).hasDerivAt
    have hd2 : HasDerivAt (fun y : ℝ => Work.Spaces.pth ψ t y)
        (Work.Spaces.pthIter 2 ψ t x) x :=
      (((hψ.pth.curry_θ ht0).contDiffAt (isOpen_Ioo.mem_nhds hxmem)).differentiableAt
        (by simp [Work.Stability.smoothOrder])).hasDerivAt
    have hgoal : HasDerivAt (fun y : ℝ => c t * ψ t y * Work.Spaces.pth ψ t y)
        (c t * (Work.Spaces.pth ψ t x * Work.Spaces.pth ψ t x
          + ψ t x * Work.Spaces.pthIter 2 ψ t x)) x := by
      have hcmul := (hd1.mul hd2).const_mul (c t)
      refine hcmul.congr_of_eventuallyEq ?_
      filter_upwards with y
      show c t * ψ t y * Work.Spaces.pth ψ t y = c t * (ψ t y * Work.Spaces.pth ψ t y)
      ring
    exact hgoal
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (x₀ := θ₀) (s := Set.Ioo t₁ t₂)
    (bound := fun _ : ℝ => max C 0) (F := F) (F' := F')
    (isOpen_Ioo.mem_nhds hθ₀mem) hmeas hint hmeas' hbound hintb hdiff
  -- the derivative integral splits into the two stated pieces
  have hI1 : IntervalIntegrable (fun z : ℝ => c z * (Work.Spaces.pth ψ z θ₀) ^ 2)
      volume a b :=
    (hc.mul (sliceOf hψ.pth θ₀ hθ₀mem |>.pow 2)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun z : ℝ => c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀)
      volume a b :=
    ((hc.mul (sliceOf hψ θ₀ hθ₀mem)).mul (sliceOf ((hψ.pth).pth) θ₀ hθ₀mem)).intervalIntegrable
  have hsplit : (∫ t in a..b, F' θ₀ t)
      = (∫ z in a..b, c z * (Work.Spaces.pth ψ z θ₀) ^ 2)
        + (∫ z in a..b, c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀) := by
    have hfun : (fun t : ℝ => F' θ₀ t)
        = fun t : ℝ => (fun z : ℝ => c z * (Work.Spaces.pth ψ z θ₀) ^ 2) t
            + (fun z : ℝ => c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀) t := by
      funext t
      simp only [hF']
      ring
    rw [hfun, intervalIntegral.integral_add hI1 hI2]
  rw [← hsplit]
  exact key.2

theorem mK_hasDerivAt_two {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ)
      ((∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ₀) ^ 2)
       + (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀)) θ₀ := by
  have hc : ContinuousOn (fun z : ℝ => χ k z * (Work.Spaces.w z) ^ 2)
      (Set.uIcc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)) := by
    have hsub : Set.uIcc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)
        ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      rw [Set.uIcc_of_le (Work.FTS.EllSol.PkgK5.cA_le_cB k)] at hz
      exact lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hz.1
    exact ((hχ.sm k).continuousOn.mono hsub).mul (continuousOn_w_sq_Ioi.mono hsub)
  exact hasDerivAt_integral_mul_pth (Work.FTS.EllSol.PkgK5.cA_pos k)
    (Work.FTS.EllSol.PkgK5.cA_le_cB k) hc hψ hθ₀

end Work.FTS.EllSol.PkgK5.InterpTrace
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cutAesmFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# A.e. strong measurability of the cut-off family and of the weight `w²·thEta`

All three functions in `cutAesmFacts` are continuous on the *open* quadrant
`(0,∞) × (0,π/2)`; the closed quadrant `Iz ×ˢ Iθ = [0,∞) × [0,π/2]` differs from it by the
null set of the coordinate axes.  Since the product `(volume.restrict Iz).prod
(volume.restrict Iθ)` is `volume.restrict (Iz ×ˢ Iθ)` (`Measure.prod_restrict`) and
`volume.restrict` only sees the set up to a.e. equality (`Measure.restrict_congr_set`),
continuity on the open quadrant is enough.
-/

/-- A real function continuous on the open quadrant `(0,∞) × (0,π/2)` is a.e. strongly
measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`. -/
theorem aestronglyMeasurable_of_continuousOn_openQuad {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- The closed quadrant and the open quadrant agree a.e. for the planar Lebesgue measure.
  have hz : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hθ : Work.Spaces.Iθ =ᵐ[(volume : Measure ℝ)] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : Measure (ℝ × ℝ))] (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hmain : MeasureTheory.AEStronglyMeasurable F
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hF.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have heq : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprod
  rw [heq]
  exact hmain





end Work.FTS.EllSol.PkgK5.TraceEngine
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.massK_iterated_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real Topology

/- Fubini/monotone-set facts for the joint integrand `G(z,θ) = w z ^ 2 * (∂_θψ z θ) ^ 2 * thEta θ`
on the box `S = [cA k, cB k] × Iθ`, given the integrability hypothesis `hE` of
`Work.FTS.EllSol.PkgK5.TraceEngine.massK_tendsto_zero`.

Route: `Measure.volume_eq_prod ℝ ℝ` + `Measure.prod_restrict` rewrite `hE` into integrability for
the product measure on `s ×ˢ Iθ`; `MeasureTheory.setIntegral_prod` gives the identity of the first
conjunct (with `MeasureTheory.integral_const_mul` to pull `w z ^ 2` out of the inner integral);
`MeasureTheory.setIntegral_nonneg` (using `thEta ≥ 0` on `Iθ`, since `0 ≤ sin(2θ)` there) gives the
second; `MeasureTheory.Integrable.integral_prod_left` gives the third; the fourth and fifth are the
same argument with `IntegrableOn.mono_set` (`Ioo 0 θ ⊆ Iθ`, resp. `Ioo θ (π/2) ⊆ Iθ`). -/
theorem massK_iterated_eq {k : ℕ} {ψ : ℝ → ℝ → ℝ}
    (hE : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
        (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ)) :
    (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
        (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s
      = ∫ p in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
    ∧ 0 ≤ ∫ p in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    ∧ MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ s in Set.Ioo 0 θ,
            (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
          (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ s in Set.Ioo θ (Real.pi / 2),
            (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
          (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)))) := by
  -- Abbreviate the box, the angular interval and the joint integrand.
  set s : Set ℝ := Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) with hs_def
  set I : Set ℝ := Work.Spaces.Iθ with hI_def
  set G : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2 *
    (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2 with hG_def
  -- `hE` is integrability for the product measure `(volume.restrict s).prod (volume.restrict I)`.
  have hE' : MeasureTheory.Integrable G
      ((MeasureTheory.volume.restrict s).prod (MeasureTheory.volume.restrict I)) := by
    rw [Measure.prod_restrict]
    exact hE
  -- The inner `θ`-integral with the constant `(w z)²` pulled out.
  have hinner : ∀ z, ∫ θ, G (z, θ) ∂(MeasureTheory.volume.restrict I) =
      (Work.Spaces.w z) ^ 2 * ∫ θ, ((Work.Spaces.pth ψ z θ) ^ 2 *
        Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict I) := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the iterated identity, by Fubini
    rw [show (∫ p in s ×ˢ I, G p) = ∫ p, G p ∂((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict I)) from by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      rw [← Measure.prod_restrict]]
    rw [MeasureTheory.integral_prod G hE']
    exact (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)).symm
  · -- (2) nonnegativity of the joint integral
    refine MeasureTheory.setIntegral_nonneg ?_ ?_
    · rw [hs_def, hI_def, Work.Spaces.Iθ]
      exact measurableSet_Icc.prod measurableSet_Icc
    · intro p hp
      obtain ⟨hz, hθ⟩ := hp
      have hθnn := Work.FTS.EllipticEst.thEta_nonneg (θ := p.2) hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hθnn
  · -- (3) integrability of the `z`-slice mass over `s`
    have h1 : MeasureTheory.Integrable (fun z => ∫ θ, G (z, θ) ∂(MeasureTheory.volume.restrict I))
        (MeasureTheory.volume.restrict s) := hE'.integral_prod_left
    exact h1.congr (Filter.Eventually.of_forall hinner)
  · -- (4) the same over the sub-interval `Ioo 0 θ ⊆ Iθ`
    intro θ hθ
    have hsub : Set.Ioo 0 θ ⊆ I := by
      rw [hI_def, Work.Spaces.Iθ]
      intro x hx
      exact ⟨hx.1.le, hx.2.le.trans hθ.2.le⟩
    have hmono : MeasureTheory.IntegrableOn G (s ×ˢ Set.Ioo 0 θ) MeasureTheory.volume :=
      hE.mono_set (Set.prod_mono Subset.rfl hsub)
    have h' : MeasureTheory.Integrable G ((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 θ))) := by
      rw [Measure.prod_restrict]
      exact hmono
    have h2 := h'.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    show ∫ y in Set.Ioo 0 θ, G (z, y) = (Work.Spaces.w z) ^ 2 * ∫ s in Set.Ioo 0 θ,
      (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  · -- (5) the same over the sub-interval `Ioo θ (π/2) ⊆ Iθ`
    intro θ hθ
    have hsub : Set.Ioo θ (Real.pi / 2) ⊆ I := by
      rw [hI_def, Work.Spaces.Iθ]
      intro x hx
      exact ⟨hθ.1.le.trans hx.1.le, hx.2.le⟩
    have hmono : MeasureTheory.IntegrableOn G (s ×ˢ Set.Ioo θ (Real.pi / 2)) MeasureTheory.volume :=
      hE.mono_set (Set.prod_mono Subset.rfl hsub)
    have h' : MeasureTheory.Integrable G ((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))) := by
      rw [Measure.prod_restrict]
      exact hmono
    have h2 := h'.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    show ∫ y in Set.Ioo θ (Real.pi / 2), G (z, y) = (Work.Spaces.w z) ^ 2 * ∫ s in
      Set.Ioo θ (Real.pi / 2), (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end Work.FTS.EllSol.PkgK5.TraceEngine
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.gK_ibp_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Clairaut for the two mixed second derivatives.**  For `G` smooth on the open quadrant,
`z > 0` and `θ ∈ (0,π/2)`, `∂_θ²(D_zG) = D_z(∂_θ²G)`; in the form needed here,
`∂_θ²(D_zG)(z,θ) = z·∂_z(θ' ↦ ∂_θ²G(z',θ))(z)`. -/
private lemma pthIter_two_Dz_eq {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = z * deriv (fun z' => Work.Spaces.pthIter 2 G z' θ) z := by
  rw [show Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ from rfl]
  rw [Work.FTS.EllSol.deriv_deriv_slice_Dz hG hz hθ]
  rfl

/-- The squared radial weight `w²` is `C¹` on `(0,∞)`. -/
private lemma w_sq_contDiffOn :
    ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : ContDiffOn ℝ 1 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.pow ?_ 2
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (contDiffOn_const.add contDiffOn_id).pow 2
    · exact contDiffOn_id.pow 2
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz))
  simpa only [Work.Spaces.w] using h

/-- The squared radial weight `w²` is continuous on `(0,∞)`. -/
private lemma w_sq_cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
  w_sq_contDiffOn.continuousOn

theorem gK_ibp_fts {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
        * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ)
      = - (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ)
        - (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
  have ha : 0 < cA k := cA_pos k
  have hab : cA k ≤ cB k := cA_le_cB k
  have hchi1 : ContDiffOn ℝ 1 (χ k) (Set.Ioi 0) :=
    (hχ.sm k).of_le (by simp [Work.Stability.smoothOrder])
  have hDz1 : ContDiffOn ℝ 1 (fun z => Work.Spaces.Dz G z θ) (Set.Ioi 0) :=
    (hG.Dz.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 G) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hG.pth.pth
  have hp2_1 : ContDiffOn ℝ 1 (fun z => Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
    (hpth2.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hφ : ContDiffOn ℝ 1 (fun z => χ k z * Work.Spaces.Dz G z θ) (Set.Ioi 0) := hchi1.mul hDz1
  -- the radial integration by parts, with the boundary terms kept
  have hIBP :=
    Work.FTS.EllipticEst.RPFresh.radial_ibp_bt (a := cA k) (b := cB k) ha hab hφ hp2_1
  -- the boundary terms vanish by the support hypothesis of `CutFam`
  have hχa : χ k (cA k) = 0 := hχ.supp k (cA k) ha (Or.inl le_rfl)
  have hχb : χ k (cB k) = 0 := hχ.supp k (cB k) (cB_pos k) (Or.inr le_rfl)
  have hBd : cB k * (Work.Spaces.w (cB k)) ^ 2 * (χ k (cB k) * Work.Spaces.Dz G (cB k) θ)
        * Work.Spaces.pthIter 2 G (cB k) θ
      - cA k * (Work.Spaces.w (cA k)) ^ 2 * (χ k (cA k) * Work.Spaces.Dz G (cA k) θ)
        * Work.Spaces.pthIter 2 G (cA k) θ = 0 := by
    rw [hχa, hχb]; ring
  -- the left-hand side is exactly the left-hand side of the radial IBP (Clairaut)
  have hLHS : (∫ z in (cA k)..(cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
        * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ)
      = ∫ z in (cA k)..(cB k),
          (Work.Spaces.w z) ^ 2 * (χ k z * Work.Spaces.Dz G z θ)
            * (z * deriv (fun z' => Work.Spaces.pthIter 2 G z' θ) z) := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [Set.uIcc_of_le hab] at hz
    have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
    rw [pthIter_two_Dz_eq hG hzpos hθ]
    ring
  -- the derivative of the coefficient `φ = χ_k · D_zG`
  have hderivmul : ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv (fun y => χ k y * Work.Spaces.Dz G y θ) z
        = deriv (χ k) z * Work.Spaces.Dz G z θ
          + χ k z * deriv (fun y => Work.Spaces.Dz G y θ) z := by
    intro z hzpos
    have h1 : HasDerivAt (fun y : ℝ => χ k y) (deriv (χ k) z) z :=
      ((hchi1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hzpos)).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => Work.Spaces.Dz G y θ)
        (deriv (fun y : ℝ => Work.Spaces.Dz G y θ) z) z :=
      ((hDz1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hzpos)).hasDerivAt
    exact (h1.mul h2).deriv
  -- the two right-hand integrands agree pointwise
  have hpoint : Set.EqOn
      (fun z => ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * (χ k z * Work.Spaces.Dz G z θ)
        + (z * (Work.Spaces.w z) ^ 2) * deriv (fun y => χ k y * Work.Spaces.Dz G y θ) z)
          * Work.Spaces.pthIter 2 G z θ)
      (fun z => χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ
        + (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ)
      (Set.uIcc (cA k) (cB k)) := by
    intro z hz
    simp only []
    rw [Set.uIcc_of_le hab] at hz
    have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
    rw [hderivmul z hzpos]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  have hsubIcc : Set.Icc (cA k) (cB k) ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hD2 : ContDiffOn ℝ 1 (fun z => Work.Spaces.DzIter 2 G z θ) (Set.Ioi 0) :=
    ((hG.DzIter 2).curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hb : ContDiffOn ℝ 1 (fun z : ℝ => (z - 3) / (1 + z)) (Set.Ioi 0) := by
    refine ContDiffOn.div ?_ ?_ ?_
    · exact contDiffOn_id.sub contDiffOn_const
    · exact contDiffOn_const.add contDiffOn_id
    · intro z hz; exact ne_of_gt (by linarith [show (0 : ℝ) < z from hz])
  -- interval integrability of the two pieces of the right-hand side
  have hint1 : IntervalIntegrable
      (fun z => χ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
          * Work.Spaces.pthIter 2 G z θ) volume (cA k) (cB k) := by
    have hcd : ContDiffOn ℝ 1 (fun z => χ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
          * Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
      ((hchi1.mul w_sq_contDiffOn).mul (hD2.add (hb.mul hDz1))).mul hp2_1
    exact (hcd.continuousOn.mono hsubIcc).intervalIntegrable_of_Icc hab
  have hdchi : ContinuousOn (fun z : ℝ => deriv (χ k) z) (Set.Ioi 0) :=
    hchi1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hint2 : IntervalIntegrable
      (fun z => (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) volume (cA k) (cB k) := by
    have hcdc : ContinuousOn (fun z => (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
      (((continuousOn_id.mul hdchi).mul w_sq_cont).mul hDz1.continuousOn).mul hp2_1.continuousOn
    exact (hcdc.mono hsubIcc).intervalIntegrable_of_Icc hab
  -- split the radial IBP right-hand side into the two integrals of the statement
  have hJrhs :
      (∫ z in (cA k)..(cB k),
          ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * (χ k z * Work.Spaces.Dz G z θ)
            + (z * (Work.Spaces.w z) ^ 2)
              * deriv (fun y => χ k y * Work.Spaces.Dz G y θ) z)
            * Work.Spaces.pthIter 2 G z θ)
      = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ)
        + (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
    rw [intervalIntegral.integral_congr hpoint]
    rw [intervalIntegral.integral_add hint1 hint2]
  have hmain : (∫ z in (cA k)..(cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
        * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ)
      = 0 - ((∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ)
        + (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ)) := by
    rw [hLHS, hIBP, hBd, hJrhs]
  rw [hmain]
  ring

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The angular `θ`-Poincaré estimate with boundary traces

`Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace`: for data `f` which is `C^∞` on the *open*
quadrant `(0,∞) × (0,π/2)` and whose angular slices `D_z^j f z ·` (`j ≤ k`, `z > 0`) vanish at
the two endpoints `θ = 0, π/2` in the sense of *limits*, and with `∂_θ²f ∈ ℋ^k` honestly, the
weighted `ℋ^k`-norms of `f` and `∂_θ f` are controlled by that of `∂_θ² f`, and both `f` and
`∂_θ f` are honestly in `ℋ^k`.

The proof integrates the per-`z` comparisons
`HkIntegrand_integral_le_pth2_trace` / `HkIntegrand_integral_le_pth2_pth_trace` (which rest on
the single-slice estimates `sliceF_le_sliceV` / `sliceF_deriv_le_sliceV` and the slice-group
identities) over `z ∈ Iz`, using the a.e. strong measurability of the `z`-integral of the
`ℋ^k`-integrand and the honesty of `∂_θ²f`.
-/

theorem thetaPoincareOpenTrace (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 f) →
      Work.Spaces.HkMem α k f ∧ Work.Spaces.HkMem α k (Work.Spaces.pth f) ∧
        Work.Spaces.HkNorm α k f ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) ∧
        Work.Spaces.HkNorm α k (Work.Spaces.pth f)
          ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
  obtain ⟨C1, hC1pos, hC1⟩ := HkIntegrand_integral_le_pth2_trace k
  obtain ⟨C2, hC2pos, hC2⟩ := HkIntegrand_integral_le_pth2_pth_trace k
  refine ⟨max 1 (max C1 C2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α f hα0 hα4 hsm htrace hmem
  have hα1 : α ≤ 1 := by linarith
  have hSO : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hSOp : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f) := hSO.pth
  have h1 := hC1 α f hα0 hα1 hSO htrace hmem.1
  have h2 := hC2 α f hα0 hα1 hSO htrace hmem.1
  have hC1le : C1 ≤ max 1 (max C1 C2) :=
    le_trans (le_max_left C1 C2) (le_max_right 1 (max C1 C2))
  have hC2le : C2 ≤ max 1 (max C1 C2) :=
    le_trans (le_max_right C1 C2) (le_max_right 1 (max C1 C2))
  have hmemf : Work.Spaces.HkMem α k f := by
    refine ⟨fun z hz => (h1 z hz).1, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul C1)
      (aesm_integral_HkIntegrand α k hSO) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ from
      MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))]
    exact (h1 z hz).2
  have hmem1 : Work.Spaces.HkMem α k (Work.Spaces.pth f) := by
    refine ⟨fun z hz => (h2 z hz).1, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul C2)
      (aesm_integral_HkIntegrand α k hSOp) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ from
      MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ))]
    exact (h2 z hz).2
  have hSq1 : Work.Spaces.HkSq α k f ≤ C1 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := by
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) z
          ≤ C1 * (fun z => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => (h1 z hz).2)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    have hInt : MeasureTheory.IntegrableOn (fun z => C1 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)) Work.Spaces.Iz :=
      hmem.2.const_mul C1
    have hm := MeasureTheory.integral_mono_of_nonneg hnn hInt hle
    calc Work.Spaces.HkSq α k f
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, C1 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := hm
      _ = C1 * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) :=
          MeasureTheory.integral_const_mul C1 _
      _ = C1 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := rfl
  have hSq2 : Work.Spaces.HkSq α k (Work.Spaces.pth f)
      ≤ C2 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := by
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) z
          ≤ C2 * (fun z => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => (h2 z hz).2)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) :=
      Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ)
    have hInt : MeasureTheory.IntegrableOn (fun z => C2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)) Work.Spaces.Iz :=
      hmem.2.const_mul C2
    have hm := MeasureTheory.integral_mono_of_nonneg hnn hInt hle
    calc Work.Spaces.HkSq α k (Work.Spaces.pth f)
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, C2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := hm
      _ = C2 * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) :=
          MeasureTheory.integral_const_mul C2 _
      _ = C2 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := rfl
  refine ⟨hmemf, hmem1, ?_, ?_⟩
  · calc Work.Spaces.HkNorm α k f = Real.sqrt (Work.Spaces.HkSq α k f) := rfl
      _ ≤ Real.sqrt (C1 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f)) :=
          Real.sqrt_le_sqrt hSq1
      _ = Real.sqrt C1 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul hC1pos.le, Work.Spaces.HkNorm]
      _ ≤ max 1 (max C1 C2) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact le_trans (sqrt_le_max_one C1) (max_le (le_max_left _ _) hC1le)
  · calc Work.Spaces.HkNorm α k (Work.Spaces.pth f)
        = Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pth f)) := rfl
      _ ≤ Real.sqrt (C2 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f)) :=
          Real.sqrt_le_sqrt hSq2
      _ = Real.sqrt C2 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul hC2pos.le, Work.Spaces.HkNorm]
      _ ≤ max 1 (max C1 C2) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact le_trans (sqrt_le_max_one C2) (max_le (le_max_left _ _) hC2le)

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllSol.ropPoincareAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The level-`4` angular Poincaré estimate `ropPoincareAe`

For `f` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)` whose angular slices satisfy the
endpoint trace conditions

* `D_z^j f z · → 0` at both endpoints, for `j ≤ 3` at *every* `z > 0` and for `j = 4` for
  *almost every* `z > 0`,

whose `D_z^j`-slices vanish at the two endpoints as *values* for `j ≤ 4`, and whose second angular
derivative is honestly in `ℋ⁴`, the weighted `ℋ⁴`-norms of `f` and of `∂_θ f` are bounded by a
constant (uniform in `α ∈ (0,1]`) times that of `∂_θ² f`, and `f`, `∂_θ f` are themselves honestly
in `ℋ⁴`.

Route: for almost every `z` the `ℋ⁴`-integrand of `f` (resp. `∂_θ f`) is compared slice group by
slice group with the one of `∂_θ² f` (`RPAe.groupBoundF`, `RPAe.groupBoundP`, both resting on the
single-slice estimates `VopAux.sliceF_le_sliceV` / `VopAux.sliceF_deriv_le_sliceV`), and the
comparison is integrated over `z`.  Pointwise in `z` the integrability of every slice group is
supplied by `RPAe.sliceGroupIntegrable`, which needs no trace hypothesis: the extra ingredient is
that `∫ (u'')² sin(2θ)^{-η} < ∞` forces `u'` to have a finite limit at both endpoints (Hölder
against `sin(2θ)^{η} ∈ L¹`), hence `u` to be bounded there.
-/

theorem ropPoincareAe : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) →
      (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        Work.Spaces.DzIter j f z 0 = 0 ∧ Work.Spaces.DzIter j f z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 4 (Work.Spaces.pthIter 2 f) →
      Work.Spaces.HkMem α 4 f ∧ Work.Spaces.HkMem α 4 (Work.Spaces.pth f) ∧
        Work.Spaces.HkNorm α 4 f ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) ∧
        Work.Spaces.HkNorm α 4 (Work.Spaces.pth f)
          ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
  refine ⟨max 1 Work.FTS.EllSol.RPAe.sliceCs,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α f hα0 hα1 hsm htr3 htr4ae hval hmem
  have hSO : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hSOp : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f) := hSO.pth
  have hSO2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hSO.pth.pth
  have hrgst : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm
  -- the conull set of `z` carrying all the trace hypotheses
  have hgood : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (0 < z) ∧ (∀ j : ℕ, j ≤ 4 →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
    have h4 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      rw [hrgst]
      exact htr4ae
    have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
      rw [hrgst]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
    filter_upwards [hpos, h4] with z hz h4z
    refine ⟨hz, fun j hj => ?_⟩
    rcases le_or_gt j 3 with h3 | h3
    · exact htr3 j h3 z hz
    · have hj4 : j = 4 := by omega
      subst hj4
      exact h4z
  -- per-`z` integrability of the slice groups
  have hgrp : ∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ)
        Work.Spaces.Iθ :=
    RPAe.sliceGroupIntegrableEasy α f hα0 hα1 hSO htr3 hmem.1
  -- the slice groups at `z = 0` vanish
  have hgrp0 : ∀ (G : ℝ → ℝ → ℝ) (j : ℕ) (θ : ℝ),
      Work.FTS.EllipticEst.sliceGroup α 4 j G 0 θ = 0 := by
    intro G j θ
    rw [Work.FTS.EllipticEst.sliceGroup, Work.Spaces.Wt, Work.Spaces.w]
    simp
  -- pointwise integrability of the `ℋ⁴`-integrand
  have hint_f : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        Work.Spaces.Iθ := by
    intro z hz
    rw [show (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        = fun θ => ∑ j ∈ Finset.range 5,
            Work.FTS.EllipticEst.sliceGroup α 4 j f z θ from
      funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α 4 f z θ]
    exact MeasureTheory.integrable_finsetSum (Finset.range 5)
      (fun j hj => (hgrp z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
  have hint_p : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        Work.Spaces.Iθ := by
    intro z hz
    rw [show (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        = fun θ => ∑ j ∈ Finset.range 5,
            Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ from
      funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α 4 (Work.Spaces.pth f) z θ]
    exact MeasureTheory.integrable_finsetSum (Finset.range 5)
      (fun j hj => (hgrp z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2)
  -- integrability of the slice groups of `∂_θ²f`
  have hgrp2 : ∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
        Work.Spaces.Iθ := by
    intro z hz j hj
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [show (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) 0 θ)
          = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => hgrp0 (Work.Spaces.pthIter 2 f) j θ]
      exact integrableOn_zero
    · exact Work.FTS.EllSol.VopAux.integrableOn_sliceGroup_of_HkIntegrand hSO2 hzpos hj
        (hmem.1 z hz)
  -- the three decompositions of the angle integrals into slice groups
  have hdec : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 G z θ) Work.Spaces.Iθ) →
      (∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 → MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j G z θ) Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 G z θ)
          = ∑ j ∈ Finset.range 5, ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j G z θ := by
    intro G hG hInt hgrps z hz
    rw [← MeasureTheory.integral_finsetSum (s := Finset.range 5)
      (f := fun j θ => Work.FTS.EllipticEst.sliceGroup α 4 j G z θ)
      (fun j hj => hgrps z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
      Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α 4 G z θ)
  have hdec_f := hdec f hSO hint_f (fun z hz j hj => (hgrp z hz j hj).1)
  have hdec_p := hdec (Work.Spaces.pth f) hSOp hint_p (fun z hz j hj => (hgrp z hz j hj).2)
  have hdec_2 := hdec (Work.Spaces.pthIter 2 f) hSO2 hmem.1 hgrp2
  -- the two a.e. per-`z` comparisons
  have hbd_f : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
    filter_upwards [hgood] with z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz.1
    have hjb : ∀ j ∈ Finset.range 5, j ≤ 4 := fun j hj =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        = ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ :=
          hdec_f z hzI
      _ ≤ ∑ j ∈ Finset.range 5, Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) :=
          Finset.sum_le_sum fun j hj =>
            RPAe.groupBoundF α f hα0 hα1 hSO z hz.1 j (hjb j hj)
              (hz.2 j (hjb j hj)).1 (hz.2 j (hjb j hj)).2 (hmem.1 z hzI)
      _ = Work.FTS.EllSol.RPAe.sliceCs * ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ :=
          (Finset.mul_sum (Finset.range 5)
            (fun j => ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
            Work.FTS.EllSol.RPAe.sliceCs).symm
      _ = Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
          rw [hdec_2 z hzI]
  have hbd_p : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
    filter_upwards [hgood] with z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz.1
    have hjb : ∀ j ∈ Finset.range 5, j ≤ 4 := fun j hj =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        = ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ :=
          hdec_p z hzI
      _ ≤ ∑ j ∈ Finset.range 5, Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) :=
          Finset.sum_le_sum fun j hj =>
            RPAe.groupBoundP α f hα0 hα1 hSO z hz.1 j (hjb j hj)
              (hz.2 j (hjb j hj)).1 (hz.2 j (hjb j hj)).2 (hmem.1 z hzI)
      _ = Work.FTS.EllSol.RPAe.sliceCs * ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ :=
          (Finset.mul_sum (Finset.range 5)
            (fun j => ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
            Work.FTS.EllSol.RPAe.sliceCs).symm
      _ = Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
          rw [hdec_2 z hzI]
  -- membership
  have hmemf : Work.Spaces.HkMem α 4 f := by
    refine ⟨hint_f, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul Work.FTS.EllSol.RPAe.sliceCs)
      (Work.FTS.EllSol.VopAux.aesm_integral_HkIntegrand α 4 hSO) ?_
    filter_upwards [hbd_f] with z hz
    rw [Real.norm_of_nonneg (MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
      measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))]
    exact hz
  have hmem1 : Work.Spaces.HkMem α 4 (Work.Spaces.pth f) := by
    refine ⟨hint_p, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul Work.FTS.EllSol.RPAe.sliceCs)
      (Work.FTS.EllSol.VopAux.aesm_integral_HkIntegrand α 4 hSOp) ?_
    filter_upwards [hbd_p] with z hz
    rw [Real.norm_of_nonneg (MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
      measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 (Work.Spaces.pth f) z θ))]
    exact hz
  -- the squared norm comparisons
  have hSq_le : ∀ (G : ℝ → ℝ → ℝ),
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 G z θ)
          ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ)) →
      Work.Spaces.HkSq α 4 G
        ≤ Work.FTS.EllSol.RPAe.sliceCs * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f) := by
    intro G hbd
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 G z θ) :=
      Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
        measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 G z θ)
    have hInt : MeasureTheory.Integrable (fun z => Work.FTS.EllSol.RPAe.sliceCs *
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hmem.2.const_mul Work.FTS.EllSol.RPAe.sliceCs
    have hm := MeasureTheory.integral_mono_of_nonneg hnn hInt hbd
    calc Work.Spaces.HkSq α 4 G
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 G z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := hm
      _ = Work.FTS.EllSol.RPAe.sliceCs * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) :=
          MeasureTheory.integral_const_mul Work.FTS.EllSol.RPAe.sliceCs _
      _ = Work.FTS.EllSol.RPAe.sliceCs * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f) := rfl
  have hSq1 := hSq_le f hbd_f
  have hSq2 := hSq_le (Work.Spaces.pth f) hbd_p
  -- the norm comparisons
  have hnorm_le : ∀ (G : ℝ → ℝ → ℝ), Work.Spaces.HkSq α 4 G
        ≤ Work.FTS.EllSol.RPAe.sliceCs * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f) →
      Work.Spaces.HkNorm α 4 G
        ≤ max 1 Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
    intro G hSq
    calc Work.Spaces.HkNorm α 4 G = Real.sqrt (Work.Spaces.HkSq α 4 G) := rfl
      _ ≤ Real.sqrt (Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f)) := Real.sqrt_le_sqrt hSq
      _ = Real.sqrt Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul (le_of_lt Work.FTS.EllSol.RPAe.sliceCs_pos), Work.Spaces.HkNorm]
      _ ≤ max 1 Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact Work.FTS.EllSol.VopAux.sqrt_le_max_one Work.FTS.EllSol.RPAe.sliceCs
  exact ⟨hmemf, hmem1, hnorm_le f hSq1, hnorm_le (Work.Spaces.pth f) hSq2⟩


end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.TruncIdent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-! ## Integrability tools -/

/-- A function vanishing outside a measurable box `K ⊆ Q0` and integrable on `K` is integrable on
the open quadrant. -/
theorem integrableOn_Q0_of_integrableOn_box {f : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hKmeas : MeasurableSet K) (hKsub : K ⊆ Work.FTS.EllipticEst.Q0)
    (hint : MeasureTheory.IntegrableOn f K)
    (hzero : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, f p = 0) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 := by
  have heq : Work.FTS.EllipticEst.Q0.indicator f = K.indicator f := by
    funext p
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hKsub hp)]
    · by_cases hq : p ∈ Work.FTS.EllipticEst.Q0
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_mem hq, hzero p ⟨hq, hp⟩]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
  rw [← MeasureTheory.integrable_indicator_iff Work.FTS.EllipticEst.isOpen_Q0.measurableSet, heq]
  exact (MeasureTheory.integrable_indicator_iff hKmeas).mpr hint

/-- A function vanishing outside the closed box `[a,b] × [c,d]` and continuous on it is integrable
on the open quadrant. -/
theorem integrableOn_Q0_of_continuousOn_box {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (ha : 0 < a) (hc0 : 0 < c) (hd : d < π / 2)
    (hcont : ContinuousOn f (Set.Icc a b ×ˢ Set.Icc c d))
    (hzero : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ (Set.Icc a b ×ˢ Set.Icc c d), f p = 0) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 :=
  integrableOn_Q0_of_integrableOn_box (measurableSet_Icc.prod measurableSet_Icc)
    (fun p hp => Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩)
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)) hzero

/-- The mode-`m` term of the left-hand side is integrable on the quadrant. -/
theorem integrableOn_mode_L (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hc0 : 0 < c) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hAcont : ContinuousOn (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Icc a b) := by
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact (radGreenContinuousOn hα hα1 m hc2 hcm).mono
      (fun z hz => lt_of_lt_of_le ha hz.1)
  have hem : Continuous (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous
  refine integrableOn_Q0_of_continuousOn_box (a := a) (b := b) (c := c) (d := d)
    ha hc0 hd ?_ ?_
  · refine ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_) ?_
    · exact hAcont.comp continuousOn_fst (fun p hp => hp.1)
    · exact hem.comp_continuousOn continuousOn_snd
    · exact (continuousOn_bslOp hφsm).mono (fun p hp =>
        Work.FTS.EllipticEst.mem_Q0.mpr
          ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩)
    · exact (continuousOn_fst.rpow_const (fun p hp =>
        Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
        (Real.continuous_cos.comp_continuousOn continuousOn_snd)
  · intro p hp
    rw [bslOp_eq_zero_off_box hbox hp.2]
    ring

/-- The mode-`m` term of the right-hand side is integrable on the quadrant. -/
theorem integrableOn_mode_R (α : ℝ) (m : ℕ) {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c ≤ d) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hem : Continuous (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2
      * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((hem.comp_continuousOn continuousOn_snd).mul (hφsm.continuousOn.mono hKsub)).mul
      ((continuousOn_fst.rpow_const (fun p hp =>
        Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
        (Real.continuous_cos.comp_continuousOn continuousOn_snd))
  have hbase : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      Work.FTS.PhiStar.Series.cmode m F p.1
        * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable hc2 hcm ha hab hc0 hcd hg
  have hKint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    hbase.congr_fun (fun p _ => by ring) (measurableSet_Icc.prod measurableSet_Icc)
  refine integrableOn_Q0_of_integrableOn_box (measurableSet_Icc.prod measurableSet_Icc)
    hKsub hKint ?_
  intro p hp
  have hφ0 : φ p.1 p.2 = 0 := by
    by_cases h1 : p.1 ∈ Set.Ioo a b
    · exact test_vanishes_off_theta hbox (fun h2 => hp.2 ⟨⟨h1.1.le, h1.2.le⟩,
        ⟨h2.1.le, h2.2.le⟩⟩)
    · exact test_vanishes_off_z hbox h1
  rw [hφ0]
  ring

/-! ## Integrability of the truncated sums -/

/-- The left-hand side integrand is integrable on the quadrant. -/
theorem integrableOn_psiTrunc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F φ : ℝ → ℝ → ℝ}
    (hcF : ∀ m : ℕ, MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (haF : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hc0 : 0 < c) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) (N : ℕ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
        * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hfun : (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
      * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = (fun p : ℝ × ℝ => (∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.acoeff α m F p.1
              * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    funext p
    simp only [Work.FTS.PhiStar.Series.psiTrunc]
  rw [hfun]
  refine integrableOn_Q0_of_continuousOn_box (a := a) (b := b) (c := c) (d := d)
    ha hc0 hd ?_ ?_
  · refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine continuousOn_finsetSum _ fun m _ => ?_
      have hAcont : ContinuousOn (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Icc a b) := by
        simp only [Work.FTS.PhiStar.Series.acoeff]
        exact (radGreenContinuousOn hα hα1 m (hcF m) (haF m)).mono
          (fun z hz => lt_of_lt_of_le ha hz.1)
      exact (hAcont.comp continuousOn_fst (fun p hp => hp.1)).mul
        ((Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).comp_continuousOn
          continuousOn_snd)
    · exact (continuousOn_bslOp hφsm).mono (fun p hp =>
        Work.FTS.EllipticEst.mem_Q0.mpr
          ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩)
    · exact (continuousOn_fst.rpow_const (fun p hp =>
        Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
        (Real.continuous_cos.comp_continuousOn continuousOn_snd)
  · intro p hp
    rw [bslOp_eq_zero_off_box hbox hp.2]
    ring

/-- The truncated source integrand is integrable on the quadrant. -/
theorem integrableOn_truncSource (α : ℝ) {F φ : ℝ → ℝ → ℝ}
    (hcF : ∀ m : ℕ, MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (haF : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c ≤ d) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) (N : ℕ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hsum : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    induction N with
    | zero =>
      have hfun : (fun p : ℝ × ℝ =>
          (∑ m ∈ Finset.range (0 + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
          = (fun p : ℝ × ℝ =>
              (Work.FTS.PhiStar.Series.cmode 0 F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam 0 p.2)
                * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
        funext p
        rw [Finset.range_one, Finset.sum_singleton]
      rw [hfun]
      exact IntegrableOn.mono_set (integrableOn_mode_R α 0 (hcF 0) (haF 0) hφ hφc hφs ha hab
        hc0 hcd hd hbox) hKsub
    | succ N ih =>
      have hfun : (fun p : ℝ × ℝ =>
          (∑ m ∈ Finset.range (N + 1 + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
          = (fun p : ℝ × ℝ =>
              (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
                * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
              + (Work.FTS.PhiStar.Series.cmode (N + 1) F p.1
                  * Work.FTS.PhiStar.Gegenbauer.eFam (N + 1) p.2)
                  * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
        funext p
        rw [Finset.sum_range_succ]
        ring
      rw [hfun]
      exact ih.add (IntegrableOn.mono_set (integrableOn_mode_R α (N + 1) (hcF (N + 1))
        (haF (N + 1)) hφ hφc hφs ha hab hc0 hcd hd hbox) hKsub)
  refine integrableOn_Q0_of_integrableOn_box (measurableSet_Icc.prod measurableSet_Icc)
    hKsub hsum ?_
  intro p hp
  have hφ0 : φ p.1 p.2 = 0 := by
    by_cases h1 : p.1 ∈ Set.Ioo a b
    · exact test_vanishes_off_theta hbox (fun h2 => hp.2 ⟨⟨h1.1.le, h1.2.le⟩,
        ⟨h2.1.le, h2.2.le⟩⟩)
    · exact test_vanishes_off_z hbox h1
  rw [hφ0]
  ring

/-! ## The truncated weak identity -/

/-- **The truncated weak identity.** -/
theorem psiTrunc_weak_identity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F φ : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (N : ℕ) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0,
          (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  obtain ⟨a, b, c, d, ha, hab, hc0, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hcF : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) := fun m =>
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  have haF : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := fun m =>
    Work.EllipticEst.ModalSolution.aesm_cmode hsm m
  have hA0 : ∀ z, Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := acoeff_zero_of_orth horth α
  have hC0 : ∀ z, Work.FTS.PhiStar.Series.cmode 0 F z = 0 := cmode_zero_eq_zero horth
  have hL0ae : (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F 0 p.1 p.2
      * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      =ᵐ[(volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0] fun _ => 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp
    rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.range_one, Finset.sum_singleton, hA0 p.1]
    ring
  have hR0ae : (fun p : ℝ × ℝ => (∑ m ∈ Finset.range (0 + 1),
        Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      =ᵐ[(volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0] fun _ => 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp
    rw [Finset.range_one, Finset.sum_singleton, hC0 p.1]
    ring
  have hpsi : ∀ N : ℕ,
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F (N + 1) p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
              * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
            + (Work.FTS.PhiStar.Series.acoeff α (N + 1) F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam (N + 1) p.2)
                * (Work.Elliptic.bslOp α φ p.1 p.2)
                * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    intro N
    funext p
    simp only [Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_range_succ]
    ring
  have hsrc : ∀ N : ℕ,
      (fun p : ℝ × ℝ =>
          (∑ m ∈ Finset.range (N + 1 + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = (fun p : ℝ × ℝ =>
              (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
                * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
              + (Work.FTS.PhiStar.Series.cmode (N + 1) F p.1
                  * Work.FTS.PhiStar.Gegenbauer.eFam (N + 1) p.2)
                  * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    intro N
    funext p
    rw [Finset.sum_range_succ]
    ring
  induction N with
  | zero =>
    rw [MeasureTheory.integral_congr_ae hL0ae, MeasureTheory.integral_congr_ae hR0ae]
  | succ N ih =>
    have hIntL := integrableOn_psiTrunc α hα hα1 hcF haF hφ hφc hφs ha hc0 hd hbox N
    have hmodeL := integrableOn_mode_L α hα hα1 (N + 1) (hcF (N + 1)) (haF (N + 1))
      hφ hφc hφs ha hc0 hd hbox
    have hIntR := integrableOn_truncSource α hcF haF hφ hφc hφs ha hab.le hc0 hcd.le hd hbox N
    have hmodeR := integrableOn_mode_R α (N + 1) (hcF (N + 1)) (haF (N + 1))
      hφ hφc hφs ha hab.le hc0 hcd.le hd hbox
    have hper := perModeQ0 α hα hα1 (N + 1) (by omega) (hcF (N + 1)) (haF (N + 1)) hφ hφc hφs
    rw [hpsi N, MeasureTheory.integral_add hIntL hmodeL, ih, hper,
      ← MeasureTheory.integral_add hIntR hmodeR, ← hsrc N]

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RouteB.lintegral_sq_le_HkSq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RouteB

/-- The unweighted square of `Y` on the open quadrant is dominated by `HkSq α 0 Y`: on
`Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)` the level-`0` integrand is `(Y · w z / sin(2θ)^{η/2})²` and the factor
`w z / sin(2θ)^{η/2} ≥ 1` there.  Suggested route: `lintegral_mono` pointwise, then
`lintegral_mono_set` for `Q0 ⊆ Iz ×ˢ Iθ`, then Tonelli (`MeasureTheory.lintegral_prod`, using the
joint a.e.-measurability hypothesis) and
`Work.FTS.ClassCHon.CmpSupp.lintegral_HkIntegrand_eq` together with
`Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici` (the point `z = 0` contributes `0`). -/
theorem lintegral_sq_le_HkSq_zero {α : ℝ} {Y : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α 0 Y)
    (hmeas : AEMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal ((Y p.1 p.2) ^ 2))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 Y) := by
  -- The level-`0` integrand is a single square, namely `(Y · w z / sin(2θ)^{η/2})²`.
  have hK : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0 Y z θ
      = (Y z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun z θ => by simp [Work.Spaces.HkIntegrand]
  -- The angular weight `w z / sin(2θ)^{η/2}` is (everywhere) measurable, and `hmeas` gives the
  -- a.e. measurability of `Y`; hence the level-`0` integrand is a.e. measurable for
  -- `(volume.restrict Iz).prod (volume.restrict Iθ)`, as Tonelli requires.
  have hw : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) := by
    have h : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [h]
    exact ((measurable_const.add measurable_fst).pow measurable_const).div
      (measurable_fst.pow measurable_const)
  have hs : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    ((Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable).comp
      ((Real.continuous_sin.measurable).comp (measurable_snd.const_mul 2))
  have hc : Measurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    hw.div hs
  have hmeas_int : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hY : AEMeasurable (fun p : ℝ × ℝ => Y p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hmeas
    have hfun : (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2))
        = fun p : ℝ × ℝ => ENNReal.ofReal ((Y p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      funext p; rw [hK]
    rw [hfun]
    exact ((hY.mul hc.aemeasurable).pow measurable_const.aemeasurable).ennreal_ofReal
  -- `Q0` sits inside `Iz ×ˢ Iθ`.
  have hQ0sub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Set.mem_prod.mpr ⟨le_of_lt hz, Set.mem_Icc.mpr ⟨le_of_lt hθ0, le_of_lt hθ1⟩⟩
  -- Pointwise on the open quadrant the weight factor is `≥ 1`, hence the plain square is the
  -- smaller one.
  have hpt : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      (Y p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 Y p.1 p.2 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    rw [hK p.1 p.2]
    have hsin_pos : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hsin_le : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have hrpow_pos : 0 < (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hsin_pos _
    have hrpow_le : (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hsin_pos) hsin_le (by norm_num [Work.Spaces.eta])
    have hw1 : 1 ≤ Work.Spaces.w p.1 := by
      rw [Work.Spaces.w]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < p.1 ^ 2)]
      nlinarith [hz]
    have hc1 : 1 ≤ Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ hrpow_pos]
      linarith
    have hcsq : 1 ≤ (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      nlinarith
    calc (Y p.1 p.2) ^ 2
        = (Y p.1 p.2) ^ 2 * 1 := by ring
      _ ≤ (Y p.1 p.2) ^ 2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hcsq (sq_nonneg _)
      _ = (Y p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
  -- `Ioi 0` and `Iz = Ici 0` differ by the null set `{0}`.
  have hIoi_eq_Iz : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  -- The product measure on `Iz ×ˢ Iθ` is the product of the two restricted measures.
  have hprod : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  -- Identification of the real-valued iterated integral with `HkSq`.
  have hSq : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Y z θ)
      = Work.Spaces.HkSq α 0 Y := by
    change _ = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 Y z θ)
    rw [← hIoi_eq_Iz]
  calc (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal ((Y p.1 p.2) ^ 2))
      ≤ ∫⁻ p in Work.FTS.EllipticEst.Q0,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2) := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
        exact Eventually.of_forall fun p hp => ENNReal.ofReal_le_ofReal (hpt p hp)
    _ ≤ ∫⁻ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2) :=
        lintegral_mono_set hQ0sub
    _ = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [hprod]
    _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y z θ) :=
        MeasureTheory.lintegral_prod _ hmeas_int
    _ = ∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y z θ) := by
        rw [← hIoi_eq_Iz]
    _ = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Y z θ) :=
        Work.FTS.ClassCHon.CmpSupp.lintegral_HkIntegrand_eq (k := 0) hm
    _ = ENNReal.ofReal (Work.Spaces.HkSq α 0 Y) := by rw [hSq]

end Work.FTS.PhiStar.RouteB
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

set_option autoImplicit false

/-- The constant `3α/(2c(α))` of the separation identities.  For `0 < α ≤ 1` one has
`0 < Cc α ≤ 15`. -/
abbrev Cc (α : ℝ) : ℝ := 3 * α / (2 * Work.Spaces.c α)

/-- The angular profile of the separated form of `NP4a`: `Cc α · Γ(θ)·q(θ)`. -/
abbrev CC (α : ℝ) : ℝ → ℝ :=
  fun θ => Cc α * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)

/-- The angular profile of the separated form of `NP5a`: `-Cc α · Γ(θ)·q(θ)`. -/
abbrev CC5 (α : ℝ) : ℝ → ℝ :=
  fun θ => -(Cc α) * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)

/-- The angular block of the order-`6` separation bound: the `η`-weighted square of `C` plus the
`γ`-weighted squares of its `D_θ`-jets of orders `1..6`.  This is the first factor produced by
`L6Aux.HkIntegrandSepLeGen` at `k = 6`. -/
abbrev AngBlk (α : ℝ) (C : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 7,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The radial profile of the separated form of `NP4a`: `F_*(z)·L₁₂(w)(z)`. -/
abbrev BB4 (w : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => Work.FM.Fstar z * Work.Construction.L12 w z

/-- The radial profile of the separated form of `NP5a`: `H(z)·L₁₂(w)(z)`, where
`H = 2z(1-z)/(1+z)³` is the radial factor of `D_zF_*`. -/
abbrev BB5 (w : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTraceO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 2000000

/-! ## The angular trace of a `C¹` slice, with the weighted Hardy rate

This file proves the lemma `SliceTraceO`: for a function `u` of class `C¹` on `(0,π/2)` whose
weighted angular energy `(u')² sin(2·)^{2-γ}` is integrable on `Iθ = [0,π/2]`, the slice `u`
has a trace `mu` at `θ = 0⁺`, and the convergence happens at the weighted Hardy rate

  `(u θ - mu)² ≤ (100/(γ-1)) · sin(2θ)^{γ-1} · ∫_{Iθ} (u')² sin(2σ)^{2-γ}`,   `0 < θ < π/4`,

where `γ = Work.Spaces.gam α = 1 + α/10`.

The mathematics is the classical weighted Hardy argument.  On `[a,b] ⊆ (0,π/4]` the fundamental
theorem of calculus and the weighted Cauchy–Schwarz inequality
(`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt`) give

  `|u b - u a| ≤ √(∫_a^b (u')² sin(2·)^{2-γ}) · √(∫_a^b sin(2·)^{γ-2})`,

the first factor is `≤ √A` with `A = ∫_{Iθ} (u')² sin(2·)^{2-γ}`
(`Work.FTS.H2.interval_integral_le_setIntegral_Iθ`), and the second is
`≤ √(100 sin(2b)^{γ-1}/(γ-1))` (`SinPowIntegral`).  The resulting oscillation bound vanishes as
`b → 0⁺`, so the slice is Cauchy at `0⁺` and its limit `mu` obeys the same bound (`TraceOfOsc`);
squaring it is the stated inequality. -/

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ_core {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **The weighted oscillation bound.**  For `u` of class `C¹` on `(0,π/2)` whose weighted
angular energy is integrable on `Iθ`, and `1 < γ`, one has

  `|u b - u a| ≤ √(A · 100/(γ-1)) · sin(2b)^{(γ-1)/2}`   for `0 < a ≤ b < π/4`,

with `A = ∫_{Iθ} (u')² sin(2·)^{2-γ}`.  This is the rate at which the slice is Cauchy at `0⁺`;
the hypothesis `hPow` is the elementary `sin`-power integral bound `SinPowIntegral`. -/
private lemma osc_bound {γ : ℝ} (hγ1 : 1 < γ) {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun σ => (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hPow : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ Real.pi / 4 →
      ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1)) :
    ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 4 →
      |u b - u a| ≤ Real.sqrt ((∫ σ in Work.Spaces.Iθ,
          (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) * (100 / (γ - 1)))
        * (Real.sin (2 * b)) ^ ((γ - 1) / 2) := by
  have hne0 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hγp : 0 < γ - 1 := by linarith
  -- the weighted energy, and its nonnegativity
  have hAnn : 0 ≤ ∫ σ in Work.Spaces.Iθ,
      (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) :=
    setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_core hσ) _)
  have hCnn : 0 ≤ 100 / (γ - 1) := by positivity
  intro a b ha hab hb
  have hb2 : b < Real.pi / 2 := by linarith [hb, Real.pi_pos]
  have hb4 : b ≤ Real.pi / 4 := le_of_lt hb
  have hb0 : 0 ≤ b := le_of_lt (lt_of_lt_of_le ha hab)
  -- the interval `[a,b]` sits strictly inside `(0,π/2)`
  have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb2⟩
  have hsubI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [← Set.uIcc_of_le hab]; exact hsub
  have hsinpos : ∀ s ∈ Set.uIcc a b, 0 < Real.sin (2 * s) := by
    intro s hs
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [(hsub hs).1])
      (by linarith [(hsub hs).2, Real.pi_pos])
  have hsincont : ∀ c : ℝ,
      ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc a b) := fun c =>
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun s hs => Or.inl (ne_of_gt (hsinpos s hs)))
  -- continuity, differentiability and the fundamental theorem of calculus on `[a,b]`
  have hcont : ContinuousOn u (Set.Icc a b) := hsm.continuousOn.mono hsubI
  have hpthcont : ContinuousOn (deriv u) (Set.uIcc a b) :=
    (hsm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt u (deriv u x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans ha hx.1, lt_of_lt_of_le hx.2 hb2.le⟩
    exact ((hsm.differentiableOn hne0).differentiableAt
      (isOpen_Ioo.mem_nhds hx')).hasDerivAt
  have hFTC : ∫ s in a..b, deriv u s = u b - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
      hpthcont.intervalIntegrable
  -- weighted Cauchy–Schwarz
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab
    (hpthcont.mul (hsincont ((2 - γ) / 2))) (hsincont ((γ - 2) / 2))
  -- the first Cauchy–Schwarz factor is at most the weighted energy `A`
  have hAint : ∫ s in a..b,
      (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) := by
    have hEq : ∫ s in a..b, (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2
        = ∫ s in a..b, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hsin : 0 < Real.sin (2 * s) := hsinpos s hs
      have h1 : ((Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2 = (Real.sin (2 * s)) ^ (2 - γ) := by
        rw [pow_two, ← Real.rpow_add hsin]
        congr 1
        ring
      rw [mul_pow, h1]
    rw [hEq]
    exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ ha hab hb2 hint
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_core hx) _))
  -- the second Cauchy–Schwarz factor is the `sin`-power weight bound
  have hBint : ∫ s in a..b, ((Real.sin (2 * s)) ^ ((γ - 2) / 2)) ^ 2
      ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by
    have hEq : ∫ s in a..b, ((Real.sin (2 * s)) ^ ((γ - 2) / 2)) ^ 2
        = ∫ s in a..b, (Real.sin (2 * s)) ^ (γ - 2) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hsin : 0 < Real.sin (2 * s) := hsinpos s hs
      rw [pow_two, ← Real.rpow_add hsin]
      congr 1
      ring
    rw [hEq]
    exact hPow (le_of_lt ha) hab hb4
  -- the two factors recombine into `u b - u a`
  have hprod : ∫ s in a..b,
      (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) * (Real.sin (2 * s)) ^ ((γ - 2) / 2)
      = u b - u a := by
    rw [← hFTC]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsin : 0 < Real.sin (2 * s) := hsinpos s hs
    rw [mul_assoc, ← Real.rpow_add hsin,
      show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  have hstep : |u b - u a| ≤ Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
      * Real.sqrt ((100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1)) := by
    rw [← hprod]
    exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- collect the two square roots into the single factor `√(A·100/(γ-1)) · sin(2b)^{(γ-1)/2}`
  refine hstep.trans (le_of_eq ?_)
  have hs0 : 0 ≤ Real.sin (2 * b) :=
    sin_two_nonneg_Iθ_core ⟨hb0, by linarith [hb, Real.pi_pos]⟩
  have hsqrt : Real.sqrt ((Real.sin (2 * b)) ^ (γ - 1)) = (Real.sin (2 * b)) ^ ((γ - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs0]
    congr 1
    ring
  calc Real.sqrt (∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
        * Real.sqrt ((100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1))
      = Real.sqrt (∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (Real.sqrt (100 / (γ - 1)) * Real.sqrt ((Real.sin (2 * b)) ^ (γ - 1))) := by
        rw [Real.sqrt_mul hCnn]
    _ = (Real.sqrt (∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * Real.sqrt (100 / (γ - 1))) * Real.sqrt ((Real.sin (2 * b)) ^ (γ - 1)) := by ring
    _ = Real.sqrt ((∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (100 / (γ - 1))) * Real.sqrt ((Real.sin (2 * b)) ^ (γ - 1)) := by
        rw [Real.sqrt_mul hAnn]
    _ = Real.sqrt ((∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (100 / (γ - 1))) * (Real.sin (2 * b)) ^ ((γ - 1) / 2) := by rw [hsqrt]

theorem SliceTraceO {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi/2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∃ mu : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      (u θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
        * ∫ σ in Work.Spaces.Iθ,
            (deriv u σ)^2 * (Real.sin (2*σ))^(2 - Work.Spaces.gam α) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hg1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hg2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hgp : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  -- the weighted energy
  set A : ℝ := ∫ σ in Work.Spaces.Iθ,
      (deriv u σ)^2 * (Real.sin (2*σ))^(2 - Work.Spaces.gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_core hσ) _)
  have hKnn : 0 ≤ A * (100 / (Work.Spaces.gam α - 1)) :=
    mul_nonneg hAnn (by positivity)
  -- the oscillation estimate
  have hcore := osc_bound (γ := Work.Spaces.gam α) hg1 hsm hint
    (fun {a b} ha hab hb => SinPowIntegral hg1 hg2 ha hab hb)
  rw [← hAdef] at hcore
  -- the trace and its rate
  obtain ⟨mu, hmu, hbd⟩ := TraceOfOsc (u := u) (γ := Work.Spaces.gam α)
    (K := Real.sqrt (A * (100 / (Work.Spaces.gam α - 1)))) hgp (Real.sqrt_nonneg _) hcore
  refine ⟨mu, hmu, fun θ hθ => ?_⟩
  have h := hbd θ hθ
  rw [Real.sq_sqrt hKnn] at h
  calc (u θ - mu)^2
      ≤ (A * (100 / (Work.Spaces.gam α - 1)))
          * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) := h
    _ = 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) * A := by ring

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev

open MeasureTheory

set_option maxHeartbeats 2000000

/-!
# `holder_half_of_W22`

`‖v‖_{C^{0,1/2}} ≤ C (‖v‖_{L²} + ‖D²v‖_{L²})` for `v : ℝ × ℝ → ℝ` of class `C²` with compact
support (the critical 2-dimensional Sobolev embedding `W^{2,2}(ℝ²) ⊂ C^{0,1/2}`).

The proof is assembled from four independent estimates, each stated separately:

* `nash_2d`      : `∫ u⁴ ≤ 4 (∫u²)(∫‖∇u‖²)` (2-D Nash, obtained from the 1-D Agmon inequality
  `one_dim_agmon` by slicing);
* `grad_L2_le`   : `∫‖∇v‖² ≤ 4 √(∫v²) √(∫‖D²v‖²)` (integration by parts);
* `segment_integral` : the FTC along a segment;
* `holder_half_of_L4` : the 2-D Morrey estimate `|v p - v q| ≤ 4 (∫‖∇v‖⁴)^{1/4} √(dist p q)`,
  proved by averaging the segment identity over a ball.

Here we combine them.
-/

/-- `Integrable` for `x ↦ ‖fderiv ℝ v x‖ ^ k`, `k ≠ 0`, when `v` is `C²` with compact support. -/
private lemma integrable_norm_fderiv_pow {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ k) := by
  have hcont : Continuous (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ k) :=
    (hv.continuous_fderiv (by simp)).norm.pow k
  have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ k) :=
    (HasCompactSupport.fderiv ℝ hc).comp_left
      (g := fun L : ℝ × ℝ →L[ℝ] ℝ => ‖L‖ ^ k) (by simp [zero_pow hk])
  exact hcont.integrable_of_hasCompactSupport hcs

/-- `(|a| + |b|)^4 ≤ 8 (a^4 + b^4)`. -/
private lemma add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]

/-- `|a| ^ 4 = a ^ 4`. -/
private lemma abs_pow_four (a : ℝ) : |a| ^ 4 = a ^ 4 := by
  rw [show (|a| : ℝ) ^ 4 = (|a| ^ 2) ^ 2 by ring, sq_abs, show (a ^ 2) ^ 2 = a ^ 4 by ring]

/-- For a linear functional on `ℝ × ℝ` (with the sup norm on the domain) the operator norm is
bounded by the sum of the absolute values of its two partial components. -/
private lemma opNorm_le_abs_sum (L : ℝ × ℝ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (1, 0)| + |L (0, 1)| := by
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro h
  have hL : L h = h.1 * L (1, 0) + h.2 * L (0, 1) := by
    conv_lhs => rw [show h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hL, Real.norm_eq_abs]
  calc |h.1 * L (1, 0) + h.2 * L (0, 1)|
      ≤ |h.1 * L (1, 0)| + |h.2 * L (0, 1)| := abs_add_le _ _
    _ = |h.1| * |L (1, 0)| + |h.2| * |L (0, 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖h‖ * |L (1, 0)| + ‖h‖ * |L (0, 1)| := by
        gcongr
        · simpa [Real.norm_eq_abs] using norm_fst_le h
        · simpa [Real.norm_eq_abs] using norm_snd_le h
    _ = (|L (1, 0)| + |L (0, 1)|) * ‖h‖ := by ring

/-- **Assembly.**  Given the four estimates (`nash_2d`, `grad_L2_le`, `segment_integral`,
`holder_half_of_L4`) the critical Sobolev embedding follows with the universal constant `16`. -/
theorem holder_half_of_W22_aux
    (hnash : ∀ (u : ℝ × ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u →
      ∫ x : ℝ × ℝ, (u x) ^ 4 ≤ 4 * (∫ x : ℝ × ℝ, (u x) ^ 2) *
        (∫ x : ℝ × ℝ, ‖fderiv ℝ u x‖ ^ 2))
    (hibp : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 2 w → HasCompactSupport w →
      ∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 2 ≤ 4 * Real.sqrt (∫ x : ℝ × ℝ, (w x) ^ 2)
        * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ w) x‖ ^ 2))
    (hseg : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → ∀ p z : ℝ × ℝ,
      w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p))
    (hl4 : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → HasCompactSupport w →
      (∀ p z : ℝ × ℝ, w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p)) →
      ∀ p q : ℝ × ℝ, |w p - w q| ≤ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 4) ^ (1 / 4 : ℝ)
        * Real.sqrt (dist p q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * Real.sqrt (dist p q) := by
  refine ⟨16, by norm_num, ?_⟩
  intro v hv hc p q
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  set α : ℝ := Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) with hαdef
  set β : ℝ := Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) with hβdef
  set G4 : ℝ := ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4 with hG4def
  have hα0 : 0 ≤ α := by rw [hαdef]; exact Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := by rw [hβdef]; exact Real.sqrt_nonneg _
  have hG0 : 0 ≤ G4 := by
    rw [hG4def]; exact integral_nonneg fun x => by positivity
  -- `∫‖∇v‖² ≤ 4 α β`
  have hgrad : ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 ≤ 4 * α * β := by
    have h := hibp v hv hc
    rw [hαdef, hβdef]
    linarith [h]
  -- the two partial derivatives of `v` as scalar functions
  set u1 : ℝ × ℝ → ℝ := fun x => fderiv ℝ v x (1, 0) with hu1def
  set u2 : ℝ × ℝ → ℝ := fun x => fderiv ℝ v x (0, 1) with hu2def
  have hcd1 : ContDiff ℝ 1 u1 := by
    rw [hu1def]
    exact ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const :
      ContDiff ℝ 1 fun x : ℝ × ℝ => fderiv ℝ v x (1, 0))
  have hcd2 : ContDiff ℝ 1 u2 := by
    rw [hu2def]
    exact ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const :
      ContDiff ℝ 1 fun x : ℝ × ℝ => fderiv ℝ v x (0, 1))
  have hc1 : HasCompactSupport u1 := by
    rw [hu1def]; exact hc.fderiv_apply ℝ (1, 0)
  have hc2 : HasCompactSupport u2 := by
    rw [hu2def]; exact hc.fderiv_apply ℝ (0, 1)
  have hint1 : Integrable (fun x : ℝ × ℝ => (u1 x) ^ 4) :=
    (hcd1.continuous.pow 4).integrable_of_hasCompactSupport
      (hc1.comp_left (zero_pow (by norm_num : (4 : ℕ) ≠ 0)))
  have hint2 : Integrable (fun x : ℝ × ℝ => (u2 x) ^ 4) :=
    (hcd2.continuous.pow 4).integrable_of_hasCompactSupport
      (hc2.comp_left (zero_pow (by norm_num : (4 : ℕ) ≠ 0)))
  have hu1_le : ∀ x : ℝ × ℝ, |u1 x| ≤ ‖fderiv ℝ v x‖ := by
    intro x
    rw [hu1def]
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ v x) ((1, 0) : ℝ × ℝ)
    simpa using h
  have hu2_le : ∀ x : ℝ × ℝ, |u2 x| ≤ ‖fderiv ℝ v x‖ := by
    intro x
    rw [hu2def]
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ v x) ((0, 1) : ℝ × ℝ)
    simpa using h
  have hfderiv_u1_le : ∀ x : ℝ × ℝ,
      ‖fderiv ℝ u1 x‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro x
    have hdiff : DifferentiableAt ℝ (fderiv ℝ v) x :=
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
    have hz : fderiv ℝ (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) x = 0 :=
      fderiv_const_apply ((1, 0) : ℝ × ℝ)
    rw [hu1def, fderiv_clm_apply hdiff (differentiableAt_const ((1, 0) : ℝ × ℝ)), hz]
    simp only [ContinuousLinearMap.comp_zero, zero_add]
    calc ‖(fderiv ℝ (fderiv ℝ v) x).flip ((1, 0) : ℝ × ℝ)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ v) x).flip‖ * ‖((1, 0) : ℝ × ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ v) x‖ := by rw [ContinuousLinearMap.opNorm_flip]; simp
  have hfderiv_u2_le : ∀ x : ℝ × ℝ,
      ‖fderiv ℝ u2 x‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro x
    have hdiff : DifferentiableAt ℝ (fderiv ℝ v) x :=
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
    have hz : fderiv ℝ (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) x = 0 :=
      fderiv_const_apply ((0, 1) : ℝ × ℝ)
    rw [hu2def, fderiv_clm_apply hdiff (differentiableAt_const ((0, 1) : ℝ × ℝ)), hz]
    simp only [ContinuousLinearMap.comp_zero, zero_add]
    calc ‖(fderiv ℝ (fderiv ℝ v) x).flip ((0, 1) : ℝ × ℝ)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ v) x).flip‖ * ‖((0, 1) : ℝ × ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ v) x‖ := by rw [ContinuousLinearMap.opNorm_flip]; simp
  have hDv2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 2) :=
    integrable_norm_fderiv_pow hv hc 2 (by norm_num)
  have hD2v2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
    have h2 : HasCompactSupport (fderiv ℝ (fderiv ℝ v)) :=
      HasCompactSupport.fderiv ℝ (HasCompactSupport.fderiv ℝ hc)
    have hg : (fun L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) => ‖L‖ ^ 2)
        (0 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) = 0 := by
      show ‖(0 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ))‖ ^ 2 = 0
      rw [ContinuousLinearMap.opNorm_zero]; norm_num
    have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) :=
      h2.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) => ‖L‖ ^ 2) hg
    exact ((h1.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport hcs
  -- `∫ u₁² ≤ ∫‖∇v‖²` and `∫ u₂² ≤ ∫‖∇v‖²`
  have hu1s : ∫ x : ℝ × ℝ, (u1 x) ^ 2 ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hDv2
    filter_upwards with x
    calc (u1 x) ^ 2 = |u1 x| ^ 2 := by rw [sq_abs]
      _ ≤ ‖fderiv ℝ v x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hu1_le x) 2
  have hu2s : ∫ x : ℝ × ℝ, (u2 x) ^ 2 ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hDv2
    filter_upwards with x
    calc (u2 x) ^ 2 = |u2 x| ^ 2 := by rw [sq_abs]
      _ ≤ ‖fderiv ℝ v x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hu2_le x) 2
  -- `∫‖∇u₁‖² ≤ ∫‖D²v‖²` and `∫‖∇u₂‖² ≤ ∫‖D²v‖²`
  have hu1d : ∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2
      ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hD2v2
    filter_upwards with x
    exact pow_le_pow_left₀ (by positivity) (hfderiv_u1_le x) 2
  have hu2d : ∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2
      ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hD2v2
    filter_upwards with x
    exact pow_le_pow_left₀ (by positivity) (hfderiv_u2_le x) 2
  have hβsq : β ^ 2 = ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    rw [hβdef, Real.sq_sqrt]
    exact integral_nonneg fun x => by positivity
  -- the `L⁴` bounds on the two partial derivatives
  have h14 : ∫ x : ℝ × ℝ, (u1 x) ^ 4 ≤ 16 * α * β ^ 3 := by
    have h := hnash u1 hcd1 hc1
    have h1 : ∫ x : ℝ × ℝ, (u1 x) ^ 2 ≤ 4 * α * β := hu1s.trans hgrad
    have h2 : ∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2 ≤ β ^ 2 := hu1d.trans_eq hβsq.symm
    have hb : (0 : ℝ) ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2 := integral_nonneg fun x => by positivity
    calc ∫ x : ℝ × ℝ, (u1 x) ^ 4
        ≤ 4 * (∫ x : ℝ × ℝ, (u1 x) ^ 2) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2) := h
      _ ≤ 4 * (4 * α * β) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hb
      _ ≤ 4 * (4 * α * β) * β ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * α * β ^ 3 := by ring
  have h24 : ∫ x : ℝ × ℝ, (u2 x) ^ 4 ≤ 16 * α * β ^ 3 := by
    have h := hnash u2 hcd2 hc2
    have h1 : ∫ x : ℝ × ℝ, (u2 x) ^ 2 ≤ 4 * α * β := hu2s.trans hgrad
    have h2 : ∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2 ≤ β ^ 2 := hu2d.trans_eq hβsq.symm
    have hb : (0 : ℝ) ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2 := integral_nonneg fun x => by positivity
    calc ∫ x : ℝ × ℝ, (u2 x) ^ 4
        ≤ 4 * (∫ x : ℝ × ℝ, (u2 x) ^ 2) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2) := h
      _ ≤ 4 * (4 * α * β) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hb
      _ ≤ 4 * (4 * α * β) * β ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * α * β ^ 3 := by ring
  -- `∫‖∇v‖⁴ ≤ 8 (∫u₁⁴ + ∫u₂⁴)`
  have hG4le : G4 ≤ 256 * α * β ^ 3 := by
    have hInt8 : Integrable (fun x : ℝ × ℝ => 8 * ((u1 x) ^ 4 + (u2 x) ^ 4)) :=
      (hint1.add hint2).const_mul 8
    have hpt : ∀ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4 ≤ 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := by
      intro x
      have h1 : ‖fderiv ℝ v x‖ ≤ |u1 x| + |u2 x| := by
        rw [hu1def, hu2def]; exact opNorm_le_abs_sum _
      calc ‖fderiv ℝ v x‖ ^ 4 ≤ (|u1 x| + |u2 x|) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h1 4
        _ ≤ 8 * (|u1 x| ^ 4 + |u2 x| ^ 4) := add_pow_four_le _ _
        _ = 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := by rw [abs_pow_four, abs_pow_four]
    have hmono : ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4
        ≤ ∫ x : ℝ × ℝ, 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hInt8
      filter_upwards with x
      exact hpt x
    rw [hG4def]
    calc ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4
        ≤ ∫ x : ℝ × ℝ, 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := hmono
      _ = 8 * ((∫ x : ℝ × ℝ, (u1 x) ^ 4) + (∫ x : ℝ × ℝ, (u2 x) ^ 4)) := by
          rw [integral_const_mul, integral_add hint1 hint2]
      _ ≤ 8 * (16 * α * β ^ 3 + 16 * α * β ^ 3) := by gcongr
      _ = 256 * α * β ^ 3 := by ring
  -- hence `G4 ≤ 256 (α + β)⁴`
  have hG4le' : G4 ≤ 256 * (α + β) ^ 4 := by
    have hα' : α ≤ α + β := le_add_of_nonneg_right hβ0
    have hβ' : β ≤ α + β := le_add_of_nonneg_left hα0
    have h1 : α * β ^ 3 ≤ (α + β) ^ 4 := by
      calc α * β ^ 3 ≤ (α + β) * (α + β) ^ 3 := by
            apply mul_le_mul hα' (pow_le_pow_left₀ hβ0 hβ' 3) (by positivity) (by positivity)
        _ = (α + β) ^ 4 := by ring
    have h2 : 256 * α * β ^ 3 ≤ 256 * (α + β) ^ 4 := by
      calc 256 * α * β ^ 3 = 256 * (α * β ^ 3) := by ring
        _ ≤ 256 * (α + β) ^ 4 := mul_le_mul_of_nonneg_left h1 (by norm_num)
    exact hG4le.trans h2
  -- the fourth root
  have hP : G4 ^ (1 / 4 : ℝ) ≤ 4 * (α + β) := by
    have h256 : ((256 : ℝ) ^ (1 / 4 : ℝ)) = 4 := by
      rw [show (256 : ℝ) = (4 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast (4 : ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have hfour : (((α + β) ^ 4 : ℝ) ^ (1 / 4 : ℝ)) = α + β := by
      rw [← Real.rpow_natCast (α + β) 4, ← Real.rpow_mul (by positivity)]
      norm_num
    calc G4 ^ (1 / 4 : ℝ) ≤ (256 * (α + β) ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hG0 hG4le' (by norm_num)
      _ = 4 * (α + β) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), h256, hfour]
  have hmor : |v p - v q| ≤ 4 * G4 ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := by
    have h := hl4 v hv1 hc (hseg v hv1) p q
    rw [hG4def]
    exact h
  have hd0 : 0 ≤ Real.sqrt (dist p q) := Real.sqrt_nonneg _
  calc |v p - v q| ≤ 4 * G4 ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := hmor
    _ ≤ 4 * (4 * (α + β)) * Real.sqrt (dist p q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) hd0
    _ = 16 * (α + β) * Real.sqrt (dist p q) := by ring
    _ = 16 * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * Real.sqrt (dist p q) := by
        rw [hαdef, hβdef]

/-- The (intended) Hölder form with an explicit real exponent: this is the statement that the
name `holder_half_of_W22` describes, and it is the one downstream users should consume. -/
theorem holder_half_of_W22_aux_rpow
    (hnash : ∀ (u : ℝ × ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u →
      ∫ x : ℝ × ℝ, (u x) ^ 4 ≤ 4 * (∫ x : ℝ × ℝ, (u x) ^ 2) *
        (∫ x : ℝ × ℝ, ‖fderiv ℝ u x‖ ^ 2))
    (hibp : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 2 w → HasCompactSupport w →
      ∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 2 ≤ 4 * Real.sqrt (∫ x : ℝ × ℝ, (w x) ^ 2)
        * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ w) x‖ ^ 2))
    (hseg : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → ∀ p z : ℝ × ℝ,
      w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p))
    (hl4 : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → HasCompactSupport w →
      (∀ p z : ℝ × ℝ, w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p)) →
      ∀ p q : ℝ × ℝ, |w p - w q| ≤ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 4) ^ (1 / 4 : ℝ)
        * Real.sqrt (dist p q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, H⟩ := holder_half_of_W22_aux hnash hibp hseg hl4
  refine ⟨C, hC, fun v hv hc p q => ?_⟩
  rw [← Real.sqrt_eq_rpow (dist p q)]
  exact H v hv hc p q

/-- The `(1/2)`-Hölder estimate in its clean public form: this is what the name
`holder_half_of_W22` describes and what downstream consumers should use.  (The binder
`dist p q ^ (1 / 2)` of the request elaborates with a **natural-number** exponent — Mathlib
reads `1 / 2 : ℕ` as `0`, so `dist p q ^ (1 / 2) = 1` — hence the request as written is the
*uniform* bound, proved below as `holder_half_of_W22`; the honest Hölder statement is this
one.) -/
theorem holder_half_of_W22_real :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) :=
  holder_half_of_W22_aux_rpow
    (fun u hu hc => HolderHalf.nash_2d hu hc
      (fun f hf hcf y => HolderHalf.one_dim_agmon hf hcf y))
    (fun w hw hw' => HolderHalf.grad_L2_le hw hw')
    (fun w hw p z => HolderHalf.segment_integral hw p z)
    (fun w hw hw' hs p q => HolderHalf.holder_half_of_L4 hw hw' hs p q)


end Work.FTS.StrongLWP.Sobolev
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false

/-! ## §1 The two functions and their identification with the angular moment -/

/-- The angular moment `FK (Fstar α)` of the fundamental profile, written out:
`z ↦ α · 2z/(1+z)²`, constant in `θ`. -/
def KsFun (α : ℝ) : ℝ → ℝ → ℝ := fun z _ => α * (2 * z / (1 + z) ^ 2)

/-- `sin²θ · FK (Fstar α)`. -/
def KsTor (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * KsFun α z θ



/-! ## §2 Factors which are constant in one variable -/

/-- A factor which does not depend on `z` passes through `∂_z`. -/
theorem pz_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field (c θ)

/-- A factor which does not depend on `z` passes through `∂_z^j`. -/
theorem pzIter_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
      have heq : Work.Spaces.pzIter j (fun z θ => c θ * K z θ)
          = fun z θ => c θ * Work.Spaces.pzIter j K z θ :=
        funext fun z => funext fun θ => ih z θ
      rw [heq, pz_const_mul]

/-- A factor which does not depend on `z` passes through `D_z^j`. -/
theorem DzIter_const_mul_apply (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.DzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
      have heq : Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
          = fun z θ => c θ * Work.Spaces.DzIter j K z θ :=
        funext fun z => funext fun θ => ih z θ
      rw [heq]
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field (c θ) (v := fun z' => Work.Spaces.DzIter j K z' θ)]
      ring

/-- The `θ`-factor passes through the `D_θ`-iterates of a product of a `θ`-only and a
`z`-only factor. -/
theorem DthIter_sep_apply (a : ℝ → ℝ) (K : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter j (fun z θ => a θ * K z) z θ = Work.Spaces.dthU^[j] a θ * K z := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ]
      have heq : Work.Spaces.DthIter j (fun z θ => a θ * K z)
          = fun z θ => Work.Spaces.dthU^[j] a θ * K z :=
        funext fun z => funext fun θ => ih z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq]
      rw [deriv_mul_const_field (K z) (u := Work.Spaces.dthU^[j] a)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.dthU]
      ring

/-! ## §3 The radial derivatives of `KsFun` -/

/-- `∂_z^k` of a constant multiple of `hKer = z/(1+z)²`. -/
theorem pzIter_zOnly_mul (c : ℝ) (K : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z (_ : ℝ) => c * K z) = fun z _ => c * deriv^[k] K z := by
  induction k with
  | zero => funext z θ; simp
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz]
      rw [deriv_const_mul_field c (v := deriv^[k] K), Function.iterate_succ_apply']

/-- `∂_z^k KsFun α = 2α · hKer^{(k)}`. -/
theorem pzIter_KsFun (α : ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (KsFun α) = fun z _ => α * 2 * deriv^[k] Work.Spaces.hKer z := by
  have h : KsFun α = fun z _ => (α * 2) * Work.Spaces.hKer z := by
    funext z θ
    simp only [KsFun, Work.Spaces.hKer_apply]
    ring
  rw [h, pzIter_zOnly_mul]

/-- The `𝒲^{6,∞}`-shape of the radial derivatives of `KsFun`:
`|(z+1)^k ∂_z^k Ks| ≤ 2α · k! · (k+1)` for `z ≥ 0`. -/
theorem ks_pz_bound (α : ℝ) (hα : 0 ≤ α) (k : ℕ) (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ|
      ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) := by
  rw [pzIter_KsFun]
  have h := Work.Spaces.pzIter_hKer_bound k z hz
  have hEq : (z + 1) ^ k * (α * 2 * deriv^[k] Work.Spaces.hKer z)
      = (α * 2) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) := by ring
  rw [hEq, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ α * 2)]
  calc α * 2 * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ α * 2 * ((k.factorial : ℝ) * (k + 1)) := mul_le_mul_of_nonneg_left h (by linarith)
    _ = 2 * α * ((k.factorial : ℝ) * (k + 1)) := by ring

/-- The `z^k`-shape of the radial derivatives of `KsFun`:
`|z^k ∂_z^k Ks| ≤ 2α · k! · (k+1) · (z/(1+z))^k` for `z ≥ 0`. -/
theorem ks_zpow_pz_bound (α : ℝ) (hα : 0 ≤ α) (k : ℕ) (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) :
    |z ^ k * Work.Spaces.pzIter k (KsFun α) z θ|
      ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) * (z / (1 + z)) ^ k := by
  rw [pzIter_KsFun]
  have h := Work.Spaces.pzIter_hKer_bound k z hz
  have hz1 : (1 + z : ℝ) ≠ 0 := by positivity
  have hr : 0 ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hsplit : z ^ k = (z + 1) ^ k * (z / (1 + z)) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  have hEq : z ^ k * (α * 2 * deriv^[k] Work.Spaces.hKer z)
      = (α * 2) * ((z / (1 + z)) ^ k * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)) := by
    rw [hsplit]; ring
  rw [hEq, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ α * 2), abs_mul,
    abs_of_nonneg (pow_nonneg hr k)]
  calc α * 2 * ((z / (1 + z)) ^ k * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|)
      ≤ α * 2 * ((z / (1 + z)) ^ k * ((k.factorial : ℝ) * (k + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (pow_nonneg hr k)) (by linarith)
    _ = 2 * α * ((k.factorial : ℝ) * (k + 1)) * (z / (1 + z)) ^ k := by ring

/-- `k! · (k+1) ≤ 5040` for `k ≤ 6`. -/
theorem fact_mul_le_5040 (k : ℕ) (hk : k ≤ 6) : (k.factorial : ℝ) * (k + 1) ≤ 5040 := by
  interval_cases k <;> norm_num

/-- `r^k ≤ r` for `0 ≤ r ≤ 1` and `k ≥ 1`. -/
theorem pow_nat_le_self {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) {k : ℕ} (hk : 1 ≤ k) : r ^ k ≤ r := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  calc r ^ m * r ≤ 1 * r := mul_le_mul_of_nonneg_right (pow_le_one₀ hr hr1) hr
    _ = r := one_mul r

/-- The uniform pointwise bound `|z^k ∂_z^k Ks| ≤ 2·5040·α·z/(1+z)` for `k ≤ 6`, `z ≥ 0`:
this is the shape consumed by the Stirling expansion of `D_z^j`. -/
theorem ks_zpow_pz_le (α : ℝ) (hα : 0 ≤ α) (k : ℕ) (hk : k ≤ 6) (z : ℝ) (hz : 0 ≤ z)
    (θ : ℝ) :
    |z ^ k * Work.Spaces.pzIter k (KsFun α) z θ| ≤ 2 * 5040 * α * (z / (1 + z)) := by
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hr : 0 ≤ z / (1 + z) := div_nonneg hz (le_of_lt hz1)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pzIter_KsFun]
    simp only [pow_zero, one_mul]
    have hid : (2 : ℝ) * z / (1 + z) ^ 2 = ((2 : ℝ) * (z / (1 + z))) / (1 + z) := by
      field_simp
    have hle : ((2 : ℝ) * (z / (1 + z))) / (1 + z) ≤ 2 * (z / (1 + z)) := by
      rw [div_le_iff₀ hz1]
      nlinarith [hr, hz, mul_nonneg hr hz]
    calc |α * 2 * deriv^[0] Work.Spaces.hKer z| = α * ((2 : ℝ) * z / (1 + z) ^ 2) := by
          rw [Function.iterate_zero, id_eq, Work.Spaces.hKer_apply]
          rw [abs_of_nonneg (by positivity)]
          ring
      _ = α * (((2 : ℝ) * (z / (1 + z))) / (1 + z)) := by rw [hid]
      _ ≤ α * (2 * (z / (1 + z))) := mul_le_mul_of_nonneg_left hle hα
      _ ≤ 2 * 5040 * α * (z / (1 + z)) := by
          have h : (0:ℝ) ≤ α * (z / (1 + z)) := mul_nonneg hα hr
          nlinarith [h]
  · have h1 := ks_zpow_pz_bound α hα k z hz θ
    have h2 := pow_nat_le_self hr ((div_le_one hz1).mpr (by linarith)) hkpos
    have h3 := fact_mul_le_5040 k hk
    have h5 : 2 * α * ((k.factorial : ℝ) * (k + 1)) * (z / (1 + z)) ^ k
        ≤ 2 * α * 5040 * (z / (1 + z)) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by linarith)) (pow_nonneg hr k)
    have h6 : 2 * α * 5040 * (z / (1 + z)) ^ k ≤ 2 * α * 5040 * (z / (1 + z)) :=
      mul_le_mul_of_nonneg_left h2 (by nlinarith)
    linarith [h1, h5, h6,
      show (2:ℝ) * 5040 * α * (z / (1 + z)) = 2 * α * 5040 * (z / (1 + z)) by ring]

/-- The Bell number of a row `n ≤ 6` is at most `203`. -/
theorem bell_le_203 (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 203 := by
  interval_cases n <;> decide

/-! ## §4 The pointwise bound for `D_z^j KsFun` -/

/-- The `z`-slices of `KsFun α` are analytic on `(-1,∞)`.  This is the smoothness
hypothesis of the Stirling expansion `Work.Spaces.DzIter_eq_sum_scoef`. -/
theorem analytic_zSlice_KsFun (α : ℝ) (θ : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => KsFun α z θ) (Set.Ioi (-1)) := by
  have hfun : (fun z : ℝ => KsFun α z θ) = fun z : ℝ => α * (2 * z / (1 + z) ^ 2) := by
    funext z; rfl
  rw [hfun]
  have hden : ∀ x : ℝ, x ∈ Set.Ioi (-1) → (1 + x) ^ 2 ≠ 0 := by
    intro x hx
    have h1 : (-1 : ℝ) < x := hx
    have h2 : (0 : ℝ) < 1 + x := by linarith
    positivity
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
    refine ContDiffOn.div ?_ ?_ hden
    · fun_prop
    · fun_prop
  have h2 := h.mul (contDiffOn_const (c := α) (s := Set.Ioi (-1)))
  have h3 : (fun x : ℝ => 2 * x / (1 + x) ^ 2 * α)
      = (fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) := by
    funext p; ring
  rwa [h3] at h2

/-- **The pointwise `D_z`-bound for the radial function `KsFun α`**:
`|D_z^j Ks| ≤ 2·5040·203·α·z/(1+z)` for every `j ≤ 6`, `z ≥ 0`. -/
theorem ks_Dz_bound (α : ℝ) (hα : 0 ≤ α) (j : ℕ) (hj : j ≤ 6) (z : ℝ) (hz : 0 ≤ z) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DzIter j (KsFun α) z θ| ≤ 2 * 5040 * 203 * α * (z / (1 + z)) := by
  have hstir := Work.Spaces.DzIter_eq_sum_scoef (h := KsFun α)
    (fun θ _ => analytic_zSlice_KsFun α θ) j z
      (by simp only [Set.mem_Ioi]; linarith [hz]) θ hθ
  rw [hstir]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le j (2 * 5040 * α * (z / (1 + z)))
    (fun k => z ^ k * Work.Spaces.pzIter k (KsFun α) z θ)
    (fun k hk => ks_zpow_pz_le α hα k (le_trans hk hj) z hz θ)
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 203 := by exact_mod_cast bell_le_203 j hj
  have hM : 0 ≤ 2 * 5040 * α * (z / (1 + z)) := by
    have : 0 ≤ α * (z / (1 + z)) := mul_nonneg hα (div_nonneg hz (by linarith))
    nlinarith [this]
  calc |∑ k ∈ Finset.range (j + 1),
        (Work.Spaces.scoef j k : ℝ) * (z ^ k * Work.Spaces.pzIter k (KsFun α) z θ)|
      ≤ (Work.Spaces.bell j : ℝ) * (2 * 5040 * α * (z / (1 + z))) := hsum
    _ ≤ 203 * (2 * 5040 * α * (z / (1 + z))) := mul_le_mul_of_nonneg_right hbell hM
    _ = 2 * 5040 * 203 * α * (z / (1 + z)) := by ring

/-! ## §5 The angular derivatives -/

/-- A `D_θ`-iterate of a constant (for `j ≥ 1`) vanishes. -/
theorem dthU_iter_const_eq_zero (c : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.dthU^[j] (fun _ : ℝ => c) = fun _ => 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  clear hj
  induction m with
  | zero =>
      funext θ
      show Real.sin (2 * θ) * deriv (fun _ : ℝ => c) θ = 0
      rw [deriv_const]
      ring
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Function.iterate_succ_apply', ih]
      funext θ
      show Real.sin (2 * θ) * deriv (fun _ : ℝ => (0:ℝ)) θ = 0
      rw [deriv_const]
      ring

/-- `KsFun α` is constant in `θ`, so all its `D_θ`-iterates of positive order vanish. -/
theorem DthIter_KsFun_eq_zero (α : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.DthIter j (KsFun α) = fun _ _ => 0 := by
  have hfun : KsFun α = fun z (_ : ℝ) => (1 : ℝ) * (fun z => KsFun α z 0) z := by
    funext z θ; simp [KsFun]
  rw [hfun]
  funext z θ
  rw [DthIter_sep_apply (a := fun _ : ℝ => (1 : ℝ)) (K := fun z => KsFun α z 0)]
  rw [dthU_iter_const_eq_zero (1 : ℝ) hj]
  simp

/-- The `D_θ`-iterates of `KsTor α` factor as `D_θ^j(sin²) · KsFun`. -/
theorem DthIter_KsTor (α : ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter j (KsTor α) z θ
      = Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ * KsFun α z θ := by
  have h : KsTor α = fun z θ => (fun t : ℝ => Real.sin t ^ 2) θ * (fun z => KsFun α z 0) z := by
    funext z θ; simp [KsTor, KsFun]
  rw [h, DthIter_sep_apply]
  simp only [KsFun]

/-- The mixed derivatives of `KsTor α` factor as `D_θ^j(sin²)(θ) · ∂_z^k KsFun α`. -/
theorem pzIter_DthIter_KsTor (α : ℝ) (j k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
      = Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
        * Work.Spaces.pzIter k (KsFun α) z θ := by
  have h : Work.Spaces.DthIter j (KsTor α)
      = fun z θ => (fun t : ℝ => Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) t) θ
          * KsFun α z θ := by
    funext z θ
    exact DthIter_KsTor α j z θ
  rw [h, pzIter_const_mul]

/-- The `∂_z^k`-iterates of `KsTor α` factor as `sin²θ · ∂_z^k KsFun`. -/
theorem pzIter_KsTor (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (KsTor α) z θ
      = Real.sin θ ^ 2 * Work.Spaces.pzIter k (KsFun α) z θ := by
  have h : KsTor α = fun z θ => (fun t : ℝ => Real.sin t ^ 2) θ * KsFun α z θ := rfl
  rw [h, pzIter_const_mul]

/-- The weighted endpoint bound for the `D_θ`-iterates of `sin²` (from
`Npair6SupAux.dthU_sinSq_weight`), in the form used by the pointwise estimates:
on the *open* angular interval,
`|D_θ^j(sin²)(θ)| ≤ C · (α + sin 2θ) · sin(2θ)^{α/5}`. -/
theorem dthU_sinSq_weighted : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ j : ℕ, 1 ≤ j → j ≤ 6 →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        ≤ C * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight
  refine ⟨C, hCpos, fun α hαI j hj1 hj6 θ hθ => ?_⟩
  obtain ⟨hα, hα1⟩ := hαI
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hb := hC α hα hα1 j hj1 hj6 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hfac : 0 < (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_pos hden (Real.rpow_pos_of_pos hs _)
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt hfac)
  have hid : |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by
    have h1 : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    have h2 : (α + Real.sin (2 * θ))⁻¹ * (α + Real.sin (2 * θ)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hden)
    rw [div_eq_mul_inv]
    calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          * (Real.sin (2 * θ)) ^ (-(α / 5)) * (α + Real.sin (2 * θ))⁻¹
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5))
          * ((α + Real.sin (2 * θ))⁻¹ * (α + Real.sin (2 * θ))) := by ring
      _ = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by rw [h1, h2]; ring
  rw [hid] at hmul
  calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
      ≤ C * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := hmul
    _ = C * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := rfl

/-! ## §6 Smoothness on the open quadrant -/

/-- `KsFun α` is `C^∞` on the open quadrant. -/
theorem SmoothOpen_KsFun (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (KsFun α) := by
  have hfun : Function.uncurry (KsFun α)
      = fun p : ℝ × ℝ => α * (2 * p.1 / (1 + p.1) ^ 2) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  have hden : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    positivity
  have h : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.div ?_ ?_ hden
    · fun_prop
    · fun_prop
  have h2 := h.mul (contDiffOn_const (c := α) (s := Work.FTS.EllipticEst.Q0))
  refine h2.congr (fun p hp => ?_)
  simp only [div_eq_mul_inv]
  ring

/-- `sin²θ · KsFun α` is `C^∞` on the open quadrant. -/
theorem SmoothOpen_KsTor (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (KsTor α) := by
  have hun : Function.uncurry (KsTor α)
      = fun p : ℝ × ℝ => Real.sin p.2 ^ 2 * (α * (2 * p.1 / (1 + p.1) ^ 2)) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hun]
  have hden : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    positivity
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0 := by
    fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (2 * p.1 / (1 + p.1) ^ 2)) Work.FTS.EllipticEst.Q0 := by
    have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div ?_ ?_ hden
      · fun_prop
      · fun_prop
    have hmul := hdiv.mul (contDiffOn_const (c := α) (s := Work.FTS.EllipticEst.Q0))
    refine hmul.congr (fun p hp => ?_)
    simp only [div_eq_mul_inv]
    ring
  exact (h1.mul h2).congr (fun p hp => rfl)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
