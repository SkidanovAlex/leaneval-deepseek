/-
# `exists_cptQ_approx` — `ℋᵏ`-membership of the error

The error of the approximation is `err n F = (chiR n · zetaR n − 1)·F − (chiR n · lam n F)·rho`.
Its `ℋᵏ`-membership (honest integrability of all the weighted derivatives) follows from the
per-`z` estimate `EstMain.theta_lintegral_le` together with:

* the finiteness of the `Ω_n`-part of the energy (`lintegral_ofReal_omegaPart_le` + `HkMem F`),
* the finiteness of the moment factor (the `Est.lintegral_momentFactor_le` bound),
* the finiteness of the angular profile `rhoProf` (`Est.rhoProf_ae_le`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAlt

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem hkMem_err (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (F : ℝ → ℝ → ℝ) (n : ℕ), 3 ≤ n → Work.FTS.EllipticEst.SmoothOpen F →
      Work.Spaces.HkMem α k F → (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) →
        Work.FTS.PhiStar.ThetaTraces α k F →
          Work.Spaces.HkMem α k (Work.FTS.PhiStar.Honesty.CptApp.err n F) := by
  intro F n hn hsm hF hFs htr
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨Ccrux, hCcruxpos, hcrux⟩ := theta_lintegral_le k α hα hα1
  have hCcrux : 0 ≤ Ccrux := hCcruxpos.le
  obtain ⟨RPb, hRPb0, hRPbd⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le k α
  obtain ⟨Cm, hCm0, hmom⟩ :=
    Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le (k := k) hsm hF hFs
  -- finiteness of `RP`
  have hvolI : (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    norm_num
  have hRPfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ)) < ⊤ := by
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := RPb * (Real.pi / 2)))
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal RPb :=
          lintegral_mono_ae (hRPbd.mono fun θ h => ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal RPb * volume Work.Spaces.Iθ := by
          rw [lintegral_const]
          congr 1
          exact Measure.restrict_apply_univ Work.Spaces.Iθ
      _ = ENNReal.ofReal RPb * ENNReal.ofReal (Real.pi / 2) := by rw [hvolI]
      _ = ENNReal.ofReal (RPb * (Real.pi / 2)) := (ENNReal.ofReal_mul hRPb0).symm
  -- finiteness of the `Ω_n`-part
  have hPfin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ)) < ⊤ := fun z hz =>
    lt_of_le_of_lt (lintegral_ofReal_omegaPart_le hF hz) ENNReal.ofReal_lt_top
  -- finiteness of the moment factor (over `Ioi 0`, hence over `Iz`)
  have hQfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)) < ⊤ := by
    have hI : (volume.restrict (Set.Ioi (0 : ℝ))) = volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.restrict_Ioi_eq_restrict_Ici
    rw [← hI]
    exact lt_of_le_of_lt (hmom n hn2) ENNReal.ofReal_lt_top
  -- the per-`z` bound
  have hz : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ)) < ⊤ := by
    intro z hz'
    refine lt_of_le_of_lt (hcrux n F hn hsm htr z hz') ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.mpr ⟨hPfin z hz',
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRPfin⟩)
  -- the angular slices of `omegaPart` are integrable in `θ`
  have hPfin2 : (∫⁻ z in Work.Spaces.Iz,
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ)) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Ici (fun z hz' => lintegral_ofReal_omegaPart_le hF hz'))) ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)]
    exact ENNReal.ofReal_lt_top
  have hsliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k (err n F) z θ) Work.Spaces.Iθ := by
    intro z hz'
    have hzge : (0 : ℝ) ≤ z := hz'
    rcases eq_or_lt_of_le hzge with h0 | hpos
    · rw [← h0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (err n F) 0 θ) = fun _ => 0 := by
        funext θ
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      rw [hzero]
      exact integrableOn_zero
    · have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k (err n F) z θ)
          (Set.Ioo 0 (π / 2)) :=
        ((EstAux.smoothOpen_err hsm hn1).continuousOn_HkIntegrand α k).comp
          (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => ⟨hpos, hθ⟩)
      refine ⟨(aemeasurable_restrict_Iθ hcont).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)]
      exact hz z hz'
  refine ⟨hsliceInt, ?_⟩
  refine ⟨(aemeasurable_integral_HkIntegrand (α := α) (k := k)
    (EstAux.smoothOpen_err hsm hn1)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)]
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (err n F) z θ)
        = ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz' =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsliceInt z hz')
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)
  rw [lintegral_congr_ae hae]
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal Ccrux
          * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
            + ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                * ∑ m ∈ Finset.range (k + 1),
                    (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
        refine lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_)
        intro z hz'
        exact hcrux n F hn hsm htr z hz'
    _ = ENNReal.ofReal Ccrux
          * ((∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
            + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                * ∑ m ∈ Finset.range (k + 1),
                    (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2))
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_add_left'
          (aemeasurable_lintegral_omegaPart (α := α) (k := k) n hsm)]
        congr 1
        exact lintegral_mul_const' _ _ hRPfin.ne
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        refine ENNReal.add_lt_top.mpr ⟨hPfin2, ENNReal.mul_lt_top hQfin hRPfin⟩

end Work.FTS.PhiStar.Honesty.CptApp.EstAlt
