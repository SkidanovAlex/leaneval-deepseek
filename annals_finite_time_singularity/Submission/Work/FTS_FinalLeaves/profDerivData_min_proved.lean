import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.MeridianDyn.Bridge.mainLHS_sub_N_eq
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.normSlopePhysVelLe
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.ctu_aux.Grad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint `C¹` of the reconstructed potential `q = potOn ω` on the half-open strip

This module proves `Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open`: the uncurried
potential `(x,t) ↦ q x t = potOn ω x t = pressurePotential (lamb (physVel ω) ω · t) x` is jointly
`C¹` on `ℝ³ × (0,T)`.

The route (the standard "continuous partials" criterion, in the corrected form
`hasFDerivAt_uncurry_of_partials'` of this area):

* the **spatial** partial derivative of the slice `q · t` is `innerSL ℝ (∂ₜu - u×ω)`
  — this is the hypothesis `hgq` of the target statement (`potGradCLM`);
* the **time** partial derivative is `potTDeriv ω x t = -∫ ⟪∇N(x-y), ∂ₜ(u×ω)(y,t)⟫`
  (`hasDerivAt_potOn_time`, the clamped-field argument of this file);
* both partial derivative fields are continuous on `ℝ³ × (0,T)`: the spatial one from the
  strip regularity (`hstrips`), the temporal one (`potTDeriv_continuousAt`) by differentiating
  under the integral sign.

`hasFDerivAt_uncurry_of_partials'` then furnishes the full derivative at each interior point and
`contDiffWithinAt_one_of_hasFDerivAt` converts this into the `C¹` statement (`ContDiffOn` is
definitionally `∀ z ∈ s, ContDiffWithinAt`).

The helper lemmas are stated with the *same* hypothesis blob as the target so that they can be
consumed verbatim; the `_aux` suffix keeps them apart from the sibling modules in which the
fleet is proving the individual pieces.
-/

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect
/-- **Continuity of the spatial partial derivative `potGradCLM ω = innerSL ℝ (∂ₜu - u×ω)`.**
On the open strip `ℝ³ × (0,S)` this is the composition of the continuous map
`(x,t) ↦ ∂ₜu(x,t) - u(x,t)×ω(x,t)` with `innerSL ℝ`. -/
theorem continuousAt_potGradCLM_aux {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z s) x = ω x s)
    (x : R3) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    ContinuousAt (fun p : R3 × ℝ => potGradCLM ω p.1 p.2) (x, t) := by
  obtain ⟨ht0, htT⟩ := ht
  obtain ⟨S, htS, hST⟩ : ∃ S : ℝ, t < S ∧ S < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  have hS0 : 0 < S := lt_trans ht0 htS
  have hSIoo : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
  have hstripS : IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S) := hstrips S hSIoo
  have hcd : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) := hstripS.1
  have hsub : Set.univ ×ˢ Set.Ioo (0 : ℝ) S ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) S :=
    Set.prod_mono (subset_refl (Set.univ : Set R3)) Set.Ioo_subset_Icc_self
  have htd : ContinuousOn (fun p : R3 × ℝ => timeDeriv (physVel ω) p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 S) := timeDeriv_physVel_continuousOn_strip_aux hS0 hstripS
  have hωc : ContinuousOn (fun p : R3 × ℝ => ω p.1 p.2) (Set.univ ×ˢ Set.Ioo 0 S) :=
    (omega_strip_continuousOn_aux hSIoo hstrips hcurl).mono hsub
  have huc : ContinuousOn (fun p : R3 × ℝ => physVel ω p.1 p.2) (Set.univ ×ˢ Set.Ioo 0 S) :=
    hcd.continuousOn.mono hsub
  have hcross : ContinuousOn (fun p : R3 × ℝ =>
      crossVec (physVel ω p.1 p.2) (ω p.1 p.2)) (Set.univ ×ˢ Set.Ioo 0 S) := by
    have h : (fun p : R3 × ℝ => crossVec (physVel ω p.1 p.2) (ω p.1 p.2))
        = fun p => BSSwirl.crossBilin (physVel ω p.1 p.2) (ω p.1 p.2) := rfl
    rw [h]
    exact (BSSwirl.crossBilin.continuous.comp_continuousOn huc).clm_apply hωc
  have hΦ : ContinuousOn (fun p : R3 × ℝ =>
      timeDeriv (physVel ω) p.1 p.2 - crossVec (physVel ω p.1 p.2) (ω p.1 p.2))
      (Set.univ ×ˢ Set.Ioo 0 S) := htd.sub hcross
  have hG : ContinuousOn (fun p : R3 × ℝ => innerSL ℝ
      (timeDeriv (physVel ω) p.1 p.2 - crossVec (physVel ω p.1 p.2) (ω p.1 p.2)))
      (Set.univ ×ˢ Set.Ioo 0 S) :=
    ((innerSL ℝ).continuous.comp_continuousOn hΦ)
  exact (hG.continuousAt (by
    rw [nhds_prod_eq]
    exact prod_mem_prod univ_mem (Ioo_mem_nhds ht0 htS)))

/-- The derivative field of the uncurried potential: `potFDeriv ω x t`, written as
`(∂ₓ q).comp fst + (∂ₜ q) • snd`. -/
theorem potFDeriv_eq_aux (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    potFDeriv ω x t = (potGradCLM ω x t).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
      + (potTDeriv ω x t) • (ContinuousLinearMap.snd ℝ R3 ℝ) := by
  rw [potFDeriv, smulRight_snd_eq_smul']


end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotOnTime =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint `C¹` of the reconstructed potential `q = potOn ω` on the half-open strip

This module proves `Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open`: the uncurried
potential `(x,t) ↦ q x t = potOn ω x t = pressurePotential (lamb (physVel ω) ω · t) x` is jointly
`C¹` on `ℝ³ × (0,T)`.

The route (the standard "continuous partials" criterion, in the corrected form
`hasFDerivAt_uncurry_of_partials'` of this area):

* the **spatial** partial derivative of the slice `q · t` is `innerSL ℝ (∂ₜu - u×ω)`
  — this is the hypothesis `hgq` of the target statement (`potGradCLM`);
* the **time** partial derivative is `potTDeriv ω x t = -∫ ⟪∇N(x-y), ∂ₜ(u×ω)(y,t)⟫`
  (`hasDerivAt_potOn_time`, the clamped-field argument of this file);
* both partial derivative fields are continuous on `ℝ³ × (0,T)`: the spatial one from the
  strip regularity (`hstrips`), the temporal one (`potTDeriv_continuousAt`) by differentiating
  under the integral sign.

`hasFDerivAt_uncurry_of_partials'` then furnishes the full derivative at each interior point and
`contDiffWithinAt_one_of_hasFDerivAt` converts this into the `C¹` statement (`ContDiffOn` is
definitionally `∀ z ∈ s, ContDiffWithinAt`).

The helper lemmas are stated with the *same* hypothesis blob as the target so that they can be
consumed verbatim; the `_aux` suffix keeps them apart from the sibling modules in which the
fleet is proving the individual pieces.
-/

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect
/-- **The time derivative of the potential exists and equals `potTDeriv`.**  Clamp the fields to
the strip `[0,S]`, `t < S < T`: the clamped Lamb vector is jointly continuous, uniformly supported,
Lipschitz in time and differentiable in time at `t` (this is where the two-sided differentiability
of the vorticity slices is used), so `hasDerivAt_pressurePotential_time_of_continuous` applies; the
clamping is invisible near `t`. -/
theorem hasDerivAt_potOn_time_aux {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z s) x = ω x s)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ y, ω y s ≠ 0 → ‖y‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ y, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω y) (timeDeriv ω y s) (Set.Ici s) s)
    (x : R3) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun s => potOn ω x s) (potTDeriv ω x t) t := by
  have ht0 : 0 < t := ht.1
  have htT : t < T := ht.2
  obtain ⟨S, htS, hST⟩ : ∃ S : ℝ, t < S ∧ S < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  have hS0 : 0 < S := lt_trans ht0 htS
  have hSIoo : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
  have hIoo : t ∈ Set.Ioo 0 S := ⟨ht0, htS⟩
  have hIcc : t ∈ Set.Icc 0 S := ⟨ht0.le, htS.le⟩
  have hstripS : IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S) := hstrips S hSIoo
  have hcd : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) := hstripS.1
  -- the clamped fields
  set uc : R3 → ℝ → R3 := extendTime (physVel ω) S with hucdef
  set ωc : R3 → ℝ → R3 := extendTime ω S with hωcdef
  set fc : R3 → ℝ → R3 := lamb uc ωc with hfcdef
  have hfc_eq : fc = extendTime (lamb (physVel ω) ω) S := by
    funext y s
    rfl
  -- joint continuity of the clamped Lamb vector
  have huc_cont : Continuous (Function.uncurry uc) :=
    continuous_uncurry_extendTime_aux hS0.le hcd.continuousOn
  have hωc_cont : Continuous (Function.uncurry ωc) :=
    continuous_uncurry_extendTime_aux hS0.le (omega_strip_continuousOn_aux hSIoo hstrips hcurl)
  have hfc_cont : Continuous fun p : R3 × ℝ => fc p.1 p.2 := by
    have h : (fun p : R3 × ℝ => fc p.1 p.2)
        = fun p => BSSwirl.crossBilin (uc p.1 p.2) (ωc p.1 p.2) := rfl
    rw [h]
    exact (BSSwirl.crossBilin.continuous.comp huc_cont).clm_apply hωc_cont
  -- its support
  obtain ⟨R₀, hR₀⟩ := hsupp S hSIoo
  have hfc_supp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, fc y s ≠ 0 → ‖y‖ ≤ R := by
    refine ⟨R₀, fun s _ y hy => ?_⟩
    have hωc : ωc y s ≠ 0 := by
      intro h
      exact hy (by rw [show fc y s = crossVec (uc y s) (ωc y s) from rfl, h,
        crossVec_zero_right'])
    exact hR₀ (clampt S s) (clampt_mem_Icc hS0.le s) y hωc
  -- the time-Lipschitz bounds on the strip, transported to the clamped fields
  obtain ⟨hωLip, huLip⟩ :=
    lipschitz_time_lamb_strips hSIoo hIcc hstrips hcurl (hsupp S hSIoo) hcontDt hderiv
  obtain ⟨Cu, huLip'⟩ := huLip
  obtain ⟨Cω, hωLip'⟩ := hωLip
  have hCu0 : 0 ≤ Cu := nonneg_of_lipschitz ht0.le htS huLip'
  have hCω0 : 0 ≤ Cω := nonneg_of_lipschitz ht0.le htS hωLip'
  have huc_lip : ∀ (y : R3) (s : ℝ), ‖uc y s - uc y t‖ ≤ Cu * |s - t| :=
    lipschitz_extendTime (v := physVel ω) hS0.le hCu0 hIcc huLip'
  have hωc_lip : ∀ (y : R3) (s : ℝ), ‖ωc y s - ωc y t‖ ≤ Cω * |s - t| :=
    lipschitz_extendTime (v := ω) hS0.le hCω0 hIcc hωLip'
  -- uniform bounds for the clamped fields
  obtain ⟨M, hM0, hMbdd⟩ := omega_uniform_bound hSIoo hstrips hcurl
  obtain ⟨B, hB0, hBbdd⟩ := biotSavart_uniform_bound hM0 hMbdd hR₀
  have huc_bdd : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖uc y s‖ ≤ B := by
    intro y s _
    rw [show uc y s = physVel ω y (clampt S s) from rfl, Work.FTS.Physical.physVel_apply]
    exact hBbdd (clampt S s) (clampt_mem_Icc hS0.le s) y
  have hωc_bdd : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ωc y s‖ ≤ M := by
    intro y s _
    exact hMbdd (clampt S s) (clampt_mem_Icc hS0.le s) y
  have huc_lip_max : ∀ (y : R3) (s : ℝ), ‖uc y s - uc y t‖ ≤ max Cu Cω * |s - t| :=
    fun y s => le_trans (huc_lip y s)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hωc_lip_max : ∀ (y : R3) (s : ℝ), ‖ωc y s - ωc y t‖ ≤ max Cu Cω * |s - t| :=
    fun y s => le_trans (hωc_lip y s)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  have huc_bdd_max : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖uc y s‖ ≤ max B M :=
    fun y s hs => le_trans (huc_bdd y s hs) (le_max_left _ _)
  have hωc_bdd_max : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ωc y s‖ ≤ max B M :=
    fun y s hs => le_trans (hωc_bdd y s hs) (le_max_right _ _)
  obtain ⟨C', hC'⟩ := lamb_lipschitz_near (u := uc) (ω := ωc) (t := t)
    (C := max Cu Cω) (B := max B M)
    (fun y s _ => huc_lip_max y s) (fun y s _ => hωc_lip_max y s) huc_bdd_max hωc_bdd_max
  -- differentiability in time of the clamped Lamb vector at `t`
  have hu_slice : ∀ y, HasDerivAt (fun s => uc y s) (timeDeriv uc y t) t := by
    intro y
    have h1 := hasDerivAt_physVel_time (x := y) hIoo hstripS
    have h2 : HasDerivAt (fun s => uc y s) (timeDeriv (physVel ω) y t) t :=
      h1.congr_of_eventuallyEq (eventuallyEq_extendTime (v := physVel ω) hIoo y)
    rwa [← timeDeriv_extendTime (v := physVel ω) hIoo y] at h2
  have hω_slice : ∀ y, HasDerivAt (fun s => ωc y s) (timeDeriv ωc y t) t := by
    intro y
    have h1 := hasDerivAt_omega_slice_at_aux hstrips hcurl hcontDt hderiv ht y
    have h2 : HasDerivAt (fun s => ωc y s) (timeDeriv ω y t) t :=
      h1.congr_of_eventuallyEq (eventuallyEq_extendTime (v := ω) hIoo y)
    rwa [← timeDeriv_extendTime (v := ω) hIoo y] at h2
  have hderiv_fc : ∀ y, HasDerivAt (fc y) (timeDeriv fc y t) t :=
    fun y => hasDerivAt_lamb_time (hu_slice y) (hω_slice y)
  have hlip_fc : ∃ C, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖fc y s - fc y t‖ ≤ C * |s - t| := by
    refine ⟨C', ?_⟩
    intro y s hs
    show ‖lamb uc ωc y s - lamb uc ωc y t‖ ≤ C' * |s - t|
    exact hC' y s hs
  -- the differentiation under the integral sign
  have hmain := hasDerivAt_pressurePotential_time_of_continuous (f := fc) (x := x)
    hfc_cont hfc_supp hlip_fc hderiv_fc
  have htd_fc : ∀ y, timeDeriv fc y t = timeDeriv (lamb (physVel ω) ω) y t := by
    intro y
    rw [hfc_eq, timeDeriv_extendTime (v := lamb (physVel ω) ω) hIoo y]
  have hval : (-∫ y, inner ℝ (nablaNfund (x - y)) (timeDeriv fc y t)) = potTDeriv ω x t := by
    rw [potTDeriv]
    congr 1
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by simp only [htd_fc y]
  rw [hval] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hIoo] with s hs
  show potOn ω x s = pressurePotential (fun y => fc y s) x
  rw [potOn]
  congr 1
  funext y
  rw [hfc_eq, extendTime_apply, clampt_eq_self_of_mem ⟨hs.1.le, hs.2.le⟩]
end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.profDerivData_min_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`ProfDerivData` from the finite-order package `RegPkgMin`.**

The seven static derivation fields of the meridian bridge follow from the finite-order regularity
package `Work.FTS.StrongGlobal.RegPkgMin α g` (joint `C¹` in `(z,θ,τ)`, spatial `C⁴` of each
slice, `ℋ⁴`-membership) and the interior `C²`-regularity of the stream function `Φ` on the open
quadrant.  This is the `RegPkgMin`-analogue of
`Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed`.

The two `L₁₂`-facts about the full profile `F_τ = F_* + g(·,·,τ)` (integrability of the density
on `(0,∞)`, continuity at `z > 0`) are obtained by additivity of the density from the slice
`g(·,·,τ)` — where `ContDiffOn ℝ 4` + `HkMem α 4` suffice (`Min.L12Cont`) — and from the explicit
profile `F_* α` (`Min.FstarFacts`).  No hypothesis on `α` is needed: when `c α = 0` the profile
`F_* α` vanishes identically. -/
theorem profDerivData_min_proved {α : ℝ} {Φ g : Work.FTS.Galerkin.Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin α g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd) :
    Work.FTS.MeridianDyn.ProfDerivData α Φ g := by
  have hQd_open : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- spatial regularity of the slices of `g`
  have hslice4 : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := fun τ hτ => hmin.c4 τ hτ.le
  have hmem4 : ∀ τ : ℝ, 0 < τ → Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice g τ) :=
    fun τ hτ => hmin.mem4 τ hτ.le
  -- the `L₁₂`-facts about the slice `g(τ)`
  have hsliceDenInt : ∀ τ : ℝ, 0 < τ → MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ)) (Set.Ioi 0) :=
    fun τ hτ => Min.L12dens_integrableOn_of_continuousOn (hslice4 τ hτ).continuousOn
      (hmem4 τ hτ)
  have hsliceDenCont : ∀ τ z : ℝ, 0 < τ → 0 < z → ContinuousAt
      (Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ)) z :=
    fun τ z hτ hz => Min.L12dens_continuousAt_of_contDiffOn_four α hz (hslice4 τ hτ)
      (hmem4 τ hτ)
  have hsliceSlice : ∀ τ : ℝ, 0 < τ → ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS.Galerkin.slice g τ s θ / s) Work.Spaces.Iθ :=
    fun τ hτ => Min.sliceK_integrableOn_of_continuousOn (hslice4 τ hτ).continuousOn
      (hmem4 τ hτ)
  -- the `L₁₂`-facts about `F_*`
  obtain ⟨hFsSlice, hFsInt, hFsCont⟩ := Min.Fstar_L12_facts α
  -- the `L₁₂`-facts about the full profile `F_τ = F_* + g(τ)`
  have hadd : ∀ τ : ℝ, 0 < τ → ∀ s : ℝ, 0 < s →
      Work.Construction.L12dens (Work.Construction.Ftau α g τ) s
        = Work.Construction.L12dens (Work.Construction.Fstar α) s
          + Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) s := by
    intro τ hτ s hs
    have h := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (a := Work.Construction.Fstar α) (b := Work.FTS.Galerkin.slice g τ)
      (s := s) (hFsSlice s hs) (hsliceSlice τ hτ s hs)
    rw [← Min.Ftau_eq_Fstar_add_slice α g τ] at h
    exact h
  have hdenInt : ∀ τ : ℝ, 0 < τ → MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Ftau α g τ)) (Set.Ioi 0) := by
    intro τ hτ
    have hsum := hFsInt.add (hsliceDenInt τ hτ)
    exact hsum.congr_fun (fun s hs => (hadd τ hτ s hs).symm) measurableSet_Ioi
  have hdenCont : ∀ τ z : ℝ, 0 < τ → 0 < z → ContinuousAt
      (Work.Construction.L12dens (Work.Construction.Ftau α g τ)) z := by
    intro τ z hτ hz
    have hsum := (hFsCont z hz).add (hsliceDenCont τ z hτ hz)
    refine hsum.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    exact (hadd τ hτ s hs).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `h2`
    intro z θ τ hQd hτ
    have hz : 0 < z := hQd.1
    have hzth : DifferentiableAt ℝ (fun z' => Φ z' θ τ) z := by
      have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, θ) :=
        ((hΦ τ hτ).contDiffAt (hQd_open.mem_nhds hQd)).differentiableAt (by norm_num)
      exact Work.Spaces.differentiableAt_curry_left (G := fun z' θ' => Φ z' θ' τ) hd
    have hthz : DifferentiableAt ℝ
        (fun z' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z :=
      Min.differentiableAt_Theta_slice_z (hdenInt τ hτ) (hdenCont τ z hτ hz) hz
    have hsub : deriv (fun z' => Φ z' θ τ
          - Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z
        = deriv (fun z' => Φ z' θ τ) z
          - deriv (fun z' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z :=
      deriv_sub hzth hthz
    simp only [Work.Spaces.pz, Work.Construction.PhiTil, Work.FTS.Galerkin.slice]
    rw [hsub]
    ring
  · -- `h3`
    intro z θ τ hQd hτ
    have hzth : DifferentiableAt ℝ (fun θ' => Φ z θ' τ) θ := by
      have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, θ) :=
        ((hΦ τ hτ).contDiffAt (hQd_open.mem_nhds hQd)).differentiableAt (by norm_num)
      exact Work.Spaces.differentiableAt_curry_right (G := fun z' θ' => Φ z' θ' τ) hd
    have htht : DifferentiableAt ℝ
        (fun θ' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ :=
      Min.differentiableAt_Theta_slice_theta
    have hsub : deriv (fun θ' => Φ z θ' τ
          - Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ
        = deriv (fun θ' => Φ z θ' τ) θ
          - deriv (fun θ' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ :=
      deriv_sub hzth htht
    simp only [Work.Spaces.pth, Work.Construction.PhiTil, Work.FTS.Galerkin.slice]
    rw [hsub]
    ring
  · -- `h5`
    intro z θ τ hQd hτ
    exact Min.Dz_Theta_eq_any (hdenInt τ hτ) (hdenCont τ z hτ hQd.1) hQd.1
  · -- `h6`
    intro z θ τ hQd hτ
    exact Min.pth_Theta_eq_any z θ
  · -- `hDz`
    intro z θ τ hQd hτ
    exact (Min.Dzg_pthg_split_c4 (α := α) (hslice4 τ hτ)).1 z θ hQd
  · -- `hpth`
    intro z θ τ hQd hτ
    exact (Min.Dzg_pthg_split_c4 (α := α) (hslice4 τ hτ)).2 z θ hQd
  · -- `hL`
    intro z τ hz hτ
    have hsum : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K
          (fun z θ => Work.Construction.Fstar α z θ + Work.FTS.Galerkin.slice g τ z θ))
        (Set.Ioi 0) := by
      have h := hdenInt τ hτ
      rwa [Min.Ftau_eq_Fstar_add_slice α g τ] at h
    have hsplit := Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
      (α := α) (a := Work.Construction.Fstar α) (b := Work.FTS.Galerkin.slice g τ)
      hFsSlice (hsliceSlice τ hτ) hsum hFsInt z hz
    rwa [← Min.Ftau_eq_Fstar_add_slice α g τ] at hsplit

end Work.FTS_FinalLeaves
end
