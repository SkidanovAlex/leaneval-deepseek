import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.contDiffWithinAt_one_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_uncurry_of_partials_corrected
import Submission.Work.FTS.PressureOn.hasDerivAt_pressurePotential_time_of_continuous
import Submission.Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential
import Submission.Work.FTS.PressureOn.Connect.Clamp
import Submission.Work.FTS.PressureOn.Connect.Data
import Submission.Work.FTS.PressureOn.Connect.lipschitz_extendTime
import Submission.Work.FTS.PressureOn.Connect.lamb_lipschitz_near
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_physVel_time
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_of_hasDerivWithinAt_Ici
import Submission.Work.FTS.PressureOn.Connect.biotSavart_uniform_bound
import Submission.Work.FTS.PressureOn.Connect.omega_uniform_bound
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.pressurePotential_basic
import Submission.Work.FTS.PressureOn.lipschitz_time_lamb_strips
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry
import Submission.Work.FTS.BSSwirl.CrossAux
import Submission.Work.FTS.Physical.Defs

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
