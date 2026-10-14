import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.normSlopePhysVelLe
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.PressureOn.weakPoisson
import Submission.Work.FTS.PressureOn.weyl_pair
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logW_fderiv_integral_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic =====
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
theorem crossVec_zero_right' (a : R3) : crossVec a 0 = 0 := by
  rw [crossVec_apply]; simp

/-- `smulRight` with the second coordinate is scalar multiplication of the projection. -/
theorem smulRight_snd_eq_smul' (c : ℝ) :
    (ContinuousLinearMap.snd ℝ R3 ℝ).smulRight c = c • (ContinuousLinearMap.snd ℝ R3 ℝ) := by
  ext v <;> simp

/-- **The clamped time field is jointly continuous.**  If `v` is jointly continuous on the closed
strip `ℝ³ × [0,S]`, then `(x,s) ↦ v x (clampt S s)` is continuous on all of `ℝ³ × ℝ`. -/
theorem continuous_uncurry_extendTime_aux {v : R3 → ℝ → R3} {S : ℝ} (hS : 0 ≤ S)
    (hv : ContinuousOn (Function.uncurry v) (Set.univ ×ˢ Set.Icc 0 S)) :
    Continuous (Function.uncurry (extendTime v S)) := by
  have hcl : Continuous fun s : ℝ => clampt S s := (lipschitzWith_clampt S).continuous
  have hmk : Continuous fun p : R3 × ℝ => ((p.1, clampt S p.2) : R3 × ℝ) :=
    continuous_fst.prodMk (hcl.comp continuous_snd)
  have hmap : ∀ p : R3 × ℝ, (p.1, clampt S p.2) ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) S :=
    fun p => ⟨trivial, clampt_mem_Icc hS p.2⟩
  have hmain := hv.comp_continuous hmk hmap
  refine hmain.congr fun p => ?_
  rfl

/-- **Joint continuity of the physical vorticity on a closed strip.**  `ω` is the curl of the
spatial slice of `u = physVel ω`, and the curl is a continuous function of the (continuous)
`fderivWithin` of `u.uncurry` on the strip. -/
theorem omega_strip_continuousOn_aux {α : NNReal} {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z s) x = ω x s) :
    ContinuousOn (Function.uncurry ω) (Set.univ ×ˢ Set.Icc 0 S) := by
  obtain ⟨hcd, -, -⟩ := hstrips S hS
  have hU : UniqueDiffOn ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS.1)
  have hcont : ContinuousOn
      (fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S))
      (Set.univ ×ˢ Set.Icc 0 S) := hcd.continuousOn_fderivWithin hU le_rfl
  have hmain : ContinuousOn (fun p : R3 × ℝ =>
      curlOf (fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S) p
        ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)) (Set.univ ×ˢ Set.Icc 0 S) :=
    continuous_curlOf.comp_continuousOn (hcont.clm_comp continuousOn_const)
  refine hmain.congr fun p hp => ?_
  obtain ⟨y, s⟩ := p
  obtain ⟨-, hs⟩ := hp
  simp only [Function.uncurry_apply_pair]
  have hwit : ContDiffWithinAt ℝ 1 (Function.uncurry (physVel ω))
      (Set.univ ×ˢ Set.Icc 0 S) (y, s) := hcd.contDiffWithinAt ⟨trivial, hs⟩
  rw [← hcurl s ⟨hs.1, lt_of_le_of_lt hs.2 hS.2⟩ y, vorticity_eq_curlOf,
    fderiv_slice_eq_fderivWithin_prod (u := physVel ω) (I := Set.Icc 0 S) hs hwit]

/-- **Joint continuity of the time derivative of the physical velocity on the open strip.** -/
theorem timeDeriv_physVel_continuousOn_strip_aux {α : NNReal} {ω : R3 → ℝ → R3} {S : ℝ}
    (hS : 0 < S)
    (hstrip : IsContDiffHolderOn ℝ α (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    ContinuousOn (fun p : R3 × ℝ => timeDeriv (physVel ω) p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 S) := by
  obtain ⟨hcd, -, -⟩ := hstrip
  have hU : UniqueDiffOn ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS)
  have hcont : ContinuousOn
      (fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S))
      (Set.univ ×ˢ Set.Icc 0 S) := hcd.continuousOn_fderivWithin hU le_rfl
  have hF : ContinuousOn (fun p : R3 × ℝ =>
      fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S) p
        ((0 : R3), (1 : ℝ))) (Set.univ ×ˢ Set.Icc 0 S) :=
    hcont.clm_apply continuousOn_const
  refine (hF.mono ?_).congr ?_
  · intro p hp
    exact ⟨trivial, ⟨le_of_lt hp.2.1, hp.2.2.le⟩⟩
  · intro p hp
    obtain ⟨y, s⟩ := p
    obtain ⟨-, hs⟩ := hp
    show timeDeriv (physVel ω) y s = fderivWithin ℝ (Function.uncurry (physVel ω))
      (Set.univ ×ˢ Set.Icc 0 S) (y, s) ((0 : R3), (1 : ℝ))
    have hnhds : (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) ∈ 𝓝 (y, s) := by
      rw [nhds_prod_eq]
      exact prod_mem_prod univ_mem (Icc_mem_nhds hs.1 hs.2)
    rw [fderivWithin_of_mem_nhds hnhds]
    have hdiff : DifferentiableAt ℝ (Function.uncurry (physVel ω)) (y, s) :=
      (hcd.contDiffAt hnhds).differentiableAt (by norm_num)
    rw [FiniteTimeSingularity.timeDeriv,
      (hasDerivAt_slice_of_hasFDerivAt_uncurry (v := physVel ω) (x := y) (t := s)
        hdiff.hasFDerivAt).deriv]

/-- **Two-sided differentiability of the vorticity slices at interior times.**  The right-hand
derivative is assumed (`hderiv`), the derivative is continuous on `[0,T)` (`hcontDt`) and the
slice is continuous on `[0,S]` (`continuousOn_time_omega_of_strips`); the one-sided mean value
theorem (`hasDerivAt_of_hasDerivWithinAt_Ici`) then gives the genuine two-sided derivative. -/
theorem hasDerivAt_omega_slice_at_aux {α : NNReal} {ω : R3 → ℝ → R3} {T t : ℝ}
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z s) x = ω x s)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x s) (Set.Ici s) s)
    (ht : t ∈ Set.Ioo 0 T) (y : R3) :
    HasDerivAt (fun s => ω y s) (timeDeriv ω y t) t := by
  obtain ⟨ht0, htT⟩ := ht
  obtain ⟨S, htS, hST⟩ : ∃ S : ℝ, t < S ∧ S < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  have hS0 : 0 < S := lt_trans ht0 htS
  have hSIoo : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
  refine hasDerivAt_of_hasDerivWithinAt_Ici (E := R3) ⟨ht0, htS⟩ ?_ ?_ ?_
  · exact continuousOn_time_omega_of_strips hSIoo hstrips hcurl y
  · have h1 : ContinuousOn (fun s : ℝ => ((y, s) : R3 × ℝ)) (Set.Ico 0 S) := by fun_prop
    have h2 : Set.MapsTo (fun s : ℝ => ((y, s) : R3 × ℝ)) (Set.Ico 0 S)
        (Set.univ ×ˢ Set.Ico 0 T) :=
      fun s hs => ⟨trivial, ⟨hs.1, lt_of_lt_of_le hs.2 hST.le⟩⟩
    have h3 := hcontDt.comp' h1 h2
    simpa only [Function.comp_apply] using h3
  · intro s hs
    exact hderiv y s ⟨hs.1, lt_of_lt_of_le hs.2 hST.le⟩
end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_potOn_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)

namespace Work.FTS.PressureOn.Connect

/-- The directional derivative is unchanged when the time variable is clamped, at an interior
time.  Companion of `timeDeriv_extendTime`. -/
theorem directionalDeriv_extendTime {v w : R3 → ℝ → R3}
    {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    FiniteTimeSingularity.directionalDeriv (extendTime v S) (extendTime w S) x t
      = FiniteTimeSingularity.directionalDeriv v w x t := by
  have htIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1.le, ht.2.le⟩
  unfold FiniteTimeSingularity.directionalDeriv
  rw [show (extendTime v S · t) = (v · t) from funext (fun y => by
        rw [extendTime_apply, clampt_eq_self_of_mem htIcc]),
      extendTime_apply, clampt_eq_self_of_mem htIcc]

theorem hasFDerivAt_potOn_slice {α : NNReal} {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {T : ℝ}
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) x = ω x t)
    (hdiv : ∀ t ∈ Set.Ico 0 T,
      FiniteTimeSingularity.div (fun z => Work.FTS.Physical.physVel ω z t) = 0)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hfderiv : ∀ t ∈ Set.Ioo 0 T, MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x))
    (hpointwise : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      ContDiffAt ℝ 2 (fun z => Work.FTS.Physical.physVel ω z t) x ∧
      ContDiffAt ℝ 1 (fun z => ω z t) x ∧
      FiniteTimeSingularity.timeDeriv ω x t
        + FiniteTimeSingularity.directionalDeriv ω (Work.FTS.Physical.physVel ω) x t
        = FiniteTimeSingularity.directionalDeriv (Work.FTS.Physical.physVel ω) ω x t)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : Work.FTS.PressureOn.R3) :
    HasFDerivAt (Work.FTS.PressureOn.potOn ω · t)
      (innerSL ℝ (FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t
        - Work.FTS.PressureOn.crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))) x := by
  obtain ⟨ht0, htT⟩ := ht
  -- an interior time `S ∈ (t,T)`: all windowed machinery is used there
  obtain ⟨S, htS, hStT, hS0⟩ :
      ∃ S : ℝ, t < S ∧ S < T ∧ 0 < S := ⟨(t + T) / 2, by linarith, by linarith, by linarith⟩
  have hSIoo : S ∈ Set.Ioo 0 T := ⟨hS0, hStT⟩
  have hIoo : t ∈ Set.Ioo 0 S := ⟨ht0, htS⟩
  have hIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht0.le, htS.le⟩
  have hIco : t ∈ Set.Ico (0 : ℝ) S := ⟨ht0.le, htS⟩
  have hstripS := hstrips S hSIoo
  -- ## Step 1: the slices at time `t`
  have hu_cd : ContDiff ℝ 1 (physVel ω · t) :=
    contDiff_slice_of_isContDiffHolderOn hstripS hIcc
  have hu_cont : Continuous (fun y => physVel ω y t) := hu_cd.continuous
  have hω_cont : Continuous (fun y => ω y t) :=
    continuous_vorticity_slice hStT hIcc hstripS hcurl
  have hcross_cont : Continuous (fun y => crossVec (physVel ω y t) (ω y t)) := by
    have h : (fun y => crossVec (physVel ω y t) (ω y t))
        = fun y => Work.FTS.BSSwirl.crossBilin (physVel ω y t) (ω y t) := rfl
    rw [h]
    exact (Work.FTS.BSSwirl.crossBilin.continuous.comp hu_cont).clm_apply hω_cont
  have hlamb_cont : Continuous (fun y => lamb (physVel ω) ω y t) := hcross_cont
  have htd_cont : Continuous (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t) :=
    continuous_timeDeriv_slice hIoo hstripS
  -- ## Step 2: the potential `q = potOn ω · t` and the field `Φ = ∂ₜu - u×ω`
  obtain ⟨R0, hR0⟩ := hsupp S hSIoo
  have hlamb_cs : HasCompactSupport (fun y => lamb (physVel ω) ω y t) :=
    hasCompactSupport_lamb_slice (u := physVel ω) (fun y hy => hR0 t hIcc y hy)
  have hpb := pressurePotential_basic hlamb_cont hlamb_cs
  have hq : Continuous (potOn ω · t) := hpb.1
  have hq0 : Filter.Tendsto (potOn ω · t) (Filter.cocompact _) (nhds 0) := hpb.2.2
  have hΦ_cont : Continuous (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t
      - crossVec (physVel ω y t) (ω y t)) := htd_cont.sub hcross_cont
  have hΦ0 : Filter.Tendsto (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t
      - crossVec (physVel ω y t) (ω y t)) (Filter.cocompact _) (nhds 0) :=
    tendsto_lamb_decay hSIoo hIco hstrips hcurl (hsupp S hSIoo) hcontDt hderiv
  -- ## Step 3: the Lipschitz-in-time bounds, transferred to the clamped fields
  obtain ⟨hωLipIcc, huLipIcc⟩ :=
    lipschitz_time_lamb_strips hSIoo hIcc hstrips hcurl (hsupp S hSIoo) hcontDt hderiv
  obtain ⟨Cu, hCulip⟩ := huLipIcc
  obtain ⟨Cω, hCωlip⟩ := hωLipIcc
  have hCulip' : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖extendTime (physVel ω) S y s - extendTime (physVel ω) S y t‖ ≤ Cu * |s - t| :=
    fun y s _ => lipschitz_extendTime hS0.le (nonneg_of_lipschitz ht0.le htS hCulip) hIcc hCulip y s
  have hCωlip' : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖extendTime ω S y s - extendTime ω S y t‖ ≤ Cω * |s - t| :=
    fun y s _ => lipschitz_extendTime hS0.le (nonneg_of_lipschitz ht0.le htS hCωlip) hIcc hCωlip y s
  -- ## Step 4: the weak divergence identity for `(q, Φ)`
  have hweakDiv : ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ y, inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t
          - crossVec (physVel ω y t) (ω y t)) (gradient φ y)
        = -∫ y, potOn ω y t * laplaceTrace φ y := by
    intro φ hφ hφcs
    -- `∫ ⟪∂ₜu, ∇φ⟫ = 0`, from the divergence-free condition on the clamped field
    have hcore : ∫ y, inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
        (gradient φ y) = 0 := by
      have h := weakDiv_timeDeriv (u := extendTime (physVel ω) S) (t := t) (φ := φ) hφ hφcs
        (Filter.Eventually.of_forall fun s => ⟨contDiff_extendTime_slice hS0.le hstripS s,
          div_extendTime hSIoo hdiv s⟩)
        (fun y => hasDerivWithinAt_extendTime hIoo
          (fun y => (hasDerivAt_physVel_time hIoo hstripS).hasDerivWithinAt) y)
        ⟨Cu, hCulip'⟩
      simpa only [timeDeriv_extendTime hIoo] using h
    exact weakDiv_pair (u := physVel ω) (ω := ω) (t := t) (φ := φ) hφ hφcs
      hlamb_cont htd_cont hcore (weakPoisson hlamb_cont hlamb_cs hφ hφcs)
  -- ## Step 5: the weak curl identity for `(q, Φ)`
  have hweakCurl : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ y, inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t
          - crossVec (physVel ω y t) (ω y t)) (FiniteTimeSingularity.vorticity ψ y) = 0 := by
    intro ψ hψ hψcs
    have hclampωt : (fun z => extendTime ω S z t) = fun z => ω z t :=
      funext fun z => by rw [extendTime_apply, clampt_eq_self_of_mem hIcc]
    have hclampedt : (fun z => extendTime (physVel ω) S z t) = fun z => physVel ω z t :=
      funext fun z => by rw [extendTime_apply, clampt_eq_self_of_mem hIcc]
    have hRclamp : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1),
        ∀ y, extendTime ω S y s ≠ 0 → ‖y‖ ≤ R :=
      ⟨max R0 0, le_max_right _ _, fun s _ y hy => by
        rw [extendTime_apply] at hy
        exact le_trans (hR0 (clampt S s) (clampt_mem_Icc hS0.le s) y hy) (le_max_left _ _)⟩
    have hwc := weakCurl_pair (u := extendTime (physVel ω) S) (ω := extendTime ω S)
      (t := t) (A := ψ) hψ hψcs hRclamp
      (fun s _ => contDiff_extendTime_slice hS0.le hstripS s)
      (fun s _ y => congrFun (vorticity_extendTime hSIoo hcurl s) y)
      (fun s _ => div_extendTime hSIoo hdiv s)
      (by rw [hclampωt]; exact hω_cont)
      (fun y hy0 hy2 => by
        rw [hclampωt]
        have hxU : y ∈ Uax := ⟨hy2, by
          intro hsum
          have h2 : 0 < y 0 ^ 2 := sq_pos_of_ne_zero hy0
          nlinarith [sq_nonneg (y 1)]⟩
        exact ((hpointwise t ⟨ht0, htT⟩ y hxU).2.1.differentiableAt (by simp)).hasFDerivAt)
      (by rw [hclampωt]; exact hfderiv t ⟨ht0, htT⟩)
      (fun y => hasDerivWithinAt_extendTime hIoo
        (fun y => (hasDerivAt_physVel_time hIoo hstripS).hasDerivWithinAt) y)
      (fun y => hasDerivWithinAt_extendTime hIoo
        (fun y => hderiv y t ⟨ht0.le, htT⟩) y)
      ⟨Cu, hCulip'⟩ ⟨Cω, hCωlip'⟩
      (fun y hy => by
        rw [timeDeriv_extendTime hIoo y,
          directionalDeriv_extendTime (v := ω) (w := physVel ω) hIoo y,
          directionalDeriv_extendTime (v := physVel ω) (w := ω) hIoo y]
        exact (hpointwise t ⟨ht0, htT⟩ y hy).2.2)
    -- undo the clamping inside the two integrals
    have h1 : (fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (extendTime (physVel ω) S) y t)
          (FiniteTimeSingularity.vorticity ψ y))
        = fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
          (FiniteTimeSingularity.vorticity ψ y) :=
      funext fun y => by rw [timeDeriv_extendTime hIoo y]
    have h2 : (fun y => inner ℝ (crossVec (extendTime (physVel ω) S y t) (extendTime ω S y t))
          (FiniteTimeSingularity.vorticity ψ y))
        = fun y => inner ℝ (crossVec (physVel ω y t) (ω y t))
          (FiniteTimeSingularity.vorticity ψ y) :=
      funext fun y => by rw [congrFun hclampedt y, congrFun hclampωt y]
    rw [h1, h2] at hwc
    -- integrability of the two pairings
    have hvort := Work.FTS.BSSwirl.contDiff_vorticity_and_support hψ hψcs
    have hint1 : Integrable (fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
        (FiniteTimeSingularity.vorticity ψ y)) :=
      (htd_cont.inner (hvort.1 0).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hvort.2 _)
    have hint2 : Integrable (fun y => inner ℝ (crossVec (physVel ω y t) (ω y t))
        (FiniteTimeSingularity.vorticity ψ y)) :=
      (hcross_cont.inner (hvort.1 0).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hvort.2 _)
    have hpt : (fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t
          - crossVec (physVel ω y t) (ω y t)) (FiniteTimeSingularity.vorticity ψ y))
        = fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
            (FiniteTimeSingularity.vorticity ψ y)
          - inner ℝ (crossVec (physVel ω y t) (ω y t)) (FiniteTimeSingularity.vorticity ψ y) :=
      funext fun y => inner_sub_left _ _ _
    rw [hpt, integral_sub hint1 hint2, hwc]
    ring
  -- ## Step 6: the Weyl/Liouville pair lemma
  exact weyl_pair (potOn ω · t)
    (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t
      - crossVec (physVel ω y t) (ω y t))
    hq hΦ_cont hq0 hΦ0 hweakDiv hweakCurl x

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4_transfer_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4_transfer_deriv.lean` — the level-four derivative-priced transfer estimate

The hypothesis `hslot` is the *slot* transfer of `TransferDeriv/Defs.lean`; the conclusion lifts it
to the level-four pairing `IP4 = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))`.

The assembly: `IP4 α (J_ε f) h − IP4 α f (J_ε h)` is the transfer defect `Def 3 0 0` of the
recursion (`IP4Rec`), which the recursion bounds by `KCB 3` times the level-zero bound
(`IP4Leaf.leaf_bound`, through the slot transfer at the cuts of the shifted slots, `IP4Slots`), and
the level-zero bound is `O(ε |f|_{ℋ⁴} |h|_{ℋ⁵})`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-!
# `Work.FTS.StrongEps.EpsRLX.WpUniformBound`

**A uniform `ℋ⁵`-bound on the projected-mollified profile `Wp ρ ε u = Pz (J_ε u)`.**

The datum `ProfileData α C₀ B ε ρ u` bounds only the *order-`6`* norm of `u`
(`HkNorm α 6 u ≤ B`).  The profile facts (`ProfileFacts`) give

* `EpsSq α u ≤ C/(γ-1)² · HkSq α 1 u` (the `X`-norm of the datum with the `1/(γ-1)`-price),
* `HkSq α 6 (Wp ρ ε u) ≤ C · (C/ε)¹² · EpsSq α u` (one factor `C/ε` per derivative),

and `HkSq α 1 u ≤ HkSq α 6 u = (HkNorm α 6 u)² ≤ B²`.  Hence

  `HkSq α 5 (Wp ρ ε u) ≤ HkSq α 6 (Wp ρ ε u) ≤ (C/(γ-1) · (C/ε)⁶ · B)²`,

and taking square roots (the bound being nonnegative) gives the statement.  In particular the
`ℋ⁵`-size of the profile is proportional to `B`, uniformly in `α` and `ε`, with the sole
`(C/ε)⁶` price of the mollifier and the `1/(γ-1)` price of the angular Hardy inequality.
-/

/-- The elementary identity behind the final constant: the product appearing in the chain of
inequalities is the square of the stated bound.  (Pure field algebra; `ring` cannot see it
directly because it treats `((γ-1)²)⁻¹` and `((γ-1)⁻¹)²` as distinct normal forms, so the
divisions are unfolded first.) -/
private theorem sq_prod_eq (C d e B : ℝ) :
    C * (C / e) ^ 12 * (C / d ^ 2 * B ^ 2) = (C / d * (C / e) ^ 6 * B) ^ 2 := by
  rw [div_eq_mul_inv]
  ring

theorem WpUniformBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {C₀ B : ℝ}, 0 ≤ B →
      ∀ {u : Work.FTS.Galerkin.Fn}, Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        ≤ C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsRLX.ProfileFacts ρ hρ
  refine ⟨C, hCpos, ?_⟩
  intro α hα ε hε C₀ B hB u hd
  obtain ⟨hmem_u, hsq_u, h3, hmem_W, hsq_W, htr, hmem7W, h8⟩ := hC α hα ε hε hd
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- `ℋ⁶`-membership of the projected-mollified profile, read off the order-`7` fact
  have hmem6W : Work.Spaces.HkMem α 6 (Wp ρ ε u) :=
    Work.FTS.OpenPkg.HkMem_mono_open hd.cls.reg 6 (by norm_num) hmem7W
  have h56 : Work.Spaces.HkSq α 5 (Wp ρ ε u) ≤ Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6W
  have h16 : Work.Spaces.HkSq α 1 u ≤ Work.Spaces.HkSq α 6 u :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hd.hkmem
  -- the datum bound `HkNorm α 6 u ≤ B` squared
  have h6B : Work.Spaces.HkSq α 6 u ≤ B ^ 2 := by
    have h := hd.hknorm
    rw [Work.Spaces.HkNorm] at h
    calc Work.Spaces.HkSq α 6 u = (Real.sqrt (Work.Spaces.HkSq α 6 u)) ^ 2 :=
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 u)).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hcf : 0 ≤ C * (C / ε) ^ 12 :=
    mul_nonneg hCpos.le (pow_nonneg (div_nonneg hCpos.le hε0.le) 12)
  -- the chain of profile facts
  have hchain : Work.Spaces.HkSq α 5 (Wp ρ ε u)
      ≤ C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) := by
    refine le_trans h56 ?_
    refine le_trans h3 (mul_le_mul_of_nonneg_left ?_ hcf)
    exact le_trans hsq_u (mul_le_mul_of_nonneg_left (le_trans h16 h6B)
      (div_nonneg hCpos.le (pow_pos hγpos 2).le))
  have ht : 0 ≤ C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B :=
    mul_nonneg (mul_nonneg (div_nonneg hCpos.le hγpos.le)
      (pow_nonneg (div_nonneg hCpos.le hε0.le) 6)) hB
  have heq := sq_prod_eq C (Work.Spaces.gam α - 1) ε B
  rw [Work.Spaces.HkNorm, Real.sqrt_le_iff]
  exact ⟨ht, le_trans hchain (le_of_eq heq)⟩

end Work.FTS.StrongEps.EpsRLX
end
