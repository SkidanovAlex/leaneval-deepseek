
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
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
