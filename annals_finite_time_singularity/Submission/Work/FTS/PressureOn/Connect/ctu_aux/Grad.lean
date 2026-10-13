import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
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
