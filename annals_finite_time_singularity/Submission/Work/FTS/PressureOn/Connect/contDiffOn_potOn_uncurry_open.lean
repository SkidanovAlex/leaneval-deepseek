import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.pressurePotential_basic
import Submission.Work.FTS.PressureOn.lipschitz_time_lamb_strips
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotOnTime
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotTDeriv
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Grad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint `C¹` of the reconstructed potential `q = potOn ω` on the half-open strip

`Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open`: the uncurried potential
`(x,t) ↦ q x t = potOn ω x t = pressurePotential (lamb (physVel ω) ω · t) x` is jointly `C¹` on
`ℝ³ × (0,T)`.

## The route

The criterion used is the "continuous partials" one, in the corrected form of this area
(`hasFDerivAt_uncurry_of_partials'` + `contDiffWithinAt_one_of_hasFDerivAt`):

* **the spatial partial derivative** of the slice `q · t` is `innerSL ℝ (∂ₜu - u×ω)`
  (`potGradCLM ω x t`).  This is precisely the hypothesis `hgq` of the statement; its continuity
  on the strip is `continuousAt_potGradCLM_aux` (`ctu_aux.Grad`), which combines the joint
  continuity of `∂ₜu` (`timeDeriv_physVel_continuousOn_strip_aux`, `ctu_aux.Basic`) and of `ω`
  (`omega_strip_continuousOn_aux`, `ctu_aux.Basic`) with the continuity of `innerSL ℝ`.

* **the time partial derivative** is `potTDeriv ω x t = -∫ ⟪∇N(x-y), ∂ₜ(u×ω)(y,t)⟫`.
  Its existence at interior times is `hasDerivAt_potOn_time_aux` (`ctu_aux.PotOnTime`): clamp the
  fields to a strip `[0,S]`, `t < S < T`; the clamped Lamb vector is jointly continuous, uniformly
  supported, Lipschitz in time (bounds for `ω` from `omega_uniform_bound`, for `u = physVel ω` from
  `biotSavart_uniform_bound`, assembled by `lamb_lipschitz_near`) and differentiable in time at `t`
  (`hasDerivAt_lamb_time`, whose vorticity input is the *two-sided* differentiability of the
  vorticity slices `hasDerivAt_omega_slice_at_aux`, obtained from the one-sided data by the
  one-sided mean value theorem `hasDerivAt_of_hasDerivWithinAt_Ici`).  Then
  `hasDerivAt_pressurePotential_time_of_continuous` differentiates under the integral sign, and the
  clamping is invisible near `t`.
  Its continuity is `potTDeriv_continuousAt_aux` (`ctu_aux.PotTDeriv`): reparametrise time by a
  clamp into `[ε,S'] ∋ t`, which turns the Lamb time derivative into a *globally* continuous,
  uniformly supported field, and apply the dominated-convergence lemma
  `continuous_shifted_integral_joint`.

Finally `potFDeriv_eq_aux` writes the two partials as the derivative
`potFDeriv ω x t = (potGradCLM ω x t) ∘ fst + (potTDeriv ω x t) • snd` on `ℝ³ × ℝ`, and the
assembly above produces the `HasFDerivAt` whose continuity gives the `C¹` statement.
-/

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

theorem contDiffOn_potOn_uncurry_open {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T : ℝ}
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hgq : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (Work.FTS.PressureOn.potOn ω · t)
      (innerSL ℝ (FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t
        - Work.FTS.PressureOn.crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))) x) :
    ContDiffOn ℝ 1 (fun z : Work.FTS.PressureOn.R3 × ℝ => Work.FTS.PressureOn.potOn ω z.1 z.2)
      (Set.univ ×ˢ Set.Ioo 0 T) := by
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) :=
    (isOpen_univ : IsOpen (Set.univ : Set R3)).prod isOpen_Ioo
  -- the candidate derivative at each interior point
  have hderivAt : ∀ z ∈ (Set.univ ×ˢ Set.Ioo (0 : ℝ) T),
      HasFDerivAt (fun z : R3 × ℝ => potOn ω z.1 z.2) (potFDeriv ω z.1 z.2) z := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have hx : HasFDerivAt (fun y => potOn ω y t) (potGradCLM ω x t) x := hgq t ht x
    have ht' : HasDerivAt (fun s => potOn ω x s) (potTDeriv ω x t) t :=
      hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv x ht
    have hnhds : (Set.univ ×ˢ Set.Ioo (0 : ℝ) T : Set (R3 × ℝ)) ∈ 𝓝 (x, t) :=
      prod_mem_nhds univ_mem (isOpen_Ioo.mem_nhds ht)
    have h2 : ∀ᶠ p in 𝓝 (x, t), HasDerivAt (fun s' => potOn ω p.1 s')
        (deriv (fun s' => potOn ω p.1 s') p.2) p.2 := by
      filter_upwards [hnhds] with p hp
      rw [(hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2).deriv]
      exact hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2
    have hcont2 : ContinuousAt (fun p : R3 × ℝ => deriv (fun s' => potOn ω p.1 s') p.2)
        (x, t) := by
      refine (potTDeriv_continuousAt_aux hstrips hcurl hsupp hcontDt hderiv x ht).congr ?_
      filter_upwards [hnhds] with p hp
      exact (hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2).deriv.symm
    have hmain := hasFDerivAt_uncurry_of_partials' (q := potOn ω) (x := x) (t := t)
      (L := potGradCLM ω x t) (c := potTDeriv ω x t) hx ht' h2 hcont2
    rw [potFDeriv_eq_aux]
    simpa only [smulRight_snd_eq_smul'] using hmain
  -- the derivative field is continuous on the strip
  have hcontF : ContinuousOn (fun z : R3 × ℝ => potFDeriv ω z.1 z.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) := by
    rw [hopen.continuousOn_iff]
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have h1 : ContinuousAt (fun z : R3 × ℝ =>
        (potGradCLM ω z.1 z.2).comp (ContinuousLinearMap.fst ℝ R3 ℝ)) (x, t) :=
      (continuousAt_potGradCLM_aux hstrips hcurl x ht).clm_comp continuousAt_const
    have h2 : ContinuousAt (fun z : R3 × ℝ =>
        (potTDeriv ω z.1 z.2) • (ContinuousLinearMap.snd ℝ R3 ℝ)) (x, t) :=
      (potTDeriv_continuousAt_aux hstrips hcurl hsupp hcontDt hderiv x ht).smul continuousAt_const
    refine (h1.add h2).congr ?_
    filter_upwards with z
    exact (potFDeriv_eq_aux ω z.1 z.2).symm
  intro z hz
  exact contDiffWithinAt_one_of_hasFDerivAt (hopen.mem_nhds hz) hderivAt hcontF

end Work.FTS.PressureOn.Connect
