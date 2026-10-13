/-
# Joint `C¹` of the reconstructed potential at the boundary time `t = 0`

`Work.FTS.PressureOn.Connect.contDiffWithinAt_potOn_at_zero`: the uncurried reconstructed
potential `(x,t) ↦ potOn ω x t` is `C¹` *within the closed half strip* `ℝ³ × [0,T)` at every
boundary point `(x,0)`.

## The route

The strip data are one sided, so the relevant "time derivative at `0`" is the *right* derivative,
which is not Mathlib's two sided `deriv` (`timeDeriv`) — the latter is the junk value `0` when the
left and right derivatives differ, and the values of `ω` at negative times are unconstrained by the
hypotheses.  The objects `Connect/BoundaryTime.lean` therefore provides are

* `tblock ω T x` — the right time derivative of the velocity slice at `0`;
* `dtLamb ω T y` — the right time derivative of the Lamb vector at `0`;
* `lambExt ω T` — the Lamb vector retracted in time (affine with slope `dtLamb` on `(-∞,0]` and
  equal to `lamb` on `[0,∞)`), so that its two sided `timeDeriv` at `0` *is* `dtLamb`;
* `potTDerivExt ω T`, `potGradExt ω T` — the time and space derivatives of the potential extended
  to the boundary, and `potFDerivExt ω T` the resulting candidate derivative.

The pieces are proved in the modules `BoundaryTime/ExtData`, `BoundaryTime/ExtDeriv`,
`BoundaryTime/BdryAbstract` and `BoundaryTime/BdryDeriv` imported below; the present file only
assembles them: `contDiffOn_succ_iff_hasFDerivWithinAt` gives `ContDiffOn ℝ 1` on the box
`bbox x T` from the interior and boundary derivatives, and `contDiffWithinAt_iff_contDiffOn_nhds`
converts that into the requested `ContDiffWithinAt`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_potOn_slice
import Submission.Work.FTS.PressureOn.Connect.contDiffWithinAt_one_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open
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
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Grad
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotOnTime
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotTDeriv
import Submission.Work.FTS.PressureOn.Connect.omega_strip_continuousOn
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtDeriv
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.BdryDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Connect

noncomputable section

theorem contDiffWithinAt_potOn_at_zero {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T : ℝ} (hT : 0 < T)
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
    ∀ x : Work.FTS.PressureOn.R3, ContDiffWithinAt ℝ 1
      (fun z : Work.FTS.PressureOn.R3 × ℝ => Work.FTS.PressureOn.potOn ω z.1 z.2)
      (Set.univ ×ˢ Set.Ico 0 T) (x, 0) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hT2T : T / 2 ≤ T := by linarith
  have hgq' : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (potOn ω · t) (potGradCLM ω x t) x :=
    fun t ht x => hgq t ht x
  intro x
  -- the box is a within-neighbourhood of `(x,0)`
  have hmem : bbox x T ∈ 𝓝[Set.univ ×ˢ Set.Ico 0 T] (x, 0) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Metric.ball x 1 ×ˢ Set.Ioo (-1) (T / 2), ?_, ?_⟩
    · exact prod_mem_nhds (Metric.ball_mem_nhds x one_pos)
        (isOpen_Ioo.mem_nhds ⟨by linarith, hT2⟩)
    · rintro ⟨z, σ⟩ ⟨⟨hz, hσ⟩, ⟨-, hσIco⟩⟩
      exact ⟨hz, hσIco.1, hσ.2⟩
  -- `C¹` on the box
  have hcd : ContDiffOn ℝ 1 (fun p : R3 × ℝ => potOn ω p.1 p.2) (bbox x T) := by
    have hidx : ((0 : WithTop ENat) + 1) = (1 : WithTop ENat) := by simp
    have hiff := contDiffOn_succ_iff_hasFDerivWithinAt (𝕜 := ℝ)
      (f := fun p : R3 × ℝ => potOn ω p.1 p.2) (s := bbox x T)
      (n := (0 : WithTop ENat)) (by simp)
    rw [hidx] at hiff
    rw [hiff]
    intro z hz
    refine ⟨bbox x T, ?_, fun h => absurd h (by simp), potFDerivExt ω T, ?_, ?_⟩
    · rw [Set.insert_eq_of_mem hz]; exact self_mem_nhdsWithin
    · intro w hw
      rcases eq_or_lt_of_le hw.2.1 with h0 | hpos
      · have hw0 : w = (w.1, 0) := by
          refine Prod.ext rfl ?_
          exact h0.symm
        rw [hw0]
        exact hasFDerivWithinAt_potOn_uncurry_boundary (α := α) hT hstrips hcurl hsupp hcontDt
          hderiv hgq' x w.1 hw.1
      · refine (hasFDerivAt_potOn_uncurry_interior (α := α) hstrips hcurl hsupp hcontDt hderiv
          hgq' (y := w.1) (t := w.2) ⟨hpos, lt_of_lt_of_le hw.2.2 hT2T⟩).hasFDerivWithinAt
    · rw [contDiffOn_zero]
      exact (potFDerivExt_continuousOn_strip (α := α) hT hstrips hcurl hsupp hcontDt
        hderiv).mono fun p hp => ⟨trivial, hp.2⟩
  rw [contDiffWithinAt_iff_contDiffOn_nhds (by simp)]
  refine ⟨bbox x T, ?_, hcd⟩
  rwa [Set.insert_eq_of_mem (show (x, 0) ∈ Set.univ ×ˢ Set.Ico 0 T from ⟨trivial, le_refl 0, hT⟩)]

end

end Work.FTS.PressureOn.Connect
