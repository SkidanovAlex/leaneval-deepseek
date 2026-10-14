import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtDeriv
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotTDeriv
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux2
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.normSlopePhysVelLe
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1LhatO
import Submission.Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO
import Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds

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
