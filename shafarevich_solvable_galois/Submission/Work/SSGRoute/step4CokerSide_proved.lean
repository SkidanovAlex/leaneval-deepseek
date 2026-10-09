import Mathlib
import Submission.Work.SSGRoute.step4CokerSideDefs
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.NodeS37.yExistsV2Node
import Submission.Work.SSGRoute.step4_x_exists_proved
import Submission.Work.SSGRoute.step4_x_old_ramification
import Submission.Work.SSGRoute.step4_local_clauses
import Submission.Work.SSGRoute.no_two_torsion_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The coker side of Step 4, assembled independently of `step4_x_exists`

This is `Work.SSGRoute.step4CokerSide_assembled`
(`Submission/Work/SSGRoute/step4CokerAssembly.lean`) with the class `x` supplied by
`Work.SSGRoute.step4_x_exists_proved` (`step4_x_exists_proved.lean`) instead of by
`Work.SSGRoute.step4_x_exists`, whose proof does not compile (its `x = 0` approach needs the
corestriction of `y` to vanish at *every* place of `S` splitting in `K`, which fails at the places
of `Tnew`).  The two statements of the `x`-node are the same, so the assembly body is unchanged.

The remaining input of this module is `Work.SSGRoute.step4_y_exists_v2` — the Step-4 datum `y`,
restated with the extra hypothesis `2 ≤ i` of the redesigned route
(`_NOTE_STEP4_DESIGN.md` §1.5): the case `(i,j) = (1,1)` is not proved by Step 4 at all but by
`Work.SSGRoute.scholz_two_one` at the level of `scholz_succ_of_properStage`. -/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-- **The coker side of Step 4, assembled.** -/
theorem step4CokerSide_proved (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : 2 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j) (n : ℕ) (hn : 1 ≤ n) :
    Step4CokerSide p K n i j := by
  classical
  obtain ⟨D, y, hY⟩ := step4_y_exists_v2_node p K n i j hj hji hi hμ hP hn
  obtain ⟨x, hxcocycle, hxloc, hxsplit, hxnot, hinv, hxinertia, hcyc7⟩ :=
    step4_x_exists_proved p K n i j hj hji hμ D y hY
  have hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K) σ • x τ :=
    fun σ τ => hxcocycle σ trivial τ trivial
  have hyS := hY.2.2.1
  have hyT := hY.2.2.2.1
  have hy0 := hY.2.2.2.2.1
  have hyT0 := hY.2.2.2.2.2.1
  have hy1 : y 1 = 0 := by
    have h : y 1 = y 1 + y 1 := by
      simpa using hY.1 1 (K.fixingSubgroup.one_mem) 1 (K.fixingSubgroup.one_mem)
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  have hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0 := by
    intro c hc hc1
    rw [no_two_torsion_fixingSubgroup p K i (le_trans hj hji) hμ c hc1 hc, hy1]
  have hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (D.psi σ)
      = Work.SSGRoute.restrict K σ := by
    intro σ
    simpa [Step4CokerData.psi, flowQuot_flowGroupMap] using D.data.2.2.1.2.2 σ
  have hxold := step4_x_old_ramification p K n i j D y hY x hxmul hxsplit hxnot
  obtain ⟨hreal, hdich⟩ := step4_local_clauses p K n i j hj hji hμ D y hY x hψquot hxmul hxloc
    hxsplit hxnot hxinertia hinv hcyc7 hxold
  exact ⟨D.m, D.hm, D.hnm, D.Φ, D.φm, D.ψm, D.data, D.Λ, D.fdΛ, D.galΛ, D.hKΛ,
    D.hΛker, D.S, D.T0, D.sec, y, x, hψquot, hxmul, D.hSfin, D.hSram, D.hsec, hyT, hy0,
    hyT0, D.hT0S, D.hT0split, D.hT0gen, D.hT0cyc, hxloc, hxsplit, hxnot, hxinertia, hinv,
    hcyc7, hreal, hdich⟩

end Work.SSGRoute
