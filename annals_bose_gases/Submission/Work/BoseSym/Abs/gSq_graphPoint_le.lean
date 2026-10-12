import Mathlib
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — monotonicity of `gSq` on graph points

The squared gradient norm `gSq` of the graph point of a test function is the
sum over the `3N` gradient directions `j : GIdx N` of the squared `L²` norm of
the corresponding directional derivative `x ↦ fderiv ℝ F x (kcDir N j.1 j.2)`.

If `G` has, in every direction `j` and at every point `x`, a directional
derivative of norm at most that of `F`, then each `L²` norm of a gradient
component of `G` is at most the corresponding one for `F` — by monotonicity of
the `L²` seminorm `eLpNorm` under pointwise domination, followed by
`ENNReal.toReal_mono` — and summing the (squared, hence monotone) inequalities
over `j` gives `gSq (graphPoint N L G) ≤ gSq (graphPoint N L F)`.
-/

namespace Work.BoseSym.Abs

open MeasureTheory

theorem gSq_graphPoint_le {N : ℕ} {L : ℝ} (F G : Work.BoseSym.testSub N L)
    (h : ∀ (j : Work.BoseSym.GIdx N) (x : Work.BoseSym.Conf N),
      ‖fderiv ℝ (G : Work.BoseSym.Conf N → ℝ) x (Submission.BoseGases.kcDir N j.1 j.2)‖
      ≤ ‖fderiv ℝ (F : Work.BoseSym.Conf N → ℝ) x (Submission.BoseGases.kcDir N j.1 j.2)‖) :
    Work.BoseSym.gSq (Work.BoseSym.graphPoint N L G) ≤ Work.BoseSym.gSq (Work.BoseSym.graphPoint N L F) := by
  -- every directional derivative of a test function is in `L²`
  have hmem : ∀ (H : Work.BoseSym.testSub N L) (j : Work.BoseSym.GIdx N),
      MemLp (fun x : Work.BoseSym.Conf N =>
        fderiv ℝ (H : Work.BoseSym.Conf N → ℝ) x (Submission.BoseGases.kcDir N j.1 j.2)) 2
        (Work.BoseSym.volC N) :=
    fun H j => Work.BoseSym.memLp_of_contDiff_hasCompactSupport
        (Submission.BoseGases.firstDir_contDiff H.2.1 (Submission.BoseGases.kcDir N j.1 j.2))
        (IsCompact.of_isClosed_subset (Work.BoseSym.hasCompactSupport_of_testFun H.2)
          (isClosed_tsupport _) (Submission.BoseGases.tsupport_firstDir_subset _))
  simp only [Work.BoseSym.gSq]
  refine Finset.sum_le_sum (fun j _ => ?_)
  -- the `j`-th component of `G` is dominated in `L²` by the `j`-th component of `F`
  have hkey : ‖(Work.BoseSym.graphPoint N L G).2 j‖ ≤ ‖(Work.BoseSym.graphPoint N L F).2 j‖ := by
    simp only [Work.BoseSym.graphPoint]
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono (ne_of_lt (MemLp.eLpNorm_lt_top (hmem F j)))
      (eLpNorm_mono (hmem G j).aestronglyMeasurable (fun x => h j x))
  exact pow_le_pow_left₀ (norm_nonneg _) hkey 2

end Work.BoseSym.Abs
