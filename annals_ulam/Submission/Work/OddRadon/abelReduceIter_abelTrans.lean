import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelTrans_hasDerivAt_direct

namespace Work.OddRadon

/-- If two functions agree on the open set `Ioo 0 1`, then so do their `k`-fold Abel
reductions (for any starting exponent).  The reduction involves `deriv`, which is a local
notion, and `Ioo 0 1` is open. -/
lemma abelReduceIter_congr_aux : ∀ (k : ℕ) (β : ℝ) {f g : ℝ → ℝ},
    Set.EqOn f g (Set.Ioo 0 1) →
    Set.EqOn (abelReduceIter β k f) (abelReduceIter β k g) (Set.Ioo 0 1) := by
  intro k
  induction k with
  | zero => intro β f g h; simpa using h
  | succ k ih =>
      intro β f g h
      rw [abelReduceIter_succ, abelReduceIter_succ]
      apply ih
      intro c hc
      simp only [abelReduce]
      congr 1
      exact (h.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hc)).deriv_eq

lemma abelReduceIter_congr {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Ioo 0 1)) (β : ℝ) (k : ℕ) :
    Set.EqOn (abelReduceIter β k f) (abelReduceIter β k g) (Set.Ioo 0 1) :=
  abelReduceIter_congr_aux k β h

/-- **One exponent-reduction step**: if `G` is `C¹` on `[0,1]` and `α > 0`, then
`abelReduce α (T_α G) = T_{α-1} G` on `(0,1)`. -/
lemma abelReduce_abelTrans {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) :
    Set.EqOn (abelReduce α (abelTrans α G)) (abelTrans (α - 1) G) (Set.Ioo 0 1) := by
  intro c hc
  have h := (AbelDirect.hasDerivAt_abelTrans_direct hα hG hc).deriv
  simp only [abelReduce]
  rw [h]
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hc0 : c ≠ 0 := ne_of_gt hc.1
  field_simp

theorem abelReduceIter_abelTrans {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1))
    {k : ℕ} {α : ℝ} (hα : (k : ℝ) - 1 < α) :
    Set.EqOn (abelReduceIter α k (abelTrans α G)) (abelTrans (α - k) G) (Set.Ioo 0 1) := by
  induction k generalizing α with
  | zero => intro c hc; simp
  | succ k ih =>
      intro c hc
      rw [abelReduceIter_succ]
      have hk : ((k : ℝ)) < α := by
        have h' : ((k : ℝ) + 1) - 1 < α := by exact_mod_cast hα
        linarith
      have hαk : (k : ℝ) - 1 < α - 1 := by linarith
      have hstep := abelReduce_abelTrans (α := α) (by linarith) hG
      have hred : abelReduceIter (α - 1) k (abelReduce α (abelTrans α G)) c
          = abelReduceIter (α - 1) k (abelTrans (α - 1) G) c :=
        abelReduceIter_congr hstep (α - 1) k hc
      rw [hred, ih hαk hc]
      have : (α - 1) - (k : ℝ) = α - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this]

end Work.OddRadon
