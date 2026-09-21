import Submission.Work.VolterraLong.Weighted.wdist_triangle

/-!
# Metric properties of the weighted distance

`wdist lam · C` is 1-Lipschitz for the ordinary supremum distance, so the
weighted balls are closed, and a sequence which is Cauchy for `wdist` converges
(completeness of the sup-norm space transferred across the equivalence of the
two metrics).
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ} {lam : ℝ}

theorem wdist_le_dist_add_dist (hlam : 0 ≤ lam)
    (Z Z' C : BoundedContinuousFunction (Set.Icc a b) E) :
    wdist lam Z C ≤ wdist lam Z' C + dist Z Z' := by
  have h := Work.VolterraLong.Weighted.wdist_triangle hlam Z Z' C
  have h2 := wdist_le_dist hlam Z Z'
  linarith

theorem lipschitzWith_wdist (hlam : 0 ≤ lam)
    (C : BoundedContinuousFunction (Set.Icc a b) E) :
    LipschitzWith 1 (fun Z : BoundedContinuousFunction (Set.Icc a b) E => wdist lam Z C) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro Z Z'
  have h1 : wdist lam Z C - wdist lam Z' C ≤ dist Z Z' := by
    linarith [wdist_le_dist_add_dist hlam Z Z' C]
  have h2 : wdist lam Z' C - wdist lam Z C ≤ dist Z Z' := by
    linarith [wdist_le_dist_add_dist hlam Z' Z C, dist_comm Z Z']
  simp only [NNReal.coe_one, one_mul]
  rw [Real.dist_eq, abs_sub_le_iff]
  exact ⟨h1, h2⟩

theorem isClosed_wdist_ball (hlam : 0 ≤ lam)
    (C : BoundedContinuousFunction (Set.Icc a b) E) (R : ℝ) :
    IsClosed {Z : BoundedContinuousFunction (Set.Icc a b) E | wdist lam Z C ≤ R} :=
  IsClosed.preimage (lipschitzWith_wdist hlam C).continuous isClosed_Iic

theorem exists_tendsto_of_wdist_cauchy [CompleteSpace E] (hab : a ≤ b) (hlam : 0 ≤ lam)
    {u : ℕ → BoundedContinuousFunction (Set.Icc a b) E}
    (h : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, wdist lam (u m) (u n) < ε) :
    ∃ z, Tendsto u atTop (𝓝 z) := by
  have hc : 0 < Real.exp (-(lam * (b - a))) := Real.exp_pos _
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε * Real.exp (-(lam * (b - a)))) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have h2 := exp_mul_dist_le_wdist hab hlam (u m) (u n)
    nlinarith [h1, h2, hc]
  exact cauchySeq_tendsto_of_complete hcauchy

/-- **`wdist` is a genuine metric**: it is nonnegative, vanishes exactly on the
diagonal, is symmetric and satisfies the triangle inequality. -/
theorem wdist_metric (hab : a ≤ b) (hlam : 0 ≤ lam) :
    (∀ Z : BoundedContinuousFunction (Set.Icc a b) E, wdist lam Z Z = 0) ∧
    (∀ Z W : BoundedContinuousFunction (Set.Icc a b) E, 0 ≤ wdist lam Z W) ∧
    (∀ Z W : BoundedContinuousFunction (Set.Icc a b) E, wdist lam Z W = wdist lam W Z) ∧
    (∀ Z W : BoundedContinuousFunction (Set.Icc a b) E, wdist lam Z W = 0 ↔ Z = W) ∧
    (∀ Z W U : BoundedContinuousFunction (Set.Icc a b) E,
      wdist lam Z U ≤ wdist lam Z W + wdist lam W U) :=
  ⟨wdist_self, fun _ _ => wdist_nonneg _ _, fun _ _ => wdist_comm _ _,
    fun Z W => wdist_eq_zero_iff hab hlam Z W,
    fun Z W U => Work.VolterraLong.Weighted.wdist_triangle hlam Z W U⟩

/-- The weighted distance and the supremum distance are equivalent:
`e^{-λ(b-a)} ‖Z - W‖_∞ ≤ wdist lam Z W ≤ ‖Z - W‖_∞`. -/
theorem wdist_equiv_dist (hab : a ≤ b) (hlam : 0 ≤ lam)
    (Z W : BoundedContinuousFunction (Set.Icc a b) E) :
    Real.exp (-(lam * (b - a))) * dist Z W ≤ wdist lam Z W ∧
      wdist lam Z W ≤ dist Z W :=
  ⟨exp_mul_dist_le_wdist hab hlam Z W, wdist_le_dist hlam Z W⟩

/-- The sup-norm space of continuous functions on a compact interval with values
in a Banach space is complete (Mathlib's instance, recorded here for the record). -/
theorem completeSpace_bcf [CompleteSpace E] :
    CompleteSpace (BoundedContinuousFunction (Set.Icc a b) E) :=
  inferInstance

/-- The weighted ball `{Z | wdist lam Z C ≤ R}` is complete for the weighted
distance: a sequence in it which is Cauchy for `wdist` has a limit in it. -/
theorem exists_tendsto_of_wdist_cauchy_in_ball [CompleteSpace E] (hab : a ≤ b) (hlam : 0 ≤ lam)
    {C : BoundedContinuousFunction (Set.Icc a b) E} {R : ℝ}
    {u : ℕ → BoundedContinuousFunction (Set.Icc a b) E}
    (h : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, wdist lam (u m) (u n) < ε)
    (hu : ∀ n, wdist lam (u n) C ≤ R) :
    ∃ z ∈ {Z : BoundedContinuousFunction (Set.Icc a b) E | wdist lam Z C ≤ R},
      Tendsto u atTop (𝓝 z) := by
  obtain ⟨z, hz⟩ := exists_tendsto_of_wdist_cauchy hab hlam h
  exact ⟨z, (isClosed_wdist_ball hlam C R).mem_of_tendsto hz (Eventually.of_forall hu), hz⟩

end Work.VolterraLong


