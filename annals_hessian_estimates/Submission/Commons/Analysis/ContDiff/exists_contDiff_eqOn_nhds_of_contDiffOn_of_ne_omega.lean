import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.CompletePartialOrder

open Set Metric Filter
open scoped Topology

namespace Commons.Analysis.ContDiff

theorem exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : WithTop ℕ∞) (hn : n ≠ ⊤) {φ : E → ℝ}
    {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) (hφ : ContDiffOn ℝ n φ s) :
    ∃ φ' : E → ℝ, ContDiff ℝ n φ' ∧ Filter.EventuallyEq (nhds x) φ' φ := by
  obtain ⟨n', hn'⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [← hn'] at hφ ⊢
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  have hbd : closedBall x (ε / 2) ⊆ s :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεs
  let c : ContDiffBump x :=
    { rIn := ε / 4, rOut := ε / 2, rIn_pos := by linarith,
      rIn_lt_rOut := by linarith }
  have htsupp : tsupport (c : E → ℝ) ⊆ s := by
    rw [c.tsupport_eq]
    exact hbd
  have hunion : s ∪ (tsupport (c : E → ℝ))ᶜ = univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : y ∈ tsupport (c : E → ℝ)
    · exact Or.inl (htsupp hy)
    · exact Or.inr hy
  refine ⟨(c : E → ℝ) * φ, ?_, ?_⟩
  · refine contDiff_of_contDiffOn_union_of_isOpen ?_ ?_ hunion hs
      (isClosed_tsupport (c : E → ℝ)).isOpen_compl
    · exact (c.contDiff (n := n')).contDiffOn.mul hφ
    · have h0 : ContDiffOn ℝ (n' : WithTop ℕ∞) (fun _ : E => (0 : ℝ))
          ((tsupport (c : E → ℝ))ᶜ) := contDiff_const.contDiffOn
      refine h0.congr fun y hy => ?_
      simp only [Pi.mul_apply]
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · filter_upwards [c.eventuallyEq_one] with y hy
    have hy1 : (c : E → ℝ) y = 1 := hy
    rw [Pi.mul_apply, hy1, one_mul]

end Commons.Analysis.ContDiff