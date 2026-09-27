import Mathlib

namespace Work.EKLComp

theorem birkhoffSum_indicator_eq_of_forall_mem {X : Type*} (T : X → X) (U : Set X) (h : X → ℝ)
    (n : ℕ) (x : X) (hx : ∀ k, k < n → T^[k] x ∈ U) :
    birkhoffSum T (U.indicator h) n x = birkhoffSum T h n x := by
  simp only [birkhoffSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Set.indicator_of_mem (hx k (Finset.mem_range.mp hk))]

end Work.EKLComp
