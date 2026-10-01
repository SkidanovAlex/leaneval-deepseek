import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Topology.ContinuousOn

open Set

theorem indicator_Ioo_continuous {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0) :
    Continuous (fun v : ℝ => if v ∈ Set.Ioo (0:ℝ) x₀ then f v else 0) := by
  classical
  have hfront : frontier {x : ℝ | x ∈ Set.Ioo (0:ℝ) x₀} = ({0, x₀} : Set ℝ) :=
    frontier_Ioo hx₀
  apply continuous_if
  · intro a ha
    rw [hfront] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with h | h
    · rw [h]; exact hf0
    · rw [h]; exact hvan x₀ le_rfl
  · rw [show closure {x : ℝ | x ∈ Set.Ioo (0:ℝ) x₀} = Set.Icc 0 x₀ from
        closure_Ioo hx₀.ne]
    exact hcont
  · exact continuousOn_const

end Commons.Topology.ContinuousOn