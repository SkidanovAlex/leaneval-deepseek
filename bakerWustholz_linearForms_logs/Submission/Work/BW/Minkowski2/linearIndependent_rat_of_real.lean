import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

/-- Linear independence over `ℝ` of a family of integer vectors implies linear
independence over `ℚ` of the same family (viewed in `ℚ^n`).

This is the special case of `linearIndependent_algebraMap_comp_iff` for the
algebra `ℚ → ℝ`, combined with the fact that the two families are related by
coordinatewise casting. -/
theorem linearIndependent_rat_of_real {n : ℕ} (v : Fin n → (Fin n → ℤ))
    (h : LinearIndependent ℝ (fun k : Fin n => (fun i => (v k i : ℝ)))) :
    LinearIndependent ℚ (fun k : Fin n => (fun i => (v k i : ℚ))) := by
  rw [← linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)
        (v := fun k : Fin n => fun i => (v k i : ℚ))]
  have key : (fun k : Fin n => (algebraMap ℚ ℝ) ∘ (fun i => (v k i : ℚ)))
      = (fun k : Fin n => fun i => (v k i : ℝ)) := by
    ext k i
    simp
  rw [key]
  exact h

end Work.BW.Minkowski2
