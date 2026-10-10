import Mathlib
import Submission.Work.MotV.TpAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

theorem tp_max {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {h : F} (hh : h ≠ 0) {y : Fin 5 → F} (hy : y ≠ 0) :
    ∃ j : Fin 5, (∀ i, wt v h y i ≤ wt v h y j) ∧ 0 < wt v h y j := by
  -- `y ≠ 0` gives a coordinate whose value is nonzero, hence a positive weight
  obtain ⟨i0, hi0⟩ : ∃ i0, y i0 ≠ 0 := Function.ne_iff.mp hy
  -- the maximum of the finite family `wt v h y ·`
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun i => wt v h y i) ⟨i0, Finset.mem_univ i0⟩
  refine ⟨j, fun i => hj i (Finset.mem_univ i), ?_⟩
  have hpos : 0 < wt v h y i0 := by
    rw [wt_pos_iff, wt]
    exact mul_ne_zero (pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hh))
      (pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hi0))
  exact lt_of_lt_of_le hpos (hj i0 (Finset.mem_univ i0))

end Work.MotV
