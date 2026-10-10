import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

theorem powLinearDependence {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (x : L) :
    ∃ g : Fin (Module.finrank F L + 1) → F,
      (∃ i, g i ≠ 0) ∧
        ∑ i : Fin (Module.finrank F L + 1), algebraMap F L (g i) * x ^ ((i : ℕ)) = 0 := by
  -- The `finrank F L + 1` powers `x ^ 0, …, x ^ finrank` are too many to be
  -- linearly independent in the `finrank F L`-dimensional space `L`.
  by_contra h
  push Not at h
  have hli : LinearIndependent F (fun i : Fin (Module.finrank F L + 1) => x ^ (i : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hi
    exact h g ⟨i, hi⟩ (by simpa only [Algebra.smul_def] using hg)
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end Work.MotV5.Nodes
