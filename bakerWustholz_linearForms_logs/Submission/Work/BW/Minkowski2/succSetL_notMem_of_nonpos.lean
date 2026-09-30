import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

/-- No level `t ≤ 0` qualifies in the definition of `succMinL F j` when `1 ≤ j`: the lattice points
of `F`-norm `≤ t ≤ 0` are all `0` (by nonnegativity together with `F x = 0 → x = 0`), so their real
span is trivial and has dimension `0 < j`. -/
theorem succSetL_notMem_of_nonpos {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F)
    {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ≤ 0) :
    ¬ (j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t})) := by
  intro hmem
  have hsub : {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t} ⊆ {0} := by
    rintro x ⟨-, hx⟩
    have hx0 : F x = 0 := le_antisymm (le_trans hx ht) (hF.nonneg x)
    simp [(hF.eq_zero x).mp hx0]
  have hbot : Submodule.span ℝ {x : Fin n → ℝ |
      (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t} = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [Submodule.span_le]
    exact hsub
  rw [hbot, finrank_bot] at hmem
  omega

end Work.BW.Minkowski2
