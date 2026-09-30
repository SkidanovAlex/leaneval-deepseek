import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Monotonicity of the successive minima `succMinBody` in the index

`Work.BW.succMinBody Λ K j` is the `j`-th successive minimum of the lattice `Λ ⊆ ℝᵈ` with
respect to the body `K`; it is the infimum of the positive levels `λ` for which the `ℝ`-span of
the lattice points of `Λ ∩ λ • K` has dimension at least `j`.

Enlarging `j` shrinks the set of admissible levels, so the infimum can only increase. This file
proves `succMinBody Λ K i ≤ succMinBody Λ K j` for `i ≤ j`, under the only extra hypothesis that
the level `succMinBody Λ K j` does not vanish (so that the defining set is nonempty; the empty
case is handled by `Real.sInf_empty`).  No convexity or symmetry of `K` is needed.
-/

namespace Work.BW.Minkowski2

open scoped Pointwise

theorem succMinBody_mono {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    {i j : ℕ} (hij : i ≤ j) (hj : Work.BW.succMinBody Λ K j ≠ 0) :
    Work.BW.succMinBody Λ K i ≤ Work.BW.succMinBody Λ K j := by
  -- Enlarging the index shrinks the defining set of admissible levels.
  have hsub : {lam : ℝ | 0 < lam ∧ j ≤ Module.finrank ℝ
        (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)))}
      ⊆ {lam : ℝ | 0 < lam ∧ i ≤ Module.finrank ℝ
        (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)))} :=
    fun lam h => ⟨h.1, le_trans hij h.2⟩
  -- The hypothesis `succMinBody Λ K j ≠ 0` forces the defining set to be nonempty.
  have hne : ({lam : ℝ | 0 < lam ∧ j ≤ Module.finrank ℝ
        (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)))} : Set ℝ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    exact hj (by unfold Work.BW.succMinBody; rw [hempty, Real.sInf_empty])
  -- Every admissible level is positive, hence the defining set is bounded below by `0`.
  have hbdd : BddBelow ({lam : ℝ | 0 < lam ∧ i ≤ Module.finrank ℝ
        (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)))} : Set ℝ) :=
    ⟨0, fun l hl => le_of_lt hl.1⟩
  unfold Work.BW.succMinBody
  exact csInf_le_csInf hbdd hne hsub

end Work.BW.Minkowski2
