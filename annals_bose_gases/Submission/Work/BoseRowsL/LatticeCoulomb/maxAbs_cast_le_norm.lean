import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowsL.LatticeCoulomb.maxAbsDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.maxAbs_cast_le_norm`

The `ℓ^∞` norm of a lattice vector is dominated by its Euclidean norm:
`maxAbs n ≤ ‖nvec n‖`.  Concretely, if `i` maximises `|n i|` over the three
coordinates then `maxAbs n = |n i|` and `|n i| = ‖(nvec n).ofLp i‖ ≤ ‖nvec n‖`,
the last inequality being the general fact that a coordinate of a `PiLp` element
is dominated by its norm (`PiLp.norm_apply_le`).

This is what converts an `ℓ^∞`-slicing of the lattice sum into a Euclidean one:
`‖nvec n‖ ≥ maxAbs n ≥ 1` for `n ≠ 0`.
-/

namespace Work.BoseRowsL.LatticeCoulomb

/-- A single coordinate of `nvec n` is at most the norm of `nvec n`. -/
lemma natAbs_le_norm_nvec (n : Fin 3 → ℤ) (i : Fin 3) :
    ((n i).natAbs : ℝ) ≤ ‖nvec n‖ := by
  have hcoord : ‖(nvec n).ofLp i‖ ≤ ‖nvec n‖ := PiLp.norm_apply_le _ _
  rw [nvec_apply, Real.norm_eq_abs] at hcoord
  calc ((n i).natAbs : ℝ) = |((n i : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
    _ ≤ ‖nvec n‖ := hcoord

theorem maxAbs_cast_le_norm (n : Fin 3 → ℤ) :
    (Work.BoseRowsL.LatticeCoulomb.maxAbs n : ℝ) ≤ ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3))
    ⟨0, Finset.mem_univ 0⟩ fun i => (n i).natAbs
  rw [maxAbs, hi]
  exact natAbs_le_norm_nvec n i

end Work.BoseRowsL.LatticeCoulomb
