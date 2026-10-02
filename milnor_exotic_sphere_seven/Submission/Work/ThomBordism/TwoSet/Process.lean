import Mathlib
import Submission.Work.ThomBordism.TwoSet.spreadCell
import Submission.Work.ThomBordism.TwoSet.CollarSubdivision
import Submission.Work.ThomBordism.TwoSet.CompressBasic
import Submission.Work.ThomBordism.TwoSet.compresses_homeo
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.ThomBordism.TwoSet.keyLemma

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

/-!
# The cell-by-cell compression over the collared subdivision

`processCells`: if `f : I^j → X` is `U`-valued on the boundary of the cube and the boxes of the
collared subdivision are labelled `U`/`V` (with the `V`-labelled boxes at scaled distance `≥ 2/N`
from `∂I^j`), and if the pairs `(V, V ∩ U)` and `(U, U ∩ V)` have the compression property in all
dimensions `≤ j`, then `f` is homotopic relative to `∂I^j` to a map into `U`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {X : Type*} [TopologicalSpace X] {j N : ℕ}

/-- The `V`-region: the union of the `V`-labelled boxes. -/
def vReg (lab : (Fin j → Fin N) → Bool) : Set (IC j) :=
  {x | ∃ m : Fin j → Fin N, lab m = true ∧ x ∈ boxSet m}

theorem cellSet_subset_of_box {c : CellIdx j N} {m : Fin j → Fin N} (hm : cellSet c ⊆ boxSet m)
    {x : IC j} (hx : x ∈ cellSet c) : x ∈ boxSet m := hm hx

/-- **A cell is contained in the box of its relative interior.** -/
theorem exists_box_of_cell (hN : 1 ≤ N) (c : CellIdx j N) (x : IC j) (hx : x ∈ cellSet c) :
    ∃ m : Fin j → Fin N, cellSet c ⊆ boxSet m := by
  classical
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  let m : Fin j → Fin N := fun i => ⟨min (N-1) (c.lo i), lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
  refine ⟨m, fun y hy i => ?_⟩
  have hle : (c.lo i : ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (le_trans (c.hle i) (c.hhi i))
  have hyc := hy i
  have hmval : ((m i : ℕ) : ℝ) = ((min (N-1) (c.lo i) : ℕ) : ℝ) := rfl
  rw [hmval]
  have h1 : ((min (N-1) (c.lo i) : ℕ) : ℝ) ≤ (c.lo i : ℝ) := by
    exact_mod_cast min_le_right (N-1) (c.lo i)
  constructor
  · have h3 := (div_le_iff₀ hNpos).mp hyc.1
    nlinarith [h1, h3]
  · rcases le_or_gt (c.lo i) (N-1) with h | h
    · have hmin : min (N-1) (c.lo i) = c.lo i := min_eq_right h
      rw [hmin]
      have h4 := (le_div_iff₀ hNpos).mp hyc.2
      have hhi : (c.hi i : ℝ) ≤ (c.lo i : ℝ) + 1 := by
        have hs := c.hstep i
        have : (c.hi i : ℝ) ≤ ((c.lo i + 1 : ℕ) : ℝ) := by exact_mod_cast hs
        push_cast at this; linarith
      linarith
    · have hmin : min (N-1) (c.lo i) = N-1 := min_eq_left (le_of_lt h)
      rw [hmin]
      have hy1 : (y i : ℝ) ≤ 1 := (y i).2.2
      have hcast : (((N - 1 : ℕ)) : ℝ) = (N:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
      rw [hcast]
      nlinarith

end Work.ThomBordism.TwoSet
