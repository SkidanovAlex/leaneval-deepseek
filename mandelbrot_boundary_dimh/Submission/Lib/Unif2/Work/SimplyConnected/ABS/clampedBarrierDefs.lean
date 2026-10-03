import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg

/-!
# The clamped barrier

Let `u` be a local barrier at a boundary point `p` of `Ω` (superharmonic on `Ω ∩ V`, positive
there, continuous on `V`, with `u p = 0`).  The *clamped barrier* is

`clampedBarrier u V C x = if x ∈ V then min (u x) C else C`.

It agrees with the (bounded) barrier `min (u ·) C` inside `V`, equals the constant `C` outside `V`,
is upper semicontinuous everywhere (it jumps *up* to `C` on `∂V`) and satisfies the circle
mean-value inequality of superharmonic type at every point of any set contained in `Ω`; it is
nonnegative there, and it vanishes at `p` (where `p ∉ Ω`, so the `else` branch is not used).
This is the function that the design note `MajorantRegDesign.lean` §1 clamps; its properties are
recorded in `Work.SimplyConnected.ABS.clampedBarrier_properties`.

Nothing of mathematical substance lives here.
-/

open Filter Set
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.ABS

open Classical

variable {X : Type*} [TopologicalSpace X]

/-- The barrier `u` clamped above by the constant `C` inside `V`, and set equal to `C` outside
`V`. -/
def clampedBarrier (u : X → ℝ) (V : Set X) (C : ℝ) : X → ℝ :=
  fun x => if x ∈ V then min (u x) C else C

@[simp]
theorem clampedBarrier_of_mem {u : X → ℝ} {V : Set X} {C : ℝ} {x : X} (hx : x ∈ V) :
    clampedBarrier u V C x = min (u x) C := by
  rw [clampedBarrier, if_pos hx]

@[simp]
theorem clampedBarrier_of_not_mem {u : X → ℝ} {V : Set X} {C : ℝ} {x : X} (hx : x ∉ V) :
    clampedBarrier u V C x = C := by
  rw [clampedBarrier, if_neg hx]

theorem clampedBarrier_le {u : X → ℝ} {V : Set X} {C : ℝ} (x : X) :
    clampedBarrier u V C x ≤ C := by
  by_cases hx : x ∈ V
  · rw [clampedBarrier_of_mem hx]; exact min_le_right _ _
  · rw [clampedBarrier_of_not_mem hx]

end Work.SimplyConnected.ABS
