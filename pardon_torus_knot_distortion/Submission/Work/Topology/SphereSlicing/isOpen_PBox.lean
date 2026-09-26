import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# Pardon's box is open

`Submission.PBox r c σ` is the open box with centre `c`, side lengths `boxSide i * r` in the
coordinate directions `σ i`.  Each coordinate constraint `|y (σ i) - c (σ i)| < boxSide i * r`
cuts out an open slab (the preimage of an open half-line under the continuous map
`y ↦ |y (σ i) - c (σ i)|`), and there are only the three constraints `i : Fin 3`; hence the box
is open.  (No hypothesis on the sign of `r` is needed: for `r ≤ 0` the box is empty, since then
`boxSide i * r ≤ 0 ≤ |·|`.)
-/

namespace Work.Topology.SphereSlicing

theorem isOpen_PBox (r : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) :
    IsOpen (Submission.PBox r c σ) := by
  have hset : Submission.PBox r c σ =
      ⋂ i : Fin 3,
        {y : LeanEval.KnotTheory.PardonDistortion.R3 |
          |y (σ i) - c (σ i)| < Submission.boxSide i * r} := by
    ext y
    simp [Submission.mem_PBox]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => ?_
  have h1 : Continuous fun y : LeanEval.KnotTheory.PardonDistortion.R3 => y (σ i) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)
  have h2 : Continuous fun y : LeanEval.KnotTheory.PardonDistortion.R3 =>
      y (σ i) - c (σ i) := h1.sub continuous_const
  have h3 : Continuous fun y : LeanEval.KnotTheory.PardonDistortion.R3 =>
      |y (σ i) - c (σ i)| := continuous_abs.comp h2
  exact isOpen_lt h3 continuous_const

end Work.Topology.SphereSlicing
