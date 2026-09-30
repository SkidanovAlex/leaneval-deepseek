import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `off` is invariant under translation by an integer: `Int.fract` is. -/
theorem off_intCast_add (t : ℝ) (n : ℤ) : off (t + (n : ℝ)) = off t := by
  unfold off
  rw [Int.fract_add_intCast]

/-- The coordinates of `ofInt3 m` are the integers `m i`, as reals. -/
theorem ofInt3_apply (m : Fin 3 → ℤ) (i : Fin 3) : ofInt3 m i = ((m i : ℤ) : ℝ) := by
  fin_cases i <;> simp [ofInt3]

theorem beta_add_int (x : E3) (m : Fin 3 → ℤ) : beta (x + ofInt3 m) = beta x := by
  have h : (∑ i : Fin 3, (off ((x + ofInt3 m) i)) ^ 2)
      = ∑ i : Fin 3, (off (x i)) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [PiLp.add_apply, ofInt3_apply, off_intCast_add]
  simp only [beta, h]

end Work.Cusp
