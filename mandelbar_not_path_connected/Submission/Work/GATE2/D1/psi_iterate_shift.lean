import Mathlib
import Submission.Work.GATE2.PL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.D1

/-- The slit plane `slitAt v` is invariant under translation by a natural number. -/
theorem add_nat_mem_slitAt {v : ℝ} {w : ℂ} (hw : w ∈ Work.GATE2.slitAt v) (n : ℕ) :
    w + (n : ℂ) ∈ Work.GATE2.slitAt v := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    have h1 : w + ((n + 1 : ℕ) : ℂ) = w + (n : ℂ) + 1 := by push_cast; ring
    rw [h1]
    exact Work.GATE2.PL.slitAt_add_one ih

theorem psi_iterate_shift {F g : ℂ → ℂ} {c₀ : ℂ} {Pg : Set ℂ} {φa : ℂ → ℂ} {v : ℝ}
    (hPL : Work.GATE2.PrincipalParam F g c₀ Pg φa v) (N : ℕ) {w : ℂ}
    (hw : w ∈ Work.GATE2.slitAt v) :
    F^[N] (hPL.ψ w) = hPL.ψ (w + (N : ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih,
      hPL.shift (w + (N : ℂ)) (add_nat_mem_slitAt hw N)]
    congr 1
    push_cast
    ring

end Work.GATE2.D1
