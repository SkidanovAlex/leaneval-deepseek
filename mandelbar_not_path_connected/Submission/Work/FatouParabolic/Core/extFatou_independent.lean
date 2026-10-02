import Mathlib
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-!
# The extended Fatou coordinate is independent of the tap time

`Work.FatouParabolic.extFatou fl z` is defined by running the orbit of `z` into the petal `fl.Pa`
and reading off `fl.φa` there, subtracting the number of steps taken (`entryTime`).  The point of
the notion is that the result does not depend on the (arbitrary) choice of the tap time, and this
file records the corresponding statement: **if `F^n z` and `F^m z` both lie in the petal `fl.Pa`,
then `φa (F^n z) - n = φa (F^m z) - m`**.

The proof is the Abel equation of the repaired flower (`ParabolicFlowerFix.φa_shift_iterate`):
`φa (F^k w) = φa w + k` for every `w ∈ Pa`.  If `n ≤ m`, then `F^m z = F^(m-n) (F^n z)` and the
Abel equation applied at `w = F^n z` gives `φa (F^m z) = φa (F^n z) + (m - n)`; the case `m ≤ n`
is symmetric.  Nothing about the entry time is needed: this is precisely what makes `extFatou`
well defined, and it is also what identifies the extended coordinate with a tap time of the orbit.

Note that the hypothesis `hz : z ∈ puncturedBasin F z₀` is *not* used by the argument — the
statement is purely about the iterate lying in the petal — but it is part of the requested
statement, since that is the setting in which `extFatou` is used.
-/

set_option linter.unusedVariables false in
theorem extFatou_independent {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) {z : ℂ}
    (hz : z ∈ Work.FatouParabolic.puncturedBasin F z₀) {n m : ℕ}
    (hn : (F^[n]) z ∈ fl.Pa) (hm : (F^[m]) z ∈ fl.Pa) :
    fl.φa ((F^[n]) z) - (n : ℂ) = fl.φa ((F^[m]) z) - (m : ℂ) := by
  rcases le_total n m with hnm | hmn
  · -- `n ≤ m`: tap the orbit at time `n` and iterate `d = m - n` more steps.
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hstep : (F^[n + d]) z = (F^[d]) ((F^[n]) z) := by
      rw [Nat.add_comm]
      exact Function.iterate_add_apply F d n z
    rw [hstep, fl.φa_shift_iterate hn d]
    push_cast
    ring
  · -- `m ≤ n`: the symmetric case.
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have hstep : (F^[m + d]) z = (F^[d]) ((F^[m]) z) := by
      rw [Nat.add_comm]
      exact Function.iterate_add_apply F d m z
    rw [hstep, fl.φa_shift_iterate hm d]
    push_cast
    ring

end Work.FatouParabolic.Core
