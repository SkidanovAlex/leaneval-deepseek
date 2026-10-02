import Mathlib
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The extended Fatou coordinate of petal data is independent of the tap time

`Work.FatouParabolic.pdExtFatou pd z` is defined by running the orbit of `z` into the petal
`pd.Pa` and reading off `pd.φa` there, subtracting the number of steps taken
(`pdEntryTime`).  The point of the notion is that the result does not depend on the (arbitrary)
choice of the tap time, and this file records the corresponding statement: **if `F^n z` and
`F^m z` both lie in the petal `pd.Pa`, then `φa (F^n z) - n = φa (F^m z) - m`**.

This is the petal-data analogue of `Work.FatouParabolic.Core.extFatou_independent` (which is the
same statement for `ParabolicFlowerFix`), and the proof is the same: the iterated Abel equation
`pd.φa ((F^[k]) w) = pd.φa w + k` for `w ∈ pd.Pa`, proved here as `PetalData.φa_shift_iterate`
from the field `PetalData.φa_shift` and the invariance `PetalData.mapsTo_Pa`.  If `n ≤ m`, then
`F^m z = F^(m-n) (F^n z)` and the Abel equation applied at `w = F^n z` gives
`φa (F^m z) = φa (F^n z) + (m - n)`; the case `m ≤ n` is symmetric.

Nothing about the entry time is needed: this is precisely what makes `pdExtFatou` well defined.
-/

namespace Work.FatouParabolic

/-- The shifted Abel equation of petal data, iterated: `φa (F^n z) = φa z + n` for `z` in the
petal.  Proved from `PetalData.φa_shift` by induction, using `PetalData.mapsTo_Pa` to know that
the orbit stays in the petal. -/
theorem PetalData.φa_shift_iterate {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) {z : ℂ}
    (hz : z ∈ pd.Pa) (k : ℕ) : pd.φa ((F^[k]) z) = pd.φa z + (k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      pd.φa_shift _ (Work.FatouCoord.mapsTo_iterate_of_mapsTo pd.mapsTo_Pa k hz), ih]
    push_cast
    ring

end Work.FatouParabolic

namespace Work.FatouParabolic.Core

theorem pdExtFatou_independent {F : ℂ → ℂ} {z₀ : ℂ} (pd : Work.FatouParabolic.PetalData F z₀)
    {z : ℂ} {n m : ℕ} (hn : (F^[n]) z ∈ pd.Pa) (hm : (F^[m]) z ∈ pd.Pa) :
    pd.φa ((F^[n]) z) - (n : ℂ) = pd.φa ((F^[m]) z) - (m : ℂ) := by
  rcases le_total n m with hnm | hmn
  · -- `n ≤ m`: tap the orbit at time `n` and iterate `d = m - n` more steps.
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hstep : (F^[n + d]) z = (F^[d]) ((F^[n]) z) := by
      rw [Nat.add_comm]
      exact Function.iterate_add_apply F d n z
    rw [hstep, PetalData.φa_shift_iterate pd hn d]
    push_cast
    ring
  · -- `m ≤ n`: the symmetric case.
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have hstep : (F^[m + d]) z = (F^[d]) ((F^[m]) z) := by
      rw [Nat.add_comm]
      exact Function.iterate_add_apply F d m z
    rw [hstep, PetalData.φa_shift_iterate pd hm d]
    push_cast
    ring

end Work.FatouParabolic.Core
