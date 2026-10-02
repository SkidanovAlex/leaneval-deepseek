import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Basin.mapsTo_puncturedBasin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open Filter
open scoped Topology

/-- `b = k + a` for some `k`, when `a ≤ b`.  Local copy to avoid name/direction issues. -/
private lemma exists_eq_add_of_le'' {a b : ℕ} (h : a ≤ b) : ∃ k, b = k + a :=
  ⟨b - a, (Nat.sub_add_cancel h).symm⟩

/-- Along an orbit of the punctured basin, the quantity `φa (F^n z) - n` does not depend on the
time `n` at which the orbit lies in the petal.  This is the integrated form of the Abel equation
`φa_shift : φa (F z) = φa z + 1` carried by a `ParabolicFlowerFix`. -/
private lemma iterate_φa_sub_eq {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) {z : ℂ} {n m : ℕ}
    (hn : (F^[n]) z ∈ fl.Pa) (hm : (F^[m]) z ∈ fl.Pa) :
    fl.φa ((F^[n]) z) - (n : ℂ) = fl.φa ((F^[m]) z) - (m : ℂ) := by
  rcases le_total n m with h | h
  · obtain ⟨k, hk⟩ := exists_eq_add_of_le'' h
    subst hk
    have hs := fl.φa_shift_iterate hn k
    rw [← Function.iterate_add_apply] at hs
    rw [hs]
    push_cast
    ring
  · obtain ⟨k, hk⟩ := exists_eq_add_of_le'' h
    subst hk
    have hs := fl.φa_shift_iterate hm k
    rw [← Function.iterate_add_apply] at hs
    rw [hs]
    push_cast
    ring

theorem extFatou_abel {F g : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) {z : ℂ}
    (hz : z ∈ Work.FatouParabolic.puncturedBasin F z₀) :
    Work.FatouParabolic.extFatou fl (F z) = Work.FatouParabolic.extFatou fl z + 1 := by
  have hzF : F z ∈ Work.FatouParabolic.puncturedBasin F z₀ :=
    Work.FatouParabolic.Basin.mapsTo_puncturedBasin hfix hz
  have hspecF := Work.FatouParabolic.entryTime_spec fl (F z) hzF
  have hspec := Work.FatouParabolic.entryTime_spec fl z hz
  have hn : (F^[entryTime fl (F z) hzF + 1]) z ∈ fl.Pa := by
    have hsucc : entryTime fl (F z) hzF + 1 = (entryTime fl (F z) hzF).succ := rfl
    rw [hsucc, Function.iterate_succ_apply]
    exact hspecF
  have hkey := iterate_φa_sub_eq fl (n := entryTime fl (F z) hzF + 1)
    (m := entryTime fl z hz) hn hspec
  rw [Work.FatouParabolic.extFatou_eq fl hzF, Work.FatouParabolic.extFatou_eq fl hz]
  have harg : (F^[entryTime fl (F z) hzF]) (F z) = (F^[entryTime fl (F z) hzF + 1]) z :=
    (Function.iterate_succ_apply F (entryTime fl (F z) hzF) z).symm
  rw [harg]
  have hkey' : fl.φa ((F^[entryTime fl (F z) hzF + 1]) z) =
      fl.φa ((F^[entryTime fl z hz]) z) - (entryTime fl z hz : ℂ)
        + (entryTime fl (F z) hzF : ℂ) + 1 := by
    have h := hkey
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  rw [hkey']
  ring

end Work.FatouParabolic.Core
