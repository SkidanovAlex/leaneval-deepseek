import Mathlib
import Submission.Work.HP.NA.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.NA

set_option linter.style.haveILetI false in
theorem not_isUnit_eq_p_mul {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (x : ZMod (p ^ r)) :
    ¬ IsUnit x ↔ ∃ y : ZMod (p ^ r), x = (p : ZMod (p ^ r)) * y := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hd : 0 < r := hr
  have hunit : IsUnit x ↔ ¬ p ∣ x.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    exact ZMod.isUnit_natCast_iff_not_dvd_pow hp hd
  constructor
  · intro hx
    have hdvd : p ∣ x.val := by
      by_contra hc
      exact hx (hunit.mpr hc)
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨(k : ZMod (p ^ r)), by
      rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul]⟩
  · rintro ⟨y, hy⟩ hxu
    rw [hy] at hxu
    exact ZMod.prime_natCast_not_isUnit_pow hp hd (IsUnit.mul_iff.mp hxu).1

end Work.HP.NA
