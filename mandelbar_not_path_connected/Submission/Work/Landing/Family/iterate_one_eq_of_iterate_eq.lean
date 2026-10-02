import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

theorem iterate_one_eq_of_iterate_eq {α : Type*} (f : α → α) {m n : ℕ} {x : α}
    (hm : f^[m] x = x) (hn : f^[n] x = x) (h : Nat.Coprime m n) : f x = x := by
  -- `x` is a periodic point of `f` with periods `m` and `n`, hence with period `gcd m n`.
  have hg : Function.IsPeriodicPt f (Nat.gcd m n) x := Function.IsPeriodicPt.gcd hm hn
  -- Coprimality says `gcd m n = 1`, so `1` is a period of `x`, i.e. `f x = x`.
  have h1 : Nat.gcd m n = 1 := h
  rw [h1] at hg
  exact hg

end Work.Landing.Family
