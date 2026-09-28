import Mathlib
import Submission.Work.HP.NA.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.NA

open Finset

theorem exists_Rset_of_FlocSet (d n p r : ℕ) (a : Work.HP.Mon d n → ZMod (p ^ r))
    (ha : Work.HP.NA.FlocSet d n p r a) :
    ∃ e, e ≤ r ∧ Work.HP.NA.Rset d n p r e a := by
  classical
  obtain ⟨hprim, x, hxprim, hfx⟩ := ha
  -- `e` is the largest `k ≤ r` such that every gradient component is divisible by `p^k`.
  let e : ℕ := Nat.findGreatest (fun k => ∀ j, vpDvd p r k (gradv d n a x j)) r
  have he_le : e ≤ r := Nat.findGreatest_le (P := fun k => ∀ j, vpDvd p r k (gradv d n a x j)) r
  have he_spec : ∀ j, vpDvd p r e (gradv d n a x j) :=
    Nat.findGreatest_spec (P := fun k => ∀ j, vpDvd p r k (gradv d n a x j))
      (m := 0) (n := r) (Nat.zero_le r)
      (fun j => ⟨gradv d n a x j, by simp⟩)
  refine ⟨e, he_le, hprim, x, hxprim, hfx, he_spec, ?_⟩
  intro her hall
  have hle : e + 1 ≤ Nat.findGreatest (fun k => ∀ j, vpDvd p r k (gradv d n a x j)) r :=
    Nat.le_findGreatest (P := fun k => ∀ j, vpDvd p r k (gradv d n a x j))
      (m := e + 1) (n := r) (by omega) hall
  have heq : Nat.findGreatest (fun k => ∀ j, vpDvd p r k (gradv d n a x j)) r = e := rfl
  omega

end Work.HP.NA
