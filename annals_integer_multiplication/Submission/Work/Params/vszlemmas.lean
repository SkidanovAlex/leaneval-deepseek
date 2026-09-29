import Mathlib
import Submission.Work.Params.basic
import Submission.Work.Params.defs
import Submission.Work.IntLib.encodeNatBridge

/-!
# Size bounds for `vsz`

Two elementary size bounds used by the `Params` area's cost bookkeeping:

* an integer value `Val.int m` has size at most `m.size + 2` (in fact exactly `isz m = m.size + 2`);
* a `cons`-list of values of size `≤ B` has size at most `(length + 1) * (B + 1)`.

The second bound is exactly what is needed to turn the cost `K * (vsz (ofList xs) + 1)` of a
program that walks a list into `K * (xs.length + 1) * (B + 1)`.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- Unfolding of `ofList` at a `cons`. -/
theorem ofList_cons (x : Val) (t : List Val) : ofList (x :: t) = Val.cons x (ofList t) := rfl

/-- The size of a `cons` value. -/
theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

/-- `vsz (ofList xs)` is bounded by the number of elements times the maximal element size:
`vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 ≤ (xs.length + 1) * (B + 1)`. -/
theorem vsz_ofList_le {xs : List Val} {B : ℕ} (h : ∀ x ∈ xs, vsz x ≤ B) :
    vsz (ofList xs) ≤ (xs.length + 1) * (B + 1) := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    rw [ofList_cons, vsz_cons, List.length_cons]
    have key : (t.length + 1 + 1) * (B + 1) = (t.length + 1) * (B + 1) + (B + 1) := by ring
    omega

theorem vszlemmas :
    (∀ m : ℕ, HvdH.vsz (HvdH.Val.int (m : ℤ)) ≤ m.size + 2) ∧
    (∀ (xs : List HvdH.Val) (B : ℕ), (∀ x ∈ xs, HvdH.vsz x ≤ B) →
      HvdH.vsz (HvdH.ofList xs) ≤ (xs.length + 1) * (B + 1)) := by
  refine ⟨?_, ?_⟩
  · intro m
    show (Val.int (m : ℤ)).enc.length ≤ m.size + 2
    rw [Work.IntLib.vsz_int, isz]
    simp
  · intro xs B h
    exact vsz_ofList_le h

end Work.Params
