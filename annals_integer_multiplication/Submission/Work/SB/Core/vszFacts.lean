import Mathlib
import Submission.Work.Layout.Shared

/-!
# Elementary size facts for `Val`, `vsz`, `ofList`

Small glue used by the `SB` (sort / strip) route:

* `vsz (cons a b) = vsz a + vsz b + 1`, and each summand is bounded by the whole;
* `vsz (ofList l) = (l.map vsz).sum + l.length + 1`, so a list of values all of size `≤ B`
  has size `≤ (l.length + 1) * (B + 1)`;
* `ofList` is injective (list values are in bijection with the corresponding lists);
* `Forall₂ (fun a b => b = f a) xs ys ⟹ ys = xs.map f` (a `mapList` post-condition in disguise).
-/

set_option autoImplicit false

namespace Work.SB.Core

open HvdH

/-- Unfolding of `ofList` at a `cons`. -/
theorem ofList_cons (x : Val) (t : List Val) : ofList (x :: t) = Val.cons x (ofList t) := rfl

theorem vsz_cons_eq (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

theorem vsz_le_vsz_cons_left (a b : Val) : vsz a ≤ vsz (Val.cons a b) := by
  rw [vsz_cons_eq]; omega

theorem vsz_le_vsz_cons_right (a b : Val) : vsz b ≤ vsz (Val.cons a b) := by
  rw [vsz_cons_eq]; omega

theorem vsz_ofList_eq (l : List Val) : vsz (ofList l) = (l.map vsz).sum + l.length + 1 := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
      show vsz (Val.cons x (ofList t)) = (List.map vsz (x :: t)).sum + (x :: t).length + 1
      rw [vsz_cons_eq, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem vsz_ofList_le {xs : List Val} {B : ℕ} (h : ∀ x ∈ xs, vsz x ≤ B) :
    vsz (ofList xs) ≤ (xs.length + 1) * (B + 1) := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    rw [ofList_cons, vsz_cons_eq, List.length_cons]
    have key : (t.length + 1 + 1) * (B + 1) = (t.length + 1) * (B + 1) + (B + 1) := by ring
    omega

/-- `ofList` is injective. -/
theorem ofList_inj : ∀ xs ys : List Val, ofList xs = ofList ys → xs = ys
  | [], [], _ => rfl
  | [], y :: t, h => by
      simp only [ofList, List.foldr_nil, List.foldr_cons] at h
      exact absurd h.symm (Val.noConfusion)
  | x :: s, [], h => by
      simp only [ofList, List.foldr_nil, List.foldr_cons] at h
      exact absurd h (Val.noConfusion)
  | x :: s, y :: t, h => by
      simp only [ofList, List.foldr_cons, Val.cons.injEq] at h
      rw [ofList_inj s t h.2, h.1]

/-- A `Forall₂` whose relation is "the second component is `f` applied to the first" forces the
second list to be the image of the first. -/
theorem forall₂_eq_map {f : Val → Val} {xs ys : List Val}
    (h : List.Forall₂ (fun a b => b = f a) xs ys) : ys = xs.map f := by
  induction h with
  | nil => rfl
  | cons hb _ ih => simp [ih, hb]

end Work.SB.Core
