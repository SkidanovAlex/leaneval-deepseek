import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Walk

open Quiver

/-- A two-valued function that is constant along every arrow is constant along every path. -/
private lemma bool_const_of_path {V : Type*} [Quiver V] {d : V → Bool}
    (hd : ∀ e : Quiver.Total V, d e.left = d e.right) {a b : V} (p : Quiver.Path a b) :
    d b = d a := by
  induction p with
  | nil => rfl
  | cons p e ih => exact (hd (Quiver.Total.mk _ _ e)).symm.trans ih

/-- On `Bool`, if `a ≠ b` then `b` is the complement of `a`. -/
private lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

theorem bipartition_eq_of_agree {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) {c c' : V → Bool}
    (hc : ∀ e : Quiver.Total V, c e.left ≠ c e.right)
    (hc' : ∀ e : Quiver.Total V, c' e.left ≠ c' e.right) {v : V} (hv : c v = c' v) :
    c = c' := by
  -- The agreement indicator `d w = (c w == c' w)` is constant along every arrow, hence along
  -- every path, hence constant on the connected graph `V`.
  let d : V → Bool := fun w => c w == c' w
  have hd : ∀ e : Quiver.Total V, d e.left = d e.right := by
    intro e
    show (c e.left == c' e.left) = (c e.right == c' e.right)
    have h1 : c e.right = !(c e.left) := bool_eq_not_of_ne (hc e)
    have h2 : c' e.right = !(c' e.left) := bool_eq_not_of_ne (hc' e)
    rw [h1, h2]
    cases c e.left <;> cases c' e.left <;> rfl
  funext w
  obtain ⟨p⟩ := hT.1 v w
  have hp : d w = d v := bool_const_of_path hd p
  have hdv : d v = true := by
    show (c v == c' v) = true
    rw [hv]; exact beq_self_eq_true _
  exact beq_iff_eq.mp (show (c w == c' w) = true from hp.trans hdv)

end Work.ORBassSerre.Tree.Walk
