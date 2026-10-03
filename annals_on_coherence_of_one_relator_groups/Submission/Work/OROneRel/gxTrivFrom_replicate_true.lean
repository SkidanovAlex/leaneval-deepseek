import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs

/-!
# The triviality predicate on a chain of `x₀`-edges

`Work.OROneRel.gxTrivFrom c D v L` says that every edge traversed by the decorated walk
`decor c v L` has trivial loop class under the gauge `D`.  Here `L` is the list
`[x₀, x₀, …, x₀]` of `n` positive traversals of a single generator `x₀`, so the decorated walk is
the chain

  `(x₀, v), (x₀, v + c x₀), …, (x₀, v + (n-1) · c x₀)`

of `x₀`-edges starting at the level `v`.  Its `k`-th edge has loop class

  `D (v + k · c x₀) · x₀ · (D (v + (k+1) · c x₀))⁻¹`

(`coverClassAt`, `gaugeMap_of`), which is trivial exactly when the hypothesized chain equation

  `D (v + (m+1) · c x₀) = D (v + m · c x₀) · x₀`

holds at `m = k`.  That is the content of the lemma: the hypothesis, stated for all `m < n`, makes
every one of the `n` edges trivial.
-/

namespace Work.OROneRel

theorem gxTrivFrom_replicate_true_aux {α : Type*} [DecidableEq α] (c : α → ℤ)
    (D : ℤ → FreeGroup α) (x₀ : α) :
    ∀ (n : ℕ) (v : ℤ),
      (∀ m : ℕ, m < n →
        D (v + ((m : ℤ) + 1) * c x₀) = D (v + (m : ℤ) * c x₀) * FreeGroup.of x₀) →
      gxTrivFrom c D v (List.replicate n (x₀, true)) := by
  intro n
  induction n with
  | zero =>
    intro v _
    simp [gxTrivFrom, decor]
  | succ n ih =>
    intro v h
    rw [List.replicate_succ]
    intro p hp
    -- the decorated walk of a cons, with the head letter `(x₀, true)` read at level `v`
    rw [show decor c v ((x₀, true) :: List.replicate n (x₀, true)) =
          ((x₀, v), true) :: decor c (v + c x₀) (List.replicate n (x₀, true)) from rfl] at hp
    rw [List.mem_cons] at hp
    rcases hp with hp | hp
    · -- the head edge `(x₀, v)`, trivial by the hypothesis at `m = 0`
      rw [hp]
      show coverClassAt D c (x₀, v) = 1
      rw [coverClassAt, gaugeMap_of]
      have h0 := h 0 (Nat.zero_lt_succ n)
      simp only [Nat.cast_zero, zero_add, one_mul, zero_mul, add_zero] at h0
      rw [h0, mul_inv_cancel]
    · -- the tail: recurse at the level `v + c x₀`, the hypothesis at `m + 1`
      refine ih (v + c x₀) ?_ p hp
      intro m hm
      have hh := h (m + 1) (Nat.succ_lt_succ hm)
      have e1 : (v + c x₀) + ((m : ℤ) + 1) * c x₀ = v + (((m + 1 : ℕ) : ℤ) + 1) * c x₀ := by
        push_cast; ring
      have e2 : (v + c x₀) + (m : ℤ) * c x₀ = v + (((m + 1 : ℕ) : ℤ)) * c x₀ := by
        push_cast; ring
      rw [e1, e2]
      exact hh

theorem gxTrivFrom_replicate_true {α : Type*} [DecidableEq α] (c : α → ℤ) (D : ℤ → FreeGroup α)
    (x₀ : α) (v : ℤ) (n : ℕ)
    (h : ∀ m : ℕ, m < n →
      D (v + ((m : ℤ) + 1) * c x₀) = D (v + (m : ℤ) * c x₀) * FreeGroup.of x₀) :
    Work.OROneRel.gxTrivFrom c D v (List.replicate n (x₀, true)) :=
  gxTrivFrom_replicate_true_aux c D x₀ n v h

end Work.OROneRel
