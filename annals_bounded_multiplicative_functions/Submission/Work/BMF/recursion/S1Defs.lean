import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.card_pair_fibre_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for the first Hölder step `S₁ ≤ |P| Σ_p I1(p)` of the
Vinogradov–Linnik recursion

This module collects the (few) definitions and unfolding lemmas needed to *state* the pieces of

* `Work.BMF.recursion.S1_le_I1` (Wooley, Michigan Math. J. **40** (1993), 175–180, §2, case (b)).

Everything is phrased in terms of the moment map
`Submission.Vinogradov.powerSums k : Tup S Q → (Fin (k+1) → ℤ)`; the fibre-square identity
`card_pair_fiber_sq` below is the elementary counting step used twice in the proof (once for
`S1pair`, once for each `I1 p`).
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open scoped BigOperators

noncomputable section

/-- The `S`-tuples in `[1,Q]` whose head (the first `k` coordinates) is pairwise distinct
modulo `p`.  This is the set called `A_p` in the proof of `S1_le_I1`; it coincides with
`i1Set S k Q p hkS` of `I1I2Defs`.

Defined with an internal `classical`, so that statements mentioning `hdpSet` do not have to
carry a `DecidablePred` instance argument. -/
def hdpSet (S k Q p : ℕ) (hkS : k ≤ S) : Finset (Tup S Q) := by
  classical
  exact Finset.univ.filter (fun x => HDp p k hkS x)

/-- Membership in `hdpSet`. -/
@[simp] lemma mem_hdpSet {S k Q p : ℕ} {hkS : k ≤ S} {x : Tup S Q} :
    x ∈ hdpSet S k Q p hkS ↔ HDp p k hkS x := by
  simp [hdpSet]

/-- Membership in `hdSet`. -/
@[simp] lemma mem_hdSet {S k Q : ℕ} {hkS : k ≤ S} {x : Tup S Q} :
    x ∈ hdSet S k Q hkS ↔ HD hkS x := by
  simp [hdSet]

/-- `HD` for an `S`-tuple is the same condition as `HD` for its head `k`-tuple. -/
lemma hd_head {k S Q : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    HD hkS x ↔ HD (le_refl k) (fun i => x (hIdx hkS i)) := by
  simp only [HD]
  exact Iff.rfl

/-- `HDp` for an `S`-tuple is the same condition as `HDp` for its head `k`-tuple. -/
lemma hdp_head {k S Q p : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    HDp p k hkS x ↔ HDp p k (le_refl k) (fun i => x (hIdx hkS i)) := by
  simp only [HDp, hIdx]

/-- **Fibre-square decomposition, real form.**  For a map `f : α → β` between finite types and a
subset `A ⊆ α`, the number of pairs in `A × A` on which `f` takes equal values equals
`Σ_v #(A ∩ f⁻¹v)²`, the sum running over the values attained by `f`.

Immediate from `card_pair_fibre_sum` (with `A = B`). -/
theorem card_pair_fiber_sq {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (A : Finset α) :
    (((Finset.univ : Finset (α × α)).filter
        (fun p => f p.1 = f p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A)).card : ℝ)
      = ∑ v ∈ Finset.univ.image f, ((A.filter (fun x => f x = v)).card : ℝ) ^ 2 := by
  rw [card_pair_fibre_sum f A A]
  exact Finset.sum_congr rfl (fun v _ => by rw [pow_two])

end

end Work.BMF.recursion
