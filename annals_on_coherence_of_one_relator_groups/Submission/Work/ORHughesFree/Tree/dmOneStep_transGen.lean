/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `dmLT` is the transitive closure of its one-step relation

The Dershowitz–Manna multiset ordering

`dmLT r M N`  iff  `M = X + Y`, `N = X + Z`, `Z ≠ 0` and every element of `Y` is `r`-dominated by
some element of `Z`,

is classically presented as the *transitive closure* of its one-step version

`dmOneStep r M N`  iff  `M = X + Y`, `N = X + {a}` and every element of `Y` is `r`-dominated by
`a`.

This file proves the inclusion that uses no property of `r` at all: every `dmLT`-comparison is
realised by a finite chain of `dmOneStep`-steps — one step for every element of `Z`.  Concretely,
writing `Z = b ::ₘ Z₀`, the elements of `Y` that are dominated by `b` (and only those) are
replaced by the single element `b`, and the induction hypothesis (applied with the "constant"
multiset enlarged by `{b}`) handles the elements dominated by the remaining elements `Z₀` of `Z`.
When `Z₀ = 0` the comparison is itself a single step, so the analysis is exhaustive.

This is the direction needed to reduce the well-foundedness of `dmLT` (and hence of the tree order
`lt`) to the well-foundedness of the one-step relation; see also
`Work.ORHughesFree.Tree.acc_dmOneStep_of_acc`.

The argument is purely combinatorial, so it is carried out for an arbitrary type `α` and an
arbitrary relation `r`: the type of elements never enters.  The general one-step relation
`dmOneStepGen` is definitionally equal to `dmOneStep` at `α = Tree`, `r = lt`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs

namespace Work.ORHughesFree.Tree

/-- The one-step Dershowitz–Manna relation on multisets over an arbitrary type: `N` is obtained
from `M` by replacing all elements of a sub-multiset `Y` by a single element `a` that dominates
them.  This is `dmOneStep` with the type of the elements generalised. -/
def dmOneStepGen {α : Type*} (r : α → α → Prop) (M N : Multiset α) : Prop :=
  ∃ X Y a, M = X + Y ∧ N = X + {a} ∧ ∀ y ∈ Y, r y a

/-- The general one-step relation is the one of `order_defs`. -/
theorem dmOneStepGen_iff_dmOneStep (M N : Multiset Tree) :
    dmOneStepGen lt M N ↔ dmOneStep lt M N := Iff.rfl

/-- **Peeling off one element of `Z`.**  If `Z ≠ 0` and every element of `Y` is `r`-dominated by
some element of `Z`, then `X + Y` reaches `X + Z` by a finite chain of `dmOneStep`-steps: the
elements of `Y` that are dominated by a fixed `b ∈ Z` — and only those — are replaced by `b` in one
step, and the induction hypothesis deals with the rest with the "constant" multiset enlarged by
`{b}`. -/
theorem dmLT_transGen_aux {α : Type*} (r : α → α → Prop) (Z : Multiset α) (hZ : Z ≠ 0)
    (X Y : Multiset α) (h : ∀ a ∈ Y, ∃ b ∈ Z, r a b) :
    Relation.TransGen (dmOneStepGen r) (X + Y) (X + Z) := by
  revert hZ X Y
  induction Z using Multiset.induction_on with
  | empty => intro h; exact absurd rfl h
  | cons b Z₀ ih =>
    intro hZ X Y h
    classical
    by_cases h0 : Z₀ = 0
    · -- `Z = {b}`: a single step replaces all of `Y` by `b`
      subst h0
      have hrel : ∀ y ∈ Y, r y b := by
        intro y hy
        obtain ⟨b', hb'mem, hb'⟩ := h y hy
        rw [Multiset.mem_cons] at hb'mem
        rcases hb'mem with rfl | hb'0
        · exact hb'
        · exact absurd hb'0 (by simp)
      refine Relation.TransGen.single ⟨X, Y, b, rfl, ?_, hrel⟩
      rw [Multiset.cons_zero]
    · -- `Z = b ::ₘ Z₀` with `Z₀ ≠ 0`: split `Y` according to whether its elements are dominated
      -- by something in `Z₀`
      set Y₂ : Multiset α := Y.filter (fun y => ∃ b' ∈ Z₀, r y b') with hY₂
      set Y₁ : Multiset α := Y.filter (fun y => ¬ ∃ b' ∈ Z₀, r y b') with hY₁
      have hY : Y = Y₂ + Y₁ := by
        have hf := Multiset.filter_add_not (fun y => ∃ b' ∈ Z₀, r y b') Y
        rw [← hY₂, ← hY₁] at hf
        rw [← hf]
      -- first step: replace `Y₁` (the elements dominated by `b` and nothing in `Z₀`) by `b`
      have stepA : dmOneStepGen r (X + Y) ((X + Y₂) + {b}) := by
        refine ⟨X + Y₂, Y₁, b, ?_, rfl, ?_⟩
        · rw [hY]; ac_rfl
        · intro y hy
          rw [hY₁, Multiset.mem_filter] at hy
          obtain ⟨hyY, hyne⟩ := hy
          obtain ⟨b', hb'mem, hb'⟩ := h y hyY
          rw [Multiset.mem_cons] at hb'mem
          rcases hb'mem with rfl | hb'0
          · exact hb'
          · exact absurd ⟨b', hb'0, hb'⟩ hyne
      -- the elements of `Y₂` are dominated by elements of `Z₀`; apply the induction hypothesis
      have hY₂cond : ∀ a ∈ Y₂, ∃ b' ∈ Z₀, r a b' := by
        intro a ha
        rw [hY₂, Multiset.mem_filter] at ha
        exact ha.2
      have ihapp := ih h0 (X + {b}) Y₂ hY₂cond
      have ihapp' : Relation.TransGen (dmOneStepGen r) ((X + Y₂) + {b}) (X + (b ::ₘ Z₀)) := by
        rw [show (X + Y₂) + {b} = (X + {b}) + Y₂ from by ac_rfl,
            show X + (b ::ₘ Z₀) = (X + {b}) + Z₀ from by rw [← Multiset.singleton_add]; ac_rfl]
        exact ihapp
      exact (Relation.TransGen.single stepA).trans ihapp'

theorem dmOneStep_transGen {M N : Multiset Tree} (h : dmLT lt M N) :
    Relation.TransGen (dmOneStep lt) M N := by
  obtain ⟨X, Y, Z, hZ, rfl, rfl, hrel⟩ := h
  exact dmLT_transGen_aux lt Z hZ X Y hrel

end Work.ORHughesFree.Tree
