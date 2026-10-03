/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reduced words in a free product of two groups, at arbitrary universe levels

`Work.OROneRel.CoprodNormalForm` and `Work.OROneRel.coprod_mk_injective_of_isReduced` set up the
normal form theory of the binary free product `M ∗ N` for two groups in the *same* universe.
The Bass--Serre tree of `ℤ/n ∗ F(γ)` needs the case of two factors in *different* universes
(`Multiplicative (ZMod n) : Type 0` on the one hand, `FreeGroup γ : Type u` on the other), so this
file repeats the two definitions at general universe levels.  The normal form theorem itself is
`Work.ORBassSerre.CoprodTree.coprod_mk_injective_of_isReduced_univ`.
-/
import Mathlib
import Submission.Work.OROneRel.coprod_mk_injective_of_isReduced

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORBassSerre.CoprodTree

/-- Two letters of a word in a free product lie in the same factor. -/
def SameFactor {M : Type u} {N : Type v} : M ⊕ N → M ⊕ N → Prop
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False

/-- A word in the generators of a free product is *reduced* if no letter is an identity and no two
adjacent letters lie in the same factor. -/
def IsReduced {M : Type u} {N : Type v} [One M] [One N] (l : List (M ⊕ N)) : Prop :=
  (∀ c ∈ l, c ≠ Sum.inl 1 ∧ c ≠ Sum.inr 1) ∧ l.IsChain fun a b => ¬ SameFactor a b

theorem isReduced_nil {M : Type u} {N : Type v} [One M] [One N] :
    IsReduced ([] : List (M ⊕ N)) :=
  ⟨by simp, List.isChain_nil⟩

theorem isReduced_sameFactor_iff {M N : Type u} (a b : M ⊕ N) :
    SameFactor a b ↔ Work.OROneRel.Coprod.SameFactor a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [SameFactor, Work.OROneRel.Coprod.SameFactor]

/-- For two factors in the *same* universe the two definitions of reducedness agree, so the
normal form theorem `Work.OROneRel.coprod_mk_injective_of_isReduced` can be reused there. -/
theorem isReduced_iff_OROneRel {M N : Type u} [Group M] [Group N] (l : List (M ⊕ N)) :
    IsReduced l ↔ Work.OROneRel.Coprod.IsReduced l := by
  have hiff : ∀ a b : M ⊕ N,
      (¬ SameFactor a b) ↔ (¬ Work.OROneRel.Coprod.SameFactor a b) :=
    fun a b => not_congr (isReduced_sameFactor_iff a b)
  constructor
  · intro h
    exact ⟨h.1, (List.IsChain.iff hiff).mp h.2⟩
  · intro h
    exact ⟨h.1, (List.IsChain.iff hiff).mpr h.2⟩

end Work.ORBassSerre.CoprodTree
