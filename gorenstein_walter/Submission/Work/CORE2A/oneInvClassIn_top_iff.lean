import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# CORE2A: one involution class in `K` vs. in `⊤ : Subgroup ↥K`

`Work.GW2.OneInvClassIn K` says that any two involutions of `K` are conjugate by an element
of `K`.  The present lemma records that this predicate is insensitive to viewing the elements
of `K` as a group in its own right: `K` has one class of involutions iff the whole group
`↥K` (that is, `⊤ : Subgroup ↥K`) does.

The proof is a pure bookkeeping exercise in the subtype coercions: an involution of `↥K` is an
element of `K` of order `2` (`Subgroup.orderOf_coe`), and conjugation in `↥K` is conjugation in
`G` transported along `Subgroup.val` (`Subgroup.val_mul`, `Subtype.ext`).
-/

namespace Work.CORE2A

open Subgroup

theorem oneInvClassIn_top_iff {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.OneInvClassIn (⊤ : Subgroup ↥K) ↔ Work.GW2.OneInvClassIn K := by
  constructor
  · -- `↥K` has one class of involutions `⇒` `K` does: replace every `a : K` by `⟨a, ·⟩ : ↥K`.
    intro h x hx y hy
    obtain ⟨hxK, hx2⟩ := hx
    obtain ⟨hyK, hy2⟩ := hy
    have hx' : (⟨x, hxK⟩ : ↥K) ∈ Work.GW2.involutionSet (⊤ : Subgroup ↥K) := by
      refine ⟨trivial, ?_⟩
      simpa using hx2
    have hy' : (⟨y, hyK⟩ : ↥K) ∈ Work.GW2.involutionSet (⊤ : Subgroup ↥K) := by
      refine ⟨trivial, ?_⟩
      simpa using hy2
    obtain ⟨g, -, hg⟩ := h (⟨x, hxK⟩ : ↥K) hx' (⟨y, hyK⟩ : ↥K) hy'
    exact ⟨(g : G), g.2, by
      have := congrArg (Subtype.val) hg
      simpa using this⟩
  · -- `K` has one class of involutions `⇒` `↥K` does: coerce the conjugator back into `↥K`.
    intro h x hx y hy
    obtain ⟨-, hx2⟩ := hx
    obtain ⟨-, hy2⟩ := hy
    obtain ⟨g, hgK, hg⟩ :=
      h (x : G) ⟨x.2, by simpa using hx2⟩ (y : G) ⟨y.2, by simpa using hy2⟩
    refine ⟨⟨g, hgK⟩, trivial, ?_⟩
    apply Subtype.ext
    simpa using hg

end Work.CORE2A
