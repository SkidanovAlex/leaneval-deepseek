/-
# [JZLA20, Proposition 5.1] with the third clause of (2)

This file assembles the two halves of the paper-faithful form of [JZLA20, Proposition 5.1]:

* `Prop51.prop51` (the induction on the `H`-complexity) gives, for every `b ∈ D_{H,P}` of
  `H`-complexity at most `Tree_H(a)`, the conclusion `Prop51Concl d b` — the series
  `b = laurentEmbed f` with its coefficient bounds;
* `Prop51.prop51_mono` (the case analysis on the decomposition of a minimal realiser of `b`) gives
  the third clause of [JZLA20, Proposition 5.1(2)]: if `b` is a single monomial `b_k t^k` then every
  minimal realiser of `b` lies in `Rat(E^×N)·t^k`.

Together they give `Prop51ConclP d b`, the full statement of [JZLA20, Proposition 5.1].
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Prop51.prop51
import Submission.Work.ORHughesFree.Prop51.mono

set_option autoImplicit false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- **[JZLA20, Proposition 5.1]**, in the paper-faithful form `Prop51ConclP` (i.e. with the third
clause of (2)), by well-founded induction on the `H`-complexity `treeH a` along the DHS04 tree
order. -/
theorem prop51P (d : Prop51Data Γ P DN) (a : P) :
    Prop51Inv d a →
      ∀ (b : P) (hb : b ∈ d.DH), Tree.le (d.treeH b) (d.treeH a) → Prop51ConclP d b := by
  suffices h : ∀ x : Tree, ∀ a : P, d.treeH a = x →
      (Prop51Inv d a → ∀ (b : P) (hb : b ∈ d.DH), Tree.le (d.treeH b) (d.treeH a) →
        Prop51ConclP d b) by
    exact h (d.treeH a) a rfl
  intro x
  induction x using Tree.lt_wf.induction with
  | h x ih =>
    intro a ha hinv b hb hle
    have hsmall : ∀ b' ∈ d.DH, Tree.lt (d.treeH b') (d.treeH a) → Prop51ConclP d b' := by
      intro b' hb' hlt
      have hltx : Tree.lt (d.treeH b') x := by rw [← ha]; exact hlt
      have hInv' : Prop51Inv d b' := prop51Inv_mono hinv (Tree.le_of_lt hlt)
      exact (ih (d.treeH b') hltx b' rfl) hInv' b' hb' (Tree.le_refl (d.treeH b'))
    obtain ⟨f, hf, hbd, hsing⟩ := prop51 d a hinv b hb hle
    have hboundU : ∀ k : ℤ, Tree.le (d.treeH (d.coeffToP (f.1 k))) (d.treeH b) := by
      intro k
      by_cases hk0 : f.1 k = 0
      · rw [hk0]
        have hc : d.coeffToP (0 : ↥DN) = 0 := rfl
        rw [hc, treeH_zero d]
        exact Tree.le_zero _
      · exact hbd k hk0
    exact ⟨f, hf, hboundU, hsing,
      fun k hk => prop51_mono d hf hb hle hboundU hsing hsmall hk⟩

end Work.ORHughesFree.Prop51
