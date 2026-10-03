import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Prop51.prop51_case
import Submission.Work.ORHughesFree.Tree.Log

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- **The induction hypothesis `Prop51Inv` is monotone in the complexity.**  If every non-zero
`c ∈ D_{H,P}` with `Tree_H(c) < Tree_H(a)` is invertible in `D_{H,P}`, then the same holds with `a`
replaced by any `b` with `Tree_H(b) ≤ Tree_H(a)`: for `Tree_H(c) ≤ Tree_H(b)` and
`Tree_H(c) ≠ Tree_H(b)` we get `Tree_H(c) ≤ Tree_H(a)` and `Tree_H(c) ≠ Tree_H(a)`. -/
theorem prop51Inv_mono {d : Prop51Data Γ P DN} {a b : P}
    (h : Prop51Inv d a) (hba : Tree.le (d.treeH b) (d.treeH a)) : Prop51Inv d b := by
  intro c hc hc0 hle hne
  refine h c hc hc0 (Tree.le_trans hle hba) ?_
  intro heq
  exact hne (Tree.le_antisymm hle (heq.symm ▸ hba))

/-- **[JZLA20, Proposition 5.1]** — the assembly.  We prove `Prop51 d a` for all `a` by well-founded
induction on the `H`-complexity `Tree_H(a)` along the DHS04 tree order `Tree.lt` (well-founded by
`Tree.lt_wf`).

Let `T := Tree_H(a)`.  For `b ∈ D_{H,P}` with `Tree_H(b) ≤ Tree_H(a)` we must produce the
conclusion `Prop51Concl d b`, and `prop51_case` does it provided we already know the conclusion for
every `b' ∈ D_{H,P}` with `Tree_H(b') < Tree_H(a)`: such a `b'` has complexity `Tree_H(b')` strictly
below the induction parameter `T`, so the induction hypothesis gives `Prop51 d b'` there; and
`Prop51Inv d b'` — the hypothesis of `Prop51 d b'` — follows from the given `Prop51Inv d a` by
monotonicity (`prop51Inv_mono`), since `Tree_H(b') ≤ Tree_H(a)`.  Applying `Prop51 d b'` to
`b'' = b'` turns it into `Prop51Concl d b'`.  It remains to feed `prop51_case` a realisation
`β : Rat(Γ)` of `b` (`Φ β = b`, `Tree β = Tree_H(b)`), which is `exists_realizing`. -/
theorem prop51 {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (a : P) : Work.ORHughesFree.Prop51 d a := by
  -- Generalise over the value of the complexity, so as to induct on it.
  suffices h : ∀ x : Tree, ∀ a : P, d.treeH a = x → Prop51 d a by
    exact h (d.treeH a) a rfl
  intro x
  induction x using Tree.lt_wf.induction with
  | h x ih =>
    intro a ha hinv b hb hle
    -- The strict induction hypothesis required by `prop51_case`.
    have hsmall : ∀ b' ∈ d.DH, Tree.lt (d.treeH b') (d.treeH a) → Prop51Concl d b' := by
      intro b' hb' hlt
      have hltx : Tree.lt (d.treeH b') x := by rw [← ha]; exact hlt
      have hInv' : Prop51Inv d b' := prop51Inv_mono hinv (Tree.le_of_lt hlt)
      exact (ih (d.treeH b') hltx b' rfl) hInv' b' hb' (Tree.le_refl (d.treeH b'))
    obtain ⟨β, hβ, htree⟩ := d.exists_realizing hb
    exact prop51_case (a := a) (b := b) d hsmall hinv hb hle β hβ htree

end Work.ORHughesFree.Prop51
