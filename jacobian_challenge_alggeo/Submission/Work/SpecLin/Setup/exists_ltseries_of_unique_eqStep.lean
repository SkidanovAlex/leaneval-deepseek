import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Setup

open RelSeries

/-- **Strict case.**  If `f` strictly increases at every step of a strict chain `l` in `α`, then
`f ∘ l` is a strict chain in `β` of the same length. -/
theorem exists_ltseries_of_strict {α β : Type*} [Preorder α] [LinearOrder β] (f : α → β)
    (hf : Monotone f) (l : LTSeries α)
    (h : ∀ i : Fin l.length, f (l i.castSucc) ≠ f (l i.succ)) :
    ∃ m : LTSeries β, m.last = f l.last ∧ l.length ≤ m.length := by
  refine ⟨LTSeries.mk l.length (fun i => f (l i)) ?_, rfl, le_rfl⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  exact lt_of_le_of_ne (hf (l.step i).le) (h i)

section Aux

variable {α β : Type*} [Preorder α] [LinearOrder β]

/-- The value of `p.snoc a hx` at the position `(Fin.castSucc i).castSucc`, i.e. the value of `p` at
`i.castSucc`. -/
lemma snoc_apply_castSucc (p : LTSeries α) (a : α) (hx : p.last < a) (i : Fin p.length) :
    (p.snoc a hx) ((Fin.castSucc i).castSucc) = p i.castSucc :=
  RelSeries.snoc_castSucc p a hx (Fin.castSucc i)

/-- The value of `p.snoc a hx` at the position `(Fin.castSucc i).succ`, i.e. the value of `p` at
`i.succ`. -/
lemma snoc_apply_succ (p : LTSeries α) (a : α) (hx : p.last < a) (i : Fin p.length) :
    (p.snoc a hx) ((Fin.castSucc i).succ) = p i.succ := by
  rw [Fin.succ_castSucc]
  exact RelSeries.snoc_castSucc p a hx i.succ

/-- The value of `p.snoc a hx` at the position `(Fin.last p.length).castSucc` is `p.last`. -/
lemma snoc_apply_last_castSucc (p : LTSeries α) (a : α) (hx : p.last < a) :
    (p.snoc a hx) ((Fin.last p.length).castSucc) = p.last := by
  rw [show (Fin.last p.length).castSucc =
      (Fin.castSucc (Fin.last p.length) : Fin (p.length + 2)) from rfl]
  exact RelSeries.snoc_castSucc p a hx (Fin.last p.length)

/-- The value of `p.snoc a hx` at the last position is `a`. -/
lemma snoc_apply_last_succ (p : LTSeries α) (a : α) (hx : p.last < a) :
    (p.snoc a hx) ((Fin.last p.length).succ) = a := by
  rw [Fin.succ_last]
  exact RelSeries.last_snoc p a hx

end Aux

/-- **Compression of a chain along a monotone map.**

Let `f : α → β` be monotone with `β` linearly ordered and let `l` be a strictly increasing chain in
`α`.  If there is at most one index `i` at which `f` does not strictly increase (i.e. all "equal
steps" `f (l i) = f (l (i+1))` occur at one and the same index), then `f` maps `l` to a weakly
increasing sequence with at most one repetition, which compresses to a *strictly* increasing chain
in `β` of length at least `l.length - 1`, ending at `f l.last`.

Proof plan: first establish the special case in which `f` strictly increases along `l`
(`∀ i, f (l i.castSucc) ≠ f (l i.succ)`); there `m` can be taken to be `l.map` of the strict
monotonicity witness, giving `l.length ≤ m.length`.  The general case is a strong induction on
`l.length`: write `l` as its prefix `l.take (l.length - 1)` (whose last element is
`l (l.length - 1)`) followed by the last step.  Either the last step is strict -- and one may
append `f l.last` to the chain obtained from the prefix by the induction hypothesis
(`RelSeries.snoc`) -- or the last step is the unique equal step, in which case the prefix has no
equal step at all, the special case applies to it, and it already ends at
`f (l (l.length - 1)) = f l.last`. -/
theorem exists_ltseries_of_unique_eqStep {α β : Type*} [Preorder α] [LinearOrder β] (f : α → β)
    (hf : Monotone f) (l : LTSeries α)
    (h : ∀ i j : Fin l.length, f (l i.castSucc) = f (l i.succ) → f (l j.castSucc) = f (l j.succ) → i = j) :
    ∃ m : LTSeries β, m.last = f l.last ∧ l.length ≤ m.length + 1 := by
  revert h
  induction l using RelSeries.inductionOn' with
  | singleton x =>
      intro _
      exact ⟨RelSeries.singleton _ (f x), by simp, by simp⟩
  | snoc p a hx hp =>
      intro H
      -- restate `H` with the step index type `Fin (p.length + 1)` of the appended series
      have H' : ∀ i j : Fin (p.length + 1),
          f ((p.snoc a hx) i.castSucc) = f ((p.snoc a hx) i.succ) →
          f ((p.snoc a hx) j.castSucc) = f ((p.snoc a hx) j.succ) → i = j := H
      by_cases heq : f p.last = f a
      · -- the last step is the (unique) equal step
        have Hp : ∀ i : Fin p.length, f (p i.castSucc) ≠ f (p i.succ) := by
          intro i hi
          have hstep : f ((p.snoc a hx) (Fin.castSucc i).castSucc) =
              f ((p.snoc a hx) (Fin.castSucc i).succ) := by
            rw [snoc_apply_castSucc, snoc_apply_succ]; exact hi
          have hlast : f ((p.snoc a hx) (Fin.last p.length).castSucc) =
              f ((p.snoc a hx) (Fin.last p.length).succ) := by
            rw [snoc_apply_last_castSucc, snoc_apply_last_succ]; exact heq
          have key := H' (Fin.last p.length) (Fin.castSucc i) hlast hstep
          have hv := congrArg Fin.val key
          simp only [Fin.val_last, Fin.val_castSucc] at hv
          omega
        obtain ⟨m', hm'last, hm'len⟩ := exists_ltseries_of_strict f hf p Hp
        refine ⟨m', ?_, ?_⟩
        · rw [hm'last, RelSeries.last_snoc]; exact heq
        · rw [RelSeries.snoc_length]; omega
      · -- the last step is strict
        have Hp : ∀ i j : Fin p.length, f (p i.castSucc) = f (p i.succ) →
            f (p j.castSucc) = f (p j.succ) → i = j := by
          intro i j hi hj
          have hi' : f ((p.snoc a hx) (Fin.castSucc i).castSucc) =
              f ((p.snoc a hx) (Fin.castSucc i).succ) := by
            rw [snoc_apply_castSucc, snoc_apply_succ]; exact hi
          have hj' : f ((p.snoc a hx) (Fin.castSucc j).castSucc) =
              f ((p.snoc a hx) (Fin.castSucc j).succ) := by
            rw [snoc_apply_castSucc, snoc_apply_succ]; exact hj
          have key := H' (Fin.castSucc i) (Fin.castSucc j) hi' hj'
          exact Fin.castSucc_inj.mp key
        obtain ⟨m', hm'last, hm'len⟩ := hp Hp
        have hrel : m'.last < f a := by
          rw [hm'last]
          exact lt_of_le_of_ne (hf hx.le) heq
        refine ⟨m'.snoc (f a) hrel, ?_, ?_⟩
        · rw [RelSeries.last_snoc, RelSeries.last_snoc]
        · rw [RelSeries.snoc_length, RelSeries.snoc_length]; omega

end Work.SpecLin.Setup
