/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Word-level blocks of the Nielsen substitution `t ↦ t ^ p`

For a reduced word `L` and the endomorphism `powSubst t p : F(α) →* F(α)` sending the generator
`t` to `t ^ p` and fixing every other generator, the reduced word of `powSubst t p (mk L)` is
obtained by replacing every letter `c = (a, b)` of `L` by a *block*:

* if `a ≠ t`, by the single letter `(a, b)`;
* if `a = t`, by `|p|` copies of the letter `t` with sign `b` if `p > 0` and sign `!b` if `p < 0`.

This file contains the definitions of these blocks together with their elementary properties.
The facts about the concatenation of the blocks are proved elsewhere; see
`Submission.Work.OROneRel.isCyclicallyReduced_powSubst`.
-/
import Mathlib

namespace Work.OROneRel

universe u

variable {α : Type u}

section Blocks

variable [DecidableEq α]

/-- The length of the block replacing a single letter `c = (a, b)` of a reduced word under the
substitution `t ↦ t ^ p`: `|p|` if `a = t`, and `1` otherwise. -/
def powSubstBlockLen (t : α) (p : ℤ) (c : α × Bool) : ℕ :=
  if c.1 = t then p.natAbs else 1

/-- The single letter out of which the block replacing `c` consists.  For `c.1 = t` the
sign of the letter is `c.2` when `p > 0` and `!c.2` when `p < 0`. -/
def powSubstBlockLetter (t : α) (p : ℤ) (c : α × Bool) : α × Bool :=
  if c.1 = t then (t, if 0 < p then c.2 else !c.2) else c

/-- The block of letters replacing a single letter `c` under the substitution `t ↦ t ^ p`. -/
def powSubstBlock (t : α) (p : ℤ) (c : α × Bool) : List (α × Bool) :=
  List.replicate (powSubstBlockLen t p c) (powSubstBlockLetter t p c)

theorem powSubstBlock_eq (t : α) (p : ℤ) (c : α × Bool) :
    powSubstBlock t p c = List.replicate (powSubstBlockLen t p c) (powSubstBlockLetter t p c) :=
  rfl

theorem powSubstBlockLen_pos (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    0 < powSubstBlockLen t p c := by
  unfold powSubstBlockLen
  split
  · exact Int.natAbs_pos.mpr hp
  · exact Nat.one_pos

theorem powSubstBlock_ne_nil (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    powSubstBlock t p c ≠ [] := by
  rw [powSubstBlock_eq, List.ne_nil_iff_length_pos, List.length_replicate]
  exact powSubstBlockLen_pos t p hp c

theorem fst_powSubstBlockLetter (t : α) (p : ℤ) (c : α × Bool) :
    (powSubstBlockLetter t p c).1 = c.1 := by
  obtain ⟨a, b⟩ := c
  by_cases h : a = t <;> simp [powSubstBlockLetter, h]

theorem powSubstBlockLetter_eq_of (t : α) (p : ℤ) {c₁ c₂ : α × Bool}
    (h1 : c₁.1 = c₂.1) (h2 : c₁.2 = c₂.2) :
    powSubstBlockLetter t p c₁ = powSubstBlockLetter t p c₂ := by
  obtain ⟨a₁, b₁⟩ := c₁
  obtain ⟨a₂, b₂⟩ := c₂
  have h1' : a₁ = a₂ := h1
  have h2' : b₁ = b₂ := h2
  subst h1'; subst h2'
  rfl

theorem powSubstBlockLetter_rel (t : α) (p : ℤ) (c₁ c₂ : α × Bool)
    (hQ : c₁.1 = c₂.1 → c₁.2 = c₂.2) :
    (powSubstBlockLetter t p c₁).1 = (powSubstBlockLetter t p c₂).1 →
      (powSubstBlockLetter t p c₁).2 = (powSubstBlockLetter t p c₂).2 := by
  intro hcon
  have hcc : c₁.1 = c₂.1 :=
    (fst_powSubstBlockLetter t p c₁).symm.trans (hcon.trans (fst_powSubstBlockLetter t p c₂))
  exact congrArg Prod.snd (powSubstBlockLetter_eq_of t p hcc (hQ hcc))

theorem powSubstBlock_isReduced (t : α) (p : ℤ) (c : α × Bool) :
    FreeGroup.IsReduced (powSubstBlock t p c) :=
  FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_replicate _ _)

theorem head?_powSubstBlock (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    (powSubstBlock t p c).head? = some (powSubstBlockLetter t p c) := by
  rw [powSubstBlock_eq, List.head?_replicate,
    if_neg (Nat.ne_of_gt (powSubstBlockLen_pos t p hp c))]

theorem getLast?_powSubstBlock (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    (powSubstBlock t p c).getLast? = some (powSubstBlockLetter t p c) := by
  rw [powSubstBlock_eq, List.getLast?_replicate,
    if_neg (Nat.ne_of_gt (powSubstBlockLen_pos t p hp c))]

end Blocks

end Work.OROneRel
