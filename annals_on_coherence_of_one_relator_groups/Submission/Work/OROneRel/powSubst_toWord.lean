/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The reduced word of `powSubst t p (mk L)`

`powSubst t p : F(α) →* F(α)` is the Nielsen substitution `t ↦ t ^ p` fixing every other
generator (`psiSubstDefs`).  This file computes the reduced word of its value on an element
presented by a *reduced* word `L`: substituting the letters of `L` letter by letter, a `t`-letter
`c = (t, b)` is replaced by the block of `|p|` copies of `t` with the sign `b` (flipped when
`p < 0`), and every other letter is left as it is.

The key points are that the substituted letter `powSubstLetter` of a letter `c` is the free-group
element `mk (powBlk t p c)` whose reduced word is exactly that block (`powSubstLetter_eq_mk`), so
that `powSubst t p (mk L) = mk ((L.map (powBlk t p)).flatten)` (`powSubst_mk`), and that the
concatenation of the blocks of a reduced word is again reduced (`isReduced_powBlk_flatten`), so
that this concatenation is the reduced word of the image.
-/
import Mathlib
import Submission.Work.OROneRel.psiSubstDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The block substituted for the letter `c = (a, b)` of a word under the Nielsen substitution
`powSubst t p`: `|p|` copies of the letter `t` with the sign of `c` (flipped when `p < 0`) if
`a = t`, and the single letter `c` otherwise. -/
private def powBlk [DecidableEq α] (t : α) (p : ℤ) (c : α × Bool) : List (α × Bool) :=
  if c.1 = t then List.replicate p.natAbs (t, if 0 < p then c.2 else !c.2) else [c]

/-- The length of the block of a letter: `|p|` for `t`, and `1` for every other letter. -/
private def powBlkLen [DecidableEq α] (t : α) (p : ℤ) (c : α × Bool) : ℕ :=
  if c.1 = t then p.natAbs else 1

/-- The (single) letter out of which the block of a letter consists. -/
private def powBlkLetter [DecidableEq α] (t : α) (p : ℤ) (c : α × Bool) : α × Bool :=
  if c.1 = t then (t, if 0 < p then c.2 else !c.2) else c

section BlockSubst

variable [DecidableEq α]

private lemma powBlk_of_eq (t : α) (p : ℤ) (c : α × Bool) (h : c.1 = t) :
    powBlk t p c = List.replicate p.natAbs (t, if 0 < p then c.2 else !c.2) := by
  rw [powBlk, if_pos h]

private lemma powBlk_of_ne (t : α) (p : ℤ) (c : α × Bool) (h : c.1 ≠ t) :
    powBlk t p c = [c] := by
  rw [powBlk, if_neg h]

/-- The block of a letter is the replicate of a single letter. -/
private lemma powBlk_eq (t : α) (p : ℤ) (c : α × Bool) :
    powBlk t p c = List.replicate (powBlkLen t p c) (powBlkLetter t p c) := by
  obtain ⟨a, b⟩ := c
  by_cases h : a = t
  · simp [powBlk, powBlkLen, powBlkLetter, h]
  · simp [powBlk, powBlkLen, powBlkLetter, h]

private lemma powBlkLen_pos (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    0 < powBlkLen t p c := by
  obtain ⟨a, b⟩ := c
  by_cases h : a = t
  · simp [powBlkLen, h, Int.natAbs_pos.mpr hp]
  · simp [powBlkLen, h]

private lemma powBlk_ne_nil (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) : powBlk t p c ≠ [] := by
  rw [powBlk_eq t p c, List.ne_nil_iff_length_pos, List.length_replicate]
  exact powBlkLen_pos t p hp c

private lemma fst_powBlkLetter (t : α) (p : ℤ) (c : α × Bool) :
    (powBlkLetter t p c).1 = c.1 := by
  obtain ⟨a, b⟩ := c
  by_cases h : a = t <;> simp [powBlkLetter, h]

private lemma powBlkLetter_rel (t : α) (p : ℤ) (c1 c2 : α × Bool)
    (hQ : c1.1 = c2.1 → c1.2 = c2.2) :
    (powBlkLetter t p c1).1 = (powBlkLetter t p c2).1 →
      (powBlkLetter t p c1).2 = (powBlkLetter t p c2).2 := by
  intro hcon
  have hc : c1.1 = c2.1 :=
    (fst_powBlkLetter t p c1).symm.trans (hcon.trans (fst_powBlkLetter t p c2))
  have hb : c1.2 = c2.2 := hQ hc
  rw [show c1 = c2 from Prod.ext hc hb]

/-- The concatenation of the blocks of a reduced word is again reduced. -/
private lemma isReduced_powBlk_flatten (t : α) (p : ℤ) (hp : p ≠ 0)
    {L : List (α × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced ((L.map (powBlk t p)).flatten) := by
  rw [FreeGroup.IsReduced] at hL ⊢
  have hnil : [] ∉ L.map (powBlk t p) := by
    intro hmem
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
    exact powBlk_ne_nil t p hp c hc
  rw [List.isChain_flatten hnil]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
    rw [powBlk_eq t p c]
    exact FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_replicate _ _)
  · refine List.isChain_map_of_isChain (powBlk t p) ?_ hL
    intro c1 c2 hQ u hu v hv
    have hn1 : powBlkLen t p c1 ≠ 0 := Nat.ne_of_gt (powBlkLen_pos t p hp c1)
    have hn2 : powBlkLen t p c2 ≠ 0 := Nat.ne_of_gt (powBlkLen_pos t p hp c2)
    rw [powBlk_eq t p c1, List.getLast?_replicate, if_neg hn1] at hu
    rw [powBlk_eq t p c2, List.head?_replicate, if_neg hn2] at hv
    simp only [Option.mem_some_iff] at hu hv
    subst hu
    subst hv
    exact powBlkLetter_rel t p c1 c2 hQ

/-! ### The reduced word of a power of a generator -/

omit [DecidableEq α] in
private lemma invRev_replicate (k : ℕ) (a : α) (b : Bool) :
    FreeGroup.invRev (List.replicate k (a, b)) = List.replicate k (a, !b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, FreeGroup.invRev_cons, ih]
    rw [show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl]
    rw [List.replicate_succ']

private lemma toWord_zpow_of (a : α) (n : ℤ) :
    ((FreeGroup.of a) ^ n).toWord = List.replicate n.natAbs (a, if 0 < n then true else false) := by
  rcases lt_trichotomy n 0 with h | h | h
  · have h2 : (FreeGroup.of a) ^ n = ((FreeGroup.of a) ^ (-n))⁻¹ := by
      conv_lhs => rw [← Int.neg_neg n, zpow_neg]
    rw [h2, FreeGroup.toWord_inv, ← Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n), zpow_natCast,
      FreeGroup.toWord_of_pow, invRev_replicate]
    have h3 : (-n).toNat = n.natAbs := by omega
    rw [h3, if_neg (by omega : ¬ (0 < n))]
    rfl
  · subst h; simp
  · conv_lhs => rw [← Int.toNat_of_nonneg (le_of_lt h), zpow_natCast]
    rw [FreeGroup.toWord_of_pow]
    simp only [if_pos h]
    rw [show n.toNat = n.natAbs from by omega]

private lemma toWord_inv_zpow_of (a : α) (n : ℤ) :
    (((FreeGroup.of a) ^ n)⁻¹).toWord =
      List.replicate n.natAbs (a, if 0 < n then false else true) := by
  rw [FreeGroup.toWord_inv, toWord_zpow_of, invRev_replicate]
  congr 1
  by_cases h : 0 < n <;> simp [h]

private lemma of_eq_mk (a : α) : FreeGroup.of a = FreeGroup.mk [(a, true)] := by
  rw [← FreeGroup.mk_toWord (x := FreeGroup.of a), FreeGroup.toWord_of]

private lemma inv_of_eq_mk (a : α) : (FreeGroup.of a)⁻¹ = FreeGroup.mk [(a, false)] := by
  rw [← FreeGroup.mk_toWord (x := (FreeGroup.of a)⁻¹), FreeGroup.toWord_inv, FreeGroup.toWord_of]
  rfl

private lemma zpow_of_eq_mk (a : α) (n : ℤ) :
    (FreeGroup.of a) ^ n =
      FreeGroup.mk (List.replicate n.natAbs (a, if 0 < n then true else false)) := by
  rw [← FreeGroup.mk_toWord (x := (FreeGroup.of a) ^ n), toWord_zpow_of]

private lemma inv_zpow_of_eq_mk (a : α) (n : ℤ) :
    ((FreeGroup.of a) ^ n)⁻¹ =
      FreeGroup.mk (List.replicate n.natAbs (a, if 0 < n then false else true)) := by
  rw [← FreeGroup.mk_toWord (x := ((FreeGroup.of a) ^ n)⁻¹), toWord_inv_zpow_of]

/-! ### The image of a single letter -/

/-- The image of a single letter `c` under `powSubst t p` is `mk (powBlk t p c)`. -/
private lemma powSubstLetter_eq_mk (t : α) (p : ℤ) (c : α × Bool) :
    (cond c.2 (powSubstFun t p c.1) ((powSubstFun t p c.1)⁻¹)) =
      FreeGroup.mk (powBlk t p c) := by
  obtain ⟨a, b⟩ := c
  cases b
  · change (powSubstFun t p a)⁻¹ = FreeGroup.mk (powBlk t p (a, false))
    by_cases h : a = t
    · rw [h, show powSubstFun t p t = FreeGroup.of t ^ p from by simp [powSubstFun],
        inv_zpow_of_eq_mk, powBlk_of_eq t p (t, false) rfl]
      rfl
    · rw [show powBlk t p (a, false) = [(a, false)] from
          powBlk_of_ne t p (a, false) (by simpa using h)]
      rw [show powSubstFun t p a = FreeGroup.of a from by simp [powSubstFun, h]]
      rw [inv_of_eq_mk]
  · change powSubstFun t p a = FreeGroup.mk (powBlk t p (a, true))
    by_cases h : a = t
    · rw [h, show powSubstFun t p t = FreeGroup.of t ^ p from by simp [powSubstFun],
        zpow_of_eq_mk, powBlk_of_eq t p (t, true) rfl]
      rfl
    · rw [show powBlk t p (a, true) = [(a, true)] from
          powBlk_of_ne t p (a, true) (by simpa using h)]
      rw [show powSubstFun t p a = FreeGroup.of a from by simp [powSubstFun, h]]
      rw [of_eq_mk]

/-- `powSubst t p` of an element presented by a word is the concatenation of the blocks of the
letters of the word. -/
private lemma powSubst_mk (t : α) (p : ℤ) (L : List (α × Bool)) :
    powSubst t p (FreeGroup.mk L) = FreeGroup.mk ((L.map (powBlk t p)).flatten) := by
  rw [powSubst, FreeGroup.lift_mk]
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.flatten_cons, ih,
      powSubstLetter_eq_mk t p c, FreeGroup.mul_mk]

end BlockSubst

theorem powSubst_toWord {α : Type*} [DecidableEq α] (t : α) (p : ℤ) (hp : p ≠ 0) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) :
    (Work.OROneRel.powSubst t p (FreeGroup.mk L)).toWord =
      (L.map (fun c : α × Bool =>
        if c.1 = t then List.replicate p.natAbs (t, if 0 < p then c.2 else !c.2) else [c])).flatten := by
  change (Work.OROneRel.powSubst t p (FreeGroup.mk L)).toWord = (L.map (powBlk t p)).flatten
  rw [powSubst_mk t p L, FreeGroup.toWord_mk,
    FreeGroup.IsReduced.reduce_eq (isReduced_powBlk_flatten t p hp hL)]

end Work.OROneRel
