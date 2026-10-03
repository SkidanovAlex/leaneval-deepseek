/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Injectivity of the Nielsen substitution `t ↦ t ^ p`

`powSubst t p : F(α) →* F(α)` sends the generator `t` to `t ^ p` and fixes every other generator
(`psiSubstDefs`).  For `p ≠ 0` this is injective, because `{t ^ p} ∪ {a : a ≠ t}` is an independent
set of elements of `F α`.

The proof is the word-level form of that statement.  The reduced word of `w` is substituted letter
by letter: a `t`-letter is replaced by a block of `|p|` copies of `t` (with the appropriate sign,
accounting for the sign of `p`), and every other letter stays a single letter.  The substituted
word is again reduced (`powSubstBlk_flatten_reduced`) and non-empty when the original word is
(`powSubstBlk_flatten_ne_nil`), while `powSubst t p (mk L) = mk (substituted word)`
(`powSubst_mk`).  Hence a non-trivial element stays non-trivial.
-/
import Mathlib
import Submission.Work.OROneRel.psiSubstDefs

namespace Work.OROneRel

universe u

section BlockSubst

variable {α : Type u}

private lemma invRev_replicate (k : ℕ) (a : α) (b : Bool) :
    FreeGroup.invRev (List.replicate k (a, b)) = List.replicate k (a, !b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, FreeGroup.invRev_cons, ih]
    rw [show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl]
    rw [List.replicate_succ']

variable [DecidableEq α]

private lemma toWord_zpow_of (a : α) (n : ℤ) :
    ((FreeGroup.of a) ^ n).toWord = List.replicate n.natAbs (a, if 0 < n then true else false) := by
  rcases lt_trichotomy n 0 with h | h | h
  · have h2 : (FreeGroup.of a) ^ n = ((FreeGroup.of a) ^ (-n))⁻¹ := by
      conv_lhs => rw [← Int.neg_neg n, zpow_neg]
    rw [h2, FreeGroup.toWord_inv, ← Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n), zpow_natCast,
      FreeGroup.toWord_of_pow, invRev_replicate]
    have h3 : (-n).toNat = n.natAbs := by omega
    rw [h3, if_neg (by omega : ¬ (0 < n))]
    rfl
  · subst h; simp
  · conv_lhs => rw [← Int.toNat_of_nonneg (le_of_lt h), zpow_natCast]
    rw [FreeGroup.toWord_of_pow, if_pos h]
    have h3 : n.natAbs = n.toNat := by omega
    rw [h3]

private lemma toWord_inv_zpow_of (a : α) (n : ℤ) (hn : n ≠ 0) :
    (((FreeGroup.of a) ^ n)⁻¹).toWord =
      List.replicate n.natAbs (a, if 0 < n then false else true) := by
  rw [show ((FreeGroup.of a) ^ n)⁻¹ = (FreeGroup.of a) ^ (-n) from (zpow_neg _ n).symm,
    toWord_zpow_of]
  rw [Int.natAbs_neg]
  by_cases h : 0 < n
  · rw [if_neg (by omega : ¬ (0 < -n)), if_pos h]
  · rw [if_pos (by omega : 0 < -n), if_neg h]

/-- The image in `F α` of a single letter `c = (a, s)` of a reduced word under `powSubst t p`. -/
noncomputable def powSubstLetter (t : α) (p : ℤ) (c : α × Bool) : FreeGroup α :=
  cond c.2 (powSubstFun t p c.1) ((powSubstFun t p c.1)⁻¹)

/-- The block of letters of the reduced word of `powSubstLetter t p c`. -/
noncomputable def powSubstBlk (t : α) (p : ℤ) (c : α × Bool) : List (α × Bool) :=
  (powSubstLetter t p c).toWord

/-- The length of the block of a letter: `|p|` for `t`, and `1` for every other letter. -/
def powSubstBlkLen (t : α) (p : ℤ) (c : α × Bool) : ℕ :=
  if c.1 = t then p.natAbs else 1

/-- The (single) letter out of which the block of a letter consists. -/
def powSubstBlkLetter (t : α) (p : ℤ) (c : α × Bool) : α × Bool :=
  if c.1 = t then (t, if 0 < p then c.2 else !c.2) else c

private lemma powSubstBlk_eq (t : α) (p : ℤ) (_hp : p ≠ 0) (c : α × Bool) :
    powSubstBlk t p c = List.replicate (powSubstBlkLen t p c) (powSubstBlkLetter t p c) := by
  obtain ⟨a, b⟩ := c
  cases b
  · by_cases h : a = t
    · subst h
      simp only [powSubstBlk, powSubstLetter, powSubstFun, ↓reduceIte, cond_false,
        FreeGroup.toWord_inv, powSubstBlkLen, powSubstBlkLetter, Bool.not_false,
        Bool.if_true_right, Bool.or_false]
      rw [toWord_zpow_of, invRev_replicate]
      by_cases h2 : 0 < p <;> simp [h2]
    · simp only [powSubstBlk, powSubstLetter, powSubstFun, h, ↓reduceIte, cond_false,
        FreeGroup.toWord_inv, FreeGroup.toWord_of, powSubstBlkLen, powSubstBlkLetter,
        List.replicate_one]
      rfl
  · by_cases h : a = t
    · subst h
      simp only [powSubstBlk, powSubstLetter, powSubstFun, ↓reduceIte, cond_true,
        powSubstBlkLen, powSubstBlkLetter, Bool.not_true, Bool.if_false_right, Bool.and_true]
      rw [toWord_zpow_of]
      by_cases h2 : 0 < p <;> simp [h2]
    · simp only [powSubstBlk, powSubstLetter, powSubstFun, h, ↓reduceIte, cond_true,
        FreeGroup.toWord_of, powSubstBlkLen, powSubstBlkLetter, List.replicate_one]

private lemma powSubstBlkLen_pos (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    0 < powSubstBlkLen t p c := by
  obtain ⟨a, b⟩ := c
  by_cases h : a = t
  · simp [powSubstBlkLen, h, Int.natAbs_pos.mpr hp]
  · simp [powSubstBlkLen, h]

private lemma powSubstBlk_ne_nil (t : α) (p : ℤ) (hp : p ≠ 0) (c : α × Bool) :
    powSubstBlk t p c ≠ [] := by
  rw [powSubstBlk_eq t p hp c, List.ne_nil_iff_length_pos, List.length_replicate]
  exact powSubstBlkLen_pos t p hp c

private lemma fst_powSubstBlkLetter (t : α) (p : ℤ) (c : α × Bool) :
    (powSubstBlkLetter t p c).1 = c.1 := by
  obtain ⟨a, b⟩ := c
  by_cases h : a = t <;> simp [powSubstBlkLetter, h]

private lemma powSubstBlkLetter_rel (t : α) (p : ℤ) (c1 c2 : α × Bool)
    (hQ : c1.1 = c2.1 → c1.2 = c2.2) :
    (powSubstBlkLetter t p c1).1 = (powSubstBlkLetter t p c2).1 →
      (powSubstBlkLetter t p c1).2 = (powSubstBlkLetter t p c2).2 := by
  intro hcon
  have hc : c1.1 = c2.1 :=
    (fst_powSubstBlkLetter t p c1).symm.trans (hcon.trans (fst_powSubstBlkLetter t p c2))
  have hb : c1.2 = c2.2 := hQ hc
  rw [show c1 = c2 from Prod.ext hc hb]

private lemma powSubstBlk_flatten_reduced (t : α) (p : ℤ) (hp : p ≠ 0)
    {L : List (α × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced ((L.map (powSubstBlk t p)).flatten) := by
  rw [FreeGroup.IsReduced] at hL ⊢
  have hnil : [] ∉ L.map (powSubstBlk t p) := by
    intro hmem
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
    exact powSubstBlk_ne_nil t p hp c hc
  rw [List.isChain_flatten hnil]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
    rw [powSubstBlk_eq t p hp c]
    exact FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_replicate _ _)
  · refine List.isChain_map_of_isChain (powSubstBlk t p) ?_ hL
    intro c1 c2 hQ u hu v hv
    have hn1 : powSubstBlkLen t p c1 ≠ 0 := Nat.ne_of_gt (powSubstBlkLen_pos t p hp c1)
    have hn2 : powSubstBlkLen t p c2 ≠ 0 := Nat.ne_of_gt (powSubstBlkLen_pos t p hp c2)
    rw [powSubstBlk_eq t p hp c1, List.getLast?_replicate, if_neg hn1] at hu
    rw [powSubstBlk_eq t p hp c2, List.head?_replicate, if_neg hn2] at hv
    simp only [Option.mem_some_iff] at hu hv
    subst hu
    subst hv
    exact powSubstBlkLetter_rel t p c1 c2 hQ

private lemma powSubstBlk_flatten_ne_nil (t : α) (p : ℤ) (hp : p ≠ 0)
    {L : List (α × Bool)} (hL : L ≠ []) : (L.map (powSubstBlk t p)).flatten ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c L' =>
    rw [List.map_cons, List.flatten_cons]
    exact List.append_ne_nil_of_left_ne_nil (powSubstBlk_ne_nil t p hp c) _

private lemma mk_flatten_powSubstBlk (t : α) (p : ℤ) (L : List (α × Bool)) :
    FreeGroup.mk ((L.map (powSubstBlk t p)).flatten)
      = (L.map (powSubstLetter t p)).prod := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    simp only [List.map_cons, List.flatten_cons, List.prod_cons]
    rw [← FreeGroup.mul_mk, ih]
    simp only [powSubstBlk, FreeGroup.mk_toWord]

private lemma powSubst_mk (t : α) (p : ℤ) (L : List (α × Bool)) :
    powSubst t p (FreeGroup.mk L) = FreeGroup.mk ((L.map (powSubstBlk t p)).flatten) := by
  rw [powSubst, FreeGroup.lift_mk, mk_flatten_powSubstBlk t p L]
  congr 1

end BlockSubst

theorem powSubst_injective {α : Type*} (t : α) (p : ℤ) (hp : p ≠ 0) :
    Function.Injective (Work.OROneRel.powSubst (α := α) t p) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  by_contra hne
  have hL : u.toWord ≠ [] := fun h => hne (FreeGroup.toWord_eq_nil_iff.mp h)
  have hred : FreeGroup.IsReduced ((u.toWord.map (powSubstBlk t p)).flatten) :=
    powSubstBlk_flatten_reduced t p hp FreeGroup.isReduced_toWord
  have hnn : (u.toWord.map (powSubstBlk t p)).flatten ≠ [] :=
    powSubstBlk_flatten_ne_nil t p hp hL
  have h1 : FreeGroup.mk ((u.toWord.map (powSubstBlk t p)).flatten) = 1 := by
    rw [← powSubst_mk t p u.toWord, FreeGroup.mk_toWord]
    exact hu
  have h2 : FreeGroup.mk ((u.toWord.map (powSubstBlk t p)).flatten) ≠ 1 := by
    intro h
    have h3 := congrArg FreeGroup.toWord h
    rw [FreeGroup.toWord_mk, FreeGroup.toWord_one] at h3
    rw [FreeGroup.IsReduced.reduce_eq hred] at h3
    exact hnn h3
  exact h2 h1

end Work.OROneRel
