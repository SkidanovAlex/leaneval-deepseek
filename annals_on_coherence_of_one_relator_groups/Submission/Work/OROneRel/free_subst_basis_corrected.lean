/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).
-/
import Mathlib

/-!
# A free substitution basis: `F(S) →* F(α)` sending the extra generator to `t ^ p`

Let `x t : α` be distinct generators of the free group `F α`, and let `p : ℤ`, `p ≠ 0`.  Write
`S = {a : α // a ≠ x ∧ a ≠ t} ⊕ Unit`.  The map on generators
`a ↦ of a` (for `a ≠ x, t`) and `* ↦ of t ^ p` extends to a homomorphism
`φ : F(S) →* F(α)`, and `φ` is injective: the set `{of a : a ≠ x, t} ∪ {of t ^ p}` is an
independent (indeed free-basis) subset of `F α`.

The proof is the standard block argument: the image of a reduced word is again reduced.  An
`a`-letter (with `a ≠ t`) becomes a single letter, the extra generator becomes a block `t^{±p}`
of `|p| ≥ 1` letters, and two successive blocks never cancel: a `t`-block against a single letter
`a ≠ t`, two distinct letters, or two `t`-blocks of the same sign (the latter because the original
word is reduced).
-/

namespace Work.OROneRel

universe u

section

variable {α : Type u}

/-- Index type of the generators of the "substituted" free group: the generators of `F α` other
than `x` and `t`, together with one extra generator standing for `t ^ p`. -/
private abbrev SubstIdx (x t : α) := {a : α // a ≠ x ∧ a ≠ t} ⊕ Unit

/-- The map on generators: `a` (with `a ≠ x, t`) maps to `of a`, and the extra generator maps to
`of t ^ p`. -/
private abbrev substGen (x t : α) (p : ℤ) : SubstIdx x t → FreeGroup α :=
  Sum.elim (fun a : {a : α // a ≠ x ∧ a ≠ t} => FreeGroup.of (a.1 : α))
    (fun _ : Unit => (FreeGroup.of t) ^ p)

private lemma invRev_replicate {α : Type u} (k : ℕ) (a : α) (b : Bool) :
    FreeGroup.invRev (List.replicate k (a, b)) = List.replicate k (a, !b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, FreeGroup.invRev_cons, ih]
    rw [show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl]
    rw [List.replicate_succ']

/-- The normal form of `(of a) ^ n`: a block of `|n|` copies of the letter `a`, each with the
sign of `n`. -/
private lemma toWord_zpow_of {α : Type u} [DecidableEq α] (a : α) (n : ℤ) :
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

/-- The normal form of `((of a) ^ n)⁻¹` (for `n ≠ 0`): the same block with the opposite sign. -/
private lemma toWord_inv_zpow_of {α : Type u} [DecidableEq α] (a : α) (n : ℤ) (hn : n ≠ 0) :
    (((FreeGroup.of a) ^ n)⁻¹).toWord = List.replicate n.natAbs (a, if 0 < n then false else true) := by
  rw [show ((FreeGroup.of a) ^ n)⁻¹ = (FreeGroup.of a) ^ (-n) from (zpow_neg _ n).symm,
    toWord_zpow_of]
  rw [Int.natAbs_neg]
  by_cases h : 0 < n
  · rw [if_neg (by omega : ¬ (0 < -n)), if_pos h]
  · rw [if_pos (by omega : 0 < -n), if_neg h]

/-- The image of a single letter `(c, s)` of `F(S)` under the substitution, written out as a word
over `α`: one letter for `c = inl a`, a block of `|p|` `t`-letters for `c = inr ()`. -/
private noncomputable def substBlk {α : Type u} [DecidableEq α] (x t : α) (p : ℤ)
    (c : SubstIdx x t × Bool) : List (α × Bool) :=
  (bif c.2 then substGen x t p c.1 else (substGen x t p c.1)⁻¹).toWord

/-- Length of the substituted block of a letter. -/
private def substBlkLen {α : Type u} (x t : α) (p : ℤ) : SubstIdx x t × Bool → ℕ
  | (Sum.inl _, _) => 1
  | (Sum.inr _, _) => p.natAbs

/-- The (single) letter out of which the substituted block of a letter consists. -/
private def substBlkLetter {α : Type u} (x t : α) (p : ℤ) : SubstIdx x t × Bool → α × Bool
  | (Sum.inl a, s) => (a.1, s)
  | (Sum.inr _, s) => (t, if 0 < p then s else !s)

private lemma substBlkLen_pos {α : Type u} (x t : α) (p : ℤ) (hp : p ≠ 0)
    (c : SubstIdx x t × Bool) : 0 < substBlkLen x t p c := by
  obtain ⟨c1, s⟩ := c
  cases c1 with
  | inl a => simp [substBlkLen]
  | inr u => simpa [substBlkLen] using (Int.natAbs_pos.mpr hp)

/-- Each substituted block is a `List.replicate` of a single letter. -/
private lemma substBlk_eq {α : Type u} [DecidableEq α] (x t : α) (p : ℤ) (hp : p ≠ 0)
    (c : SubstIdx x t × Bool) :
    substBlk x t p c = List.replicate (substBlkLen x t p c) (substBlkLetter x t p c) := by
  obtain ⟨c1, s⟩ := c
  cases c1 with
  | inl a =>
    cases s
    · show ((substGen x t p (Sum.inl a))⁻¹).toWord = List.replicate 1 (a.1, false)
      rw [substGen, Sum.elim_inl, FreeGroup.toWord_inv, FreeGroup.toWord_of]
      rw [show FreeGroup.invRev [(a.1, true)] = [(a.1, false)] from rfl]
      rfl
    · show (substGen x t p (Sum.inl a)).toWord = List.replicate 1 (a.1, true)
      rw [substGen, Sum.elim_inl, FreeGroup.toWord_of]
      rfl
  | inr u =>
    cases s
    · show ((substGen x t p (Sum.inr u))⁻¹).toWord =
        List.replicate p.natAbs (t, if 0 < p then false else !false)
      rw [substGen, Sum.elim_inr, toWord_inv_zpow_of t p hp, Bool.not_false]
    · show (substGen x t p (Sum.inr u)).toWord =
        List.replicate p.natAbs (t, if 0 < p then true else !true)
      rw [substGen, Sum.elim_inr, toWord_zpow_of, Bool.not_true]

private lemma substBlk_ne_nil {α : Type u} [DecidableEq α] (x t : α) (p : ℤ) (hp : p ≠ 0)
    (c : SubstIdx x t × Bool) : substBlk x t p c ≠ [] := by
  rw [substBlk_eq x t p hp c, List.ne_nil_iff_length_pos, List.length_replicate]
  exact substBlkLen_pos x t p hp c

/-- Successive substituted blocks of a reduced word never cancel: two distinct generators give
letters with different first components (or the same `inl` generator, in which case reducedness
forces the same sign), and `t` is distinct from every `inl` generator. -/
private lemma substBlkLetter_rel {α : Type u} (x t : α) (p : ℤ) (c1 c2 : SubstIdx x t × Bool)
    (hQ : c1.1 = c2.1 → c1.2 = c2.2) :
    (substBlkLetter x t p c1).1 = (substBlkLetter x t p c2).1 →
      (substBlkLetter x t p c1).2 = (substBlkLetter x t p c2).2 := by
  obtain ⟨d1, s1⟩ := c1
  obtain ⟨d2, s2⟩ := c2
  cases d1 with
  | inl a1 =>
    cases d2 with
    | inl a2 =>
      intro h
      have hd : (Sum.inl a1 : SubstIdx x t) = Sum.inl a2 := by rw [Subtype.ext h]
      have hs : s1 = s2 := hQ hd
      simpa [substBlkLetter] using hs
    | inr u2 => intro h; exact absurd h a1.2.2
  | inr u1 =>
    cases d2 with
    | inl a2 => intro h; exact absurd h.symm a2.2.2
    | inr u2 =>
      intro h
      have hs : s1 = s2 := hQ (by simp)
      rw [hs]

/-- The substitution of a reduced word is reduced. -/
private lemma substReduced {α : Type u} [DecidableEq α] (x t : α) (p : ℤ) (hp : p ≠ 0)
    {L : List (SubstIdx x t × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced ((L.map (substBlk x t p)).flatten) := by
  rw [FreeGroup.IsReduced] at hL ⊢
  have hnil : [] ∉ L.map (substBlk x t p) := by
    intro hmem
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
    exact substBlk_ne_nil x t p hp c hc
  rw [List.isChain_flatten hnil]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
    exact FreeGroup.isReduced_toWord
  · refine List.isChain_map_of_isChain (substBlk x t p) ?_ hL
    intro c1 c2 hQ u hu v hv
    have hn1 : substBlkLen x t p c1 ≠ 0 := Nat.ne_of_gt (substBlkLen_pos x t p hp c1)
    have hn2 : substBlkLen x t p c2 ≠ 0 := Nat.ne_of_gt (substBlkLen_pos x t p hp c2)
    rw [substBlk_eq x t p hp c1, List.getLast?_replicate, if_neg hn1] at hu
    rw [substBlk_eq x t p hp c2, List.head?_replicate, if_neg hn2] at hv
    simp only [Option.mem_some_iff] at hu hv
    subst hu; subst hv
    exact substBlkLetter_rel x t p c1 c2 hQ

/-- The substitution of a nonempty word is nonempty (every block has positive length). -/
private lemma substFlatten_ne_nil {α : Type u} [DecidableEq α] (x t : α) (p : ℤ) (hp : p ≠ 0)
    {L : List (SubstIdx x t × Bool)} (hL : L ≠ []) :
    (L.map (substBlk x t p)).flatten ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c L' =>
    rw [List.map_cons, List.flatten_cons]
    exact List.append_ne_nil_of_left_ne_nil (substBlk_ne_nil x t p hp c) _

/-- `FreeGroup.lift` of `mk L` is `mk` of the substituted word. -/
private lemma lift_mk_subst {α : Type u} [DecidableEq α] (x t : α) (p : ℤ)
    (L : List (SubstIdx x t × Bool)) :
    FreeGroup.lift (substGen x t p) (FreeGroup.mk L) =
      FreeGroup.mk ((L.map (substBlk x t p)).flatten) := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [FreeGroup.lift_mk, List.map_cons, List.prod_cons]
    rw [← FreeGroup.lift_mk (f := substGen x t p), ih]
    rw [List.map_cons, List.flatten_cons, ← FreeGroup.mul_mk]
    have hc : (bif c.2 then substGen x t p c.1 else (substGen x t p c.1)⁻¹) =
        FreeGroup.mk (substBlk x t p c) := by
      rw [substBlk]
      exact FreeGroup.mk_toWord.symm
    rw [hc]

set_option linter.unusedVariables false

/-- **Correct form of the requested lemma.**  The set `{of a : a ≠ x, t} ∪ {of t ^ p}` is
independent in `F α`: the substitution map is injective. -/
theorem free_subst_basis_corrected {α : Type u} (x t : α) (hxt : x ≠ t) (p : ℤ) (hp : p ≠ 0) :
    Function.Injective (FreeGroup.lift (Sum.elim
        (fun a : {a : α // a ≠ x ∧ a ≠ t} => FreeGroup.of (a.1 : α))
        (fun _ : Unit => (FreeGroup.of t) ^ p))) := by
  classical
  change Function.Injective (FreeGroup.lift (substGen x t p))
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  by_contra hne
  have hL : u.toWord ≠ [] := by
    intro h
    exact hne (FreeGroup.toWord_eq_nil_iff.mp h)
  have hred : FreeGroup.IsReduced ((u.toWord.map (substBlk x t p)).flatten) :=
    substReduced x t p hp FreeGroup.isReduced_toWord
  have hnn : (u.toWord.map (substBlk x t p)).flatten ≠ [] :=
    substFlatten_ne_nil x t p hp hL
  have h1 : FreeGroup.mk ((u.toWord.map (substBlk x t p)).flatten) = 1 := by
    rw [← lift_mk_subst x t p u.toWord, FreeGroup.mk_toWord]
    exact hu
  have h2 : FreeGroup.mk ((u.toWord.map (substBlk x t p)).flatten) ≠ 1 := by
    intro h
    have h3 := congrArg FreeGroup.toWord h
    rw [FreeGroup.toWord_mk, FreeGroup.toWord_one] at h3
    rw [FreeGroup.IsReduced.reduce_eq hred] at h3
    exact hnn h3
  exact h2 h1

end

end Work.OROneRel
