/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Nielsen substitution `t ↦ t ^ p` preserves cyclic reducedness

If `L` is a reduced, cyclically reduced word, then the reduced word of `powSubst t p (mk L)` is
again cyclically reduced.  The proof replaces every letter of `L` by its block
(`Submission.Work.OROneRel.powSubstBlockDefs`), shows that the concatenation of the blocks is
reduced and cyclically reduced, and identifies it with `(powSubst t p (mk L)).toWord`.
-/
import Mathlib
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.powSubstBlockDefs

namespace Work.OROneRel

universe u

section Support

variable {α : Type u} [DecidableEq α]

/-- The inverse-reversal of a constant run of letters is the run with the sign flipped. -/
private theorem invRev_replicate (k : ℕ) (a : α) (b : Bool) :
    FreeGroup.invRev (List.replicate k (a, b)) = List.replicate k (a, !b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, FreeGroup.invRev_cons, ih]
    rw [show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl]
    rw [List.replicate_succ']

/-- The reduced word of an integral power of a generator. -/
theorem zpow_toWord (a : α) (n : ℤ) :
    ((FreeGroup.of a) ^ n).toWord = List.replicate n.natAbs (a, if 0 < n then true else false) := by
  rcases lt_trichotomy n 0 with h | h | h
  · have h2 : (FreeGroup.of a) ^ n = ((FreeGroup.of a) ^ (-n))⁻¹ := by
      rw [zpow_neg, inv_inv]
    rw [h2, FreeGroup.toWord_inv, ← Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n), zpow_natCast,
      FreeGroup.toWord_of_pow, invRev_replicate]
    have h3 : (-n).toNat = n.natAbs := by omega
    rw [h3, if_neg (by omega : ¬ (0 < n))]
    rfl
  · subst h; simp
  · conv_lhs => rw [← Int.toNat_of_nonneg (le_of_lt h), zpow_natCast]
    rw [FreeGroup.toWord_of_pow, if_pos h]
    have h3 : n.natAbs = n.toNat := by omega
    rw [h3]

/-- The reduced word of the inverse of an integral power of a generator. -/
theorem inv_zpow_toWord (a : α) (n : ℤ) :
    (((FreeGroup.of a) ^ n)⁻¹).toWord =
      List.replicate n.natAbs (a, if 0 < n then false else true) := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [show ((FreeGroup.of a) ^ n)⁻¹ = (FreeGroup.of a) ^ (-n) from (zpow_neg _ n).symm,
      zpow_toWord, Int.natAbs_neg, if_pos (by omega : 0 < -n), if_neg (by omega : ¬ (0 < n))]
  · subst h; simp
  · rw [show ((FreeGroup.of a) ^ n)⁻¹ = (FreeGroup.of a) ^ (-n) from (zpow_neg _ n).symm,
      zpow_toWord, Int.natAbs_neg, if_neg (by omega : ¬ (0 < -n)), if_pos h]

/-- A single block is the reduced word of the image of the corresponding letter under `powSubst`. -/
theorem mk_powSubstBlock (t : α) (p : ℤ) (c : α × Bool) :
    FreeGroup.mk (powSubstBlock t p c) =
      cond c.2 (powSubstFun t p c.1) ((powSubstFun t p c.1)⁻¹) := by
  obtain ⟨a, b⟩ := c
  cases b
  · by_cases h : a = t
    · rw [← h]
      rw [show powSubstBlock a p (a, false) = ((FreeGroup.of a ^ p)⁻¹).toWord by
            rw [inv_zpow_toWord]
            simp [powSubstBlock, powSubstBlockLen, powSubstBlockLetter]]
      rw [FreeGroup.mk_toWord]
      simp [powSubstFun]
    · rw [show powSubstBlock t p (a, false) = [(a, false)] by
            simp [powSubstBlock, powSubstBlockLen, powSubstBlockLetter, h]]
      rw [show FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ by
            rw [FreeGroup.of, FreeGroup.inv_mk]; rfl]
      simp [powSubstFun, h]
  · by_cases h : a = t
    · rw [← h]
      rw [show powSubstBlock a p (a, true) = ((FreeGroup.of a ^ p)).toWord by
            rw [zpow_toWord]
            simp [powSubstBlock, powSubstBlockLen, powSubstBlockLetter]]
      rw [FreeGroup.mk_toWord]
      simp [powSubstFun]
    · rw [show powSubstBlock t p (a, true) = [(a, true)] by
            simp [powSubstBlock, powSubstBlockLen, powSubstBlockLetter, h]]
      rw [show FreeGroup.mk [(a, true)] = FreeGroup.of a from rfl]
      simp [powSubstFun, h]

/-- Concatenating the reduced words of `mk`-images of a list of words. -/
private theorem prod_map_mk (L : List (List (α × Bool))) :
    (L.map FreeGroup.mk).prod = FreeGroup.mk (L.flatten) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    rw [List.map_cons, List.prod_cons, ih, FreeGroup.mul_mk, List.flatten_cons]

/-- The word-level form of the substitution: the blocks of the letters of `L` concatenate to the
substitute of `mk L`. -/
theorem powSubst_mk (t : α) (p : ℤ) (L : List (α × Bool)) :
    powSubst t p (FreeGroup.mk L) = FreeGroup.mk ((L.map (powSubstBlock t p)).flatten) := by
  rw [powSubst, FreeGroup.lift_mk]
  have hmap : (L.map fun x => cond x.2 (powSubstFun t p x.1) ((powSubstFun t p x.1)⁻¹))
      = L.map (fun c => FreeGroup.mk (powSubstBlock t p c)) :=
    List.map_congr_left (fun c _ => (mk_powSubstBlock t p c).symm)
  rw [hmap]
  have hcomp : (L.map (fun c => FreeGroup.mk (powSubstBlock t p c)))
      = (L.map (powSubstBlock t p)).map FreeGroup.mk := by
    rw [List.map_map]; rfl
  rw [hcomp]
  exact prod_map_mk (L.map (powSubstBlock t p))

/-- The concatenation of the blocks of a nonempty word is nonempty. -/
private theorem flatten_ne_nil (t : α) (p : ℤ) (hp : p ≠ 0) {L : List (α × Bool)}
    (hL : L ≠ []) : (L.map (powSubstBlock t p)).flatten ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c L =>
    rw [List.map_cons, List.flatten_cons]
    exact List.append_ne_nil_of_left_ne_nil (powSubstBlock_ne_nil t p hp c) _

/-- The first letter of the concatenation of the blocks is the first block's letter. -/
theorem head_flatten_powSubstBlock (t : α) (p : ℤ) (hp : p ≠ 0) (L : List (α × Bool)) :
    ((L.map (powSubstBlock t p)).flatten).head? =
      L.head?.map (powSubstBlockLetter t p) := by
  cases L with
  | nil => rfl
  | cons c L =>
    rw [List.map_cons, List.flatten_cons,
      List.head?_append_of_ne_nil (powSubstBlock t p c) (powSubstBlock_ne_nil t p hp c),
      head?_powSubstBlock t p hp c]
    rfl

/-- The last letter of the concatenation of the blocks is the last block's letter. -/
theorem getLast_flatten_powSubstBlock (t : α) (p : ℤ) (hp : p ≠ 0) (L : List (α × Bool)) :
    ((L.map (powSubstBlock t p)).flatten).getLast? =
      L.getLast?.map (powSubstBlockLetter t p) := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    cases L with
    | nil =>
      rw [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
        getLast?_powSubstBlock t p hp c]
      rfl
    | cons c' L' =>
      rw [List.map_cons, List.flatten_cons,
        List.getLast?_append_of_ne_nil _ (flatten_ne_nil t p hp (L := c' :: L') (by simp)), ih,
        List.getLast?_cons_cons]

/-- The concatenation of the blocks of a reduced word is reduced. -/
theorem powSubstBlock_flatten_isReduced (t : α) (p : ℤ) (hp : p ≠ 0)
    {L : List (α × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced ((L.map (powSubstBlock t p)).flatten) := by
  rw [FreeGroup.IsReduced] at hL ⊢
  have hnil : [] ∉ L.map (powSubstBlock t p) := by
    intro hmem
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
    exact powSubstBlock_ne_nil t p hp c hc
  rw [List.isChain_flatten hnil]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
    exact powSubstBlock_isReduced t p c
  · refine List.isChain_map_of_isChain (powSubstBlock t p) ?_ hL
    intro c₁ c₂ hQ u hu v hv
    have hn1 : powSubstBlockLen t p c₁ ≠ 0 := Nat.ne_of_gt (powSubstBlockLen_pos t p hp c₁)
    have hn2 : powSubstBlockLen t p c₂ ≠ 0 := Nat.ne_of_gt (powSubstBlockLen_pos t p hp c₂)
    rw [powSubstBlock_eq, List.getLast?_replicate, if_neg hn1] at hu
    rw [powSubstBlock_eq, List.head?_replicate, if_neg hn2] at hv
    simp only [Option.mem_some_iff] at hu hv
    subst hu; subst hv
    exact powSubstBlockLetter_rel t p c₁ c₂ hQ

/-- The concatenation of the blocks of a cyclically reduced word is cyclically reduced. -/
theorem flatten_isCyclicallyReduced (t : α) (p : ℤ) (hp : p ≠ 0) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) (hcyc : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced ((L.map (powSubstBlock t p)).flatten) := by
  rw [FreeGroup.isCyclicallyReduced_iff]
  refine ⟨powSubstBlock_flatten_isReduced t p hp hL, ?_⟩
  intro a ha b hb hcon
  rw [getLast_flatten_powSubstBlock t p hp L] at ha
  rw [head_flatten_powSubstBlock t p hp L] at hb
  rw [Option.mem_map] at ha hb
  obtain ⟨c, hc, hca⟩ := ha
  obtain ⟨c', hc', hc'a⟩ := hb
  subst hca; subst hc'a
  have hcc : c.1 = c'.1 :=
    (fst_powSubstBlockLetter t p c).symm.trans (hcon.trans (fst_powSubstBlockLetter t p c'))
  have hc2 : c.2 = c'.2 := hcyc.2 c hc c' hc' hcc
  exact congrArg Prod.snd (powSubstBlockLetter_eq_of t p hcc hc2)

end Support

theorem isCyclicallyReduced_powSubst {α : Type*} [DecidableEq α] (t : α) (p : ℤ) (hp : p ≠ 0) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) (hcyc : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (Work.OROneRel.powSubst t p (FreeGroup.mk L)).toWord := by
  rw [powSubst_mk t p L, FreeGroup.toWord_mk,
    FreeGroup.IsReduced.reduce_eq (powSubstBlock_flatten_isReduced t p hp hL)]
  exact flatten_isCyclicallyReduced t p hp hL hcyc

end Work.OROneRel
