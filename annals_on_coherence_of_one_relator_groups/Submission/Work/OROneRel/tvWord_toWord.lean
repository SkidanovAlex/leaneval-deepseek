import Mathlib
import Submission.Work.OROneRel.transvectionNielsenDefs

namespace Work.OROneRel

/-!
# `toWord` of the transvection image `(x * y ^ m) ^ p * y ^ q`

This file computes the reduced word of the element
`(of 0 * of 1 ^ m) ^ p * of 1 ^ q` of the free group on two generators.  For `m < 0` and
`0 ≤ m + q` this word is the explicit reduced list `tvWord p q m` of
`transvectionNielsenDefs`.

The proof is split into two independent halves:

* `isReduced_tvWord_aux` : the list `tvWord p q m` is reduced (so its maximal reduction is
  itself);
* `mk_tvWord_aux` : the list `tvWord p q m` represents the group element in question.

`FreeGroup.toWord` of the element is the maximal reduction of any word representing it, so the
two halves together give the result.
-/

/-! ## The list `tvWord p q m` is reduced -/

/-- The word `x :: replicate k x` is its own maximal reduction. -/
private lemma reduce_replicate_cons (x : Fin 2 × Bool) (k : ℕ) :
    FreeGroup.reduce (x :: List.replicate k x) = x :: List.replicate k x := by
  rw [← List.replicate_succ, FreeGroup.reduce_replicate, List.replicate_succ]

/-- A `(0,true)`-letter followed by a run of `(1,b)`-letters (for any sign `b`) is a reduced
word: the first junction joins different generators, and inside the run the letters are equal. -/
private lemma isReduced_zero_true_cons_replicate (n : ℕ) (b : Bool) :
    FreeGroup.IsReduced (((0 : Fin 2), true) :: List.replicate n ((1 : Fin 2), b)) := by
  rw [FreeGroup.isReduced_iff_reduce_eq]
  cases n with
  | zero => rfl
  | succ k =>
    rw [List.replicate_succ, FreeGroup.reduce.cons, reduce_replicate_cons ((1 : Fin 2), b) k]
    simp

/-- The block `tvBlk m` is a reduced word. -/
private lemma isReduced_tvBlk (m : ℤ) : FreeGroup.IsReduced (tvBlk m) := by
  rw [tvBlk]
  exact isReduced_zero_true_cons_replicate m.natAbs false

/-- The first letter of the block `tvBlk m`. -/
private lemma tvBlk_head (m : ℤ) :
    (tvBlk m).head? = some ((0 : Fin 2), true) := by
  rw [tvBlk]
  rfl

/-- The last letter of the block `tvBlk m`, for `m < 0`. -/
private lemma tvBlk_getLast (m : ℤ) (hm : m < 0) :
    (tvBlk m).getLast? = some ((1 : Fin 2), false) := by
  have hpos : m.natAbs ≠ 0 := ne_of_gt (Int.natAbs_pos.mpr (ne_of_lt hm))
  rw [tvBlk,
    List.getLast?_cons_of_ne_nil (by simpa [List.replicate_eq_nil_iff] using hpos),
    List.getLast?_replicate, if_neg hpos]

/-- The block `tvBlk m` is cyclically reduced when `m < 0`: it starts with the generator `0` and
ends with the generator `1`. -/
private lemma isCyclicallyReduced_tvBlk (m : ℤ) (hm : m < 0) :
    FreeGroup.IsCyclicallyReduced (tvBlk m) := by
  refine ⟨isReduced_tvBlk m, ?_⟩
  intro a ha b hb hab
  rw [tvBlk_getLast m hm] at ha
  simp only [Option.mem_some_iff] at ha
  rw [tvBlk_head] at hb
  simp only [Option.mem_some_iff] at hb
  subst ha
  subst hb
  exact absurd hab (by decide)

/-- If `B` is cyclically reduced and `B ++ L` is reduced, then inserting any number of copies of
`B` at the front of `L` keeps the word reduced.  This is `FreeGroup.IsReduced.append_flatten_replicate_append`
with `L₁ = []`, stated in the form needed below. -/
private lemma isReduced_flatten_replicate_append {B L : List (Fin 2 × Bool)}
    (hBcyc : FreeGroup.IsCyclicallyReduced B) (hBL : FreeGroup.IsReduced (B ++ L)) :
    ∀ n : ℕ, FreeGroup.IsReduced ((List.replicate n B).flatten ++ L)
  | 0 => (List.isChain_append.mp hBL).2.1
  | n + 1 =>
    FreeGroup.IsReduced.append_flatten_replicate_append (L₂ := B) (L₁ := []) (L₃ := L)
      (n := n + 1) hBcyc hBL (by simp)

/-- The explicit word `tvWord p q m` is reduced. -/
private lemma isReduced_tvWord_aux (p q : ℕ) (m : ℤ) (hm : m < 0) :
    FreeGroup.IsReduced (tvWord p q m) := by
  have hBcyc : FreeGroup.IsCyclicallyReduced (tvBlk m) := isCyclicallyReduced_tvBlk m hm
  have hCD : FreeGroup.IsReduced
      (((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true)) :=
    isReduced_zero_true_cons_replicate _ true
  have hBL : FreeGroup.IsReduced
      (tvBlk m ++ (((0 : Fin 2), true) ::
        List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true))) := by
    refine List.IsChain.append (isReduced_tvBlk m) hCD ?_
    intro x hx y hy hxy
    rw [tvBlk_getLast m hm] at hx
    simp only [Option.mem_some_iff] at hx
    subst hx
    rw [List.head?_cons] at hy
    simp only [Option.mem_some_iff] at hy
    subst hy
    exact absurd hxy (by decide)
  exact isReduced_flatten_replicate_append hBcyc hBL (p - 1)

/-! ## `tvWord p q m` represents `(of 0 * of 1 ^ m) ^ p * of 1 ^ q` -/

/-- A run of positive letters: `mk ((a,true) ^ n) = (of a) ^ n`. -/
private lemma mk_repl_true (a : Fin 2) (n : ℕ) :
    FreeGroup.mk (List.replicate n (a, true)) = (FreeGroup.of a) ^ n := by
  rw [← List.flatten_replicate_singleton (n := n) (a := (a, true)), ← FreeGroup.pow_mk]
  rfl

/-- A run of negative letters: `mk ((a,false) ^ n) = (of a) ^ (-n)`. -/
private lemma mk_repl_false (a : Fin 2) (n : ℕ) :
    FreeGroup.mk (List.replicate n (a, false)) = (FreeGroup.of a) ^ (-(n : ℤ)) := by
  rw [← List.flatten_replicate_singleton (n := n) (a := (a, false)), ← FreeGroup.pow_mk]
  rw [show FreeGroup.mk ([(a, false)] : List (Fin 2 × Bool)) = (FreeGroup.of a)⁻¹ from by
        rw [FreeGroup.of]
        exact (FreeGroup.inv_mk (L := [(a, true)])).symm]
  rw [inv_pow, zpow_neg, zpow_natCast]

/-- The block `tvBlk m` represents `of 0 * of 1 ^ m` for `m < 0`. -/
private lemma mk_tvBlk (m : ℤ) (hm : m < 0) :
    FreeGroup.mk (tvBlk m) = FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m := by
  rw [tvBlk]
  change FreeGroup.mk ([((0 : Fin 2), true)] ++ List.replicate m.natAbs ((1 : Fin 2), false))
      = FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m
  rw [← FreeGroup.mul_mk, mk_repl_false,
    Int.ofNat_natAbs_of_nonpos (le_of_lt hm), neg_neg]
  rfl

/-- A pure group-theoretic identity in an arbitrary group. -/
private lemma group_identity {G : Type*} [Group G] (x y : G) (p q : ℕ) (m : ℤ) (hp : 1 ≤ p) :
    ((x * y ^ m) ^ (p - 1) * x) * y ^ (m + (q : ℤ)) = (x * y ^ m) ^ p * y ^ q := by
  have hpow : (x * y ^ m) ^ p = (x * y ^ m) ^ (p - 1 + 1) := by
    rw [Nat.sub_add_cancel hp]
  rw [hpow, pow_succ, zpow_add, zpow_natCast]
  simp only [mul_assoc]

/-- The list `tvWord p q m` represents `(of 0 * of 1 ^ m) ^ p * of 1 ^ q`. -/
private lemma mk_tvWord_aux (p q : ℕ) (m : ℤ) (hp : 1 ≤ p) (hm : m < 0)
    (hmq : 0 ≤ m + (q : ℤ)) :
    FreeGroup.mk (tvWord p q m)
      = (FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m) ^ p
        * FreeGroup.of (1 : Fin 2) ^ q := by
  rw [tvWord]
  rw [show ((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true)
        = [((0 : Fin 2), true)]
          ++ List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true) from rfl]
  rw [← List.append_assoc, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  rw [← FreeGroup.pow_mk, mk_repl_true, mk_tvBlk m hm]
  rw [show FreeGroup.mk ([((0 : Fin 2), true)] : List (Fin 2 × Bool))
        = FreeGroup.of (0 : Fin 2) from rfl]
  rw [show (FreeGroup.of (1 : Fin 2)) ^ (m + (q : ℤ)).toNat
        = (FreeGroup.of (1 : Fin 2)) ^ (m + (q : ℤ)) from by
      rw [← zpow_natCast, Int.toNat_of_nonneg hmq]]
  exact group_identity (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2)) p q m hp

/-! ## The main statement -/

theorem tvWord_toWord (p q : ℕ) (m : ℤ) (hp : 1 ≤ p) (hm : m < 0) (hmq : 0 ≤ m + (q : ℤ)) :
    FreeGroup.toWord
      ((FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m) ^ p * FreeGroup.of (1 : Fin 2) ^ q)
      = Work.OROneRel.tvWord p q m := by
  have hred := isReduced_tvWord_aux p q m hm
  have hmk := mk_tvWord_aux p q m hp hm hmq
  calc FreeGroup.toWord
        ((FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m) ^ p
          * FreeGroup.of (1 : Fin 2) ^ q)
      = FreeGroup.toWord (FreeGroup.mk (Work.OROneRel.tvWord p q m)) := by rw [hmk]
    _ = FreeGroup.reduce (Work.OROneRel.tvWord p q m) := FreeGroup.toWord_mk
    _ = Work.OROneRel.tvWord p q m := (FreeGroup.isReduced_iff_reduce_eq).mp hred

end Work.OROneRel
