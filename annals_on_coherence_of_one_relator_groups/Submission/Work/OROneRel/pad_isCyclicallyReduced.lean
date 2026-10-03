import Mathlib
import Submission.Work.OROneRel.padDefs

/-!
# The padded relator is cyclically reduced

Given a relator `r : FreeGroup α` whose reduced word is cyclically reduced, and padding exponents
`c : α → ℤ`, we show that the padded relator `padRel c r` is again cyclically reduced.

The reason is that the padding `a ↦ a z ^ (c a) a` replaces every letter `a` of the reduced word of
`r` by a *block* which is reduced, begins and ends with the letter `a` itself, and whose interior
letters are the fresh letter `z`.  Hence concatenating the blocks of a reduced word never cancels,
so the padded word is reduced; and the first and last letter of the padded word are the images of
the first and last letter of the reduced word of `r`, so no cyclic cancellation occurs either.

The two ingredients are made precise as

* `pcr_padList_isReduced`: the list of blocks of a reduced word is reduced;
* `pcr_mk_padList`: the product of the blocks of a word is the padding of the word.

The key trick that avoids computing the first and last letters of a list of blocks explicitly is
that a (nonempty) list `L` is cyclically reduced exactly when `L ++ L` is reduced
(`FreeGroup.IsCyclicallyReduced L ↔ FreeGroup.IsReduced (L ++ L)`, both arising from
`List.isChain_append` with the two copies of `L`).

The files `padBlock_eq_true`, `padBlock_eq_false` give the explicit form of a single block, and
`isReduced_some_cons_replicate_append` the reducedness of a list of that shape.  For independence,
that computation is reproduced here in the local lemmas `pcr_padBlock_eq_true` /
`pcr_padBlock_eq_false` / `pcr_isReduced_some_cons_replicate_append`, so that this file rests only
on `padDefs` and Mathlib.
-/

universe u

namespace Work.OROneRel

open FreeGroup

variable {α : Type u}

/-! ### The explicit form of a single block

This is a self-contained computation: the reduced word of `of x * z ^ m * of x` for two distinct
generators `x ≠ z` is `(x,true) :: z^|m| :: [(x,true)]`, because the outer letters cannot cancel
with the power of the middle letter. -/

lemma pcr_mk_replicate_true {β : Type*} (b : β) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, true)) = (FreeGroup.of b) ^ n := by
  induction n with
  | zero => exact (FreeGroup.one_eq_mk).symm
  | succ n ih =>
    rw [List.replicate_succ, ← List.singleton_append, ← FreeGroup.mul_mk,
      show FreeGroup.mk [(b, true)] = FreeGroup.of b from rfl, ih, pow_succ']

lemma pcr_mk_replicate_false {β : Type*} (b : β) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, false)) = ((FreeGroup.of b) ^ n)⁻¹ := by
  have h : List.replicate n (b, false) = FreeGroup.invRev (List.replicate n (b, true)) := by
    simp [FreeGroup.invRev, List.map_replicate]
  rw [h, ← FreeGroup.inv_mk, pcr_mk_replicate_true]

lemma pcr_mk_replicate_cond {β : Type*} (b : β) (d : Bool) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, d)) =
      (cond d (FreeGroup.of b) ((FreeGroup.of b)⁻¹)) ^ n := by
  cases d
  · show FreeGroup.mk (List.replicate n (b, false)) = ((FreeGroup.of b)⁻¹) ^ n
    rw [pcr_mk_replicate_false, inv_pow]
  · show FreeGroup.mk (List.replicate n (b, true)) = (FreeGroup.of b) ^ n
    rw [pcr_mk_replicate_true]

/-- In a group, the `|m|`-th power of `g` or of `g⁻¹` according to the sign of `m` is `g ^ m`. -/
lemma pcr_cond_pow_natAbs_eq_zpow {G : Type*} [Group G] (g : G) (m : ℤ) :
    (cond (decide (0 < m)) g g⁻¹) ^ m.natAbs = g ^ m := by
  rcases lt_trichotomy (0 : ℤ) m with h | h | h
  · have hd : decide (0 < m) = true := decide_eq_true h
    rw [hd]
    show g ^ m.natAbs = g ^ m
    rw [← zpow_natCast, Int.natAbs_of_nonneg h.le]
  · subst h
    simp
  · have hd : decide (0 < m) = false := decide_eq_false (not_lt.mpr h.le)
    rw [hd]
    show (g⁻¹) ^ m.natAbs = g ^ m
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    rw [Int.ofNat_natAbs_of_nonpos h.le]
    ring

lemma pcr_isReduced_replicate_append_singleton {β : Type*} (u v : β × Bool)
    (h : u.1 ≠ v.1) (n : ℕ) : FreeGroup.IsReduced (List.replicate n u ++ [v]) := by
  rw [FreeGroup.IsReduced, List.isChain_append]
  refine ⟨List.isChain_replicate_of_rel n (fun _ => rfl), List.isChain_singleton v, ?_⟩
  intro a ha b hb
  rw [List.head?_singleton] at hb
  rw [List.getLast?_replicate] at ha
  by_cases hn : n = 0
  · rw [if_pos hn] at ha
    exact absurd ha (Option.not_mem_none a)
  · rw [if_neg hn] at ha
    obtain hbv : v = b := Option.mem_some_iff.mp hb
    obtain hau : u = a := Option.mem_some_iff.mp ha
    subst hbv
    subst hau
    intro huv
    exact absurd huv h

lemma pcr_isReduced_cons_replicate_append_singleton {β : Type*} (u v : β × Bool)
    (h : v.1 ≠ u.1) (n : ℕ) : FreeGroup.IsReduced (v :: (List.replicate n u ++ [v])) := by
  refine List.IsChain.cons (pcr_isReduced_replicate_append_singleton u v (Ne.symm h) n) ?_
  intro y hy
  rw [List.head?_append, List.head?_replicate, List.head?_singleton] at hy
  by_cases hn : n = 0
  · rw [if_pos hn, Option.none_or] at hy
    obtain hyv : v = y := Option.mem_some_iff.mp hy
    subst hyv
    intro _
    rfl
  · rw [if_neg hn, Option.some_or] at hy
    obtain hyu : u = y := Option.mem_some_iff.mp hy
    subst hyu
    intro hvu
    exact absurd hvu h

/-- **Reducedness of a block-shaped word**: `(x,b) :: (w ^ n) ++ [(x,b)]` with all interior letters
equal to `(w, t)` and a first component different from `x`. -/
theorem pcr_isReduced_some_cons_replicate_append {β : Type*} (x : β) (b t : Bool) (m : ℕ) :
    FreeGroup.IsReduced ((some x, b) ::
      (List.replicate m (((none : Option β)), t) ++ [(some x, b)])) :=
  pcr_isReduced_cons_replicate_append_singleton ((none : Option β), t) (some x, b) (by simp) m

/-- The explicit form of the block of a letter. -/
theorem pcr_padBlock_eq_true (c : α → ℤ) (a : α) :
    padBlock c (a, true) =
      (some a, true) :: (List.replicate ((c a).natAbs) (((none : PadT α)), decide (0 < c a)) ++
        [(some a, true)]) := by
  classical
  have hred : FreeGroup.IsReduced
      ((some a, true) :: (List.replicate ((c a).natAbs) ((none : PadT α), decide (0 < c a)) ++
        [(some a, true)])) :=
    pcr_isReduced_some_cons_replicate_append a true (decide (0 < c a)) ((c a).natAbs)
  have hmk : FreeGroup.mk
        ((some a, true) ::
          (List.replicate ((c a).natAbs) ((none : PadT α), decide (0 < c a)) ++ [(some a, true)])) =
      padGen c a := by
    rw [show (some a, true) ::
          (List.replicate ((c a).natAbs) ((none : PadT α), decide (0 < c a)) ++ [(some a, true)]) =
        [(some a, true)] ++
          (List.replicate ((c a).natAbs) ((none : PadT α), decide (0 < c a)) ++ [(some a, true)])
      from rfl]
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    rw [show FreeGroup.mk [(some a, true)] = FreeGroup.of (some a) from rfl,
      pcr_mk_replicate_cond, pcr_cond_pow_natAbs_eq_zpow, padGen, mul_assoc]
  rw [show padBlock c (a, true) = (padGen c a).toWord from rfl, ← hmk, FreeGroup.toWord_mk]
  exact hred.reduce_eq

/-! ### Elementary properties of a single block -/

/-- The block of an inverse-letter is the `invRev` of the block of the letter. -/
theorem pcr_padBlock_false_eq_invRev (c : α → ℤ) (a : α) :
    padBlock c (a, false) = FreeGroup.invRev (padBlock c (a, true)) := by
  classical
  show ((padGen c a)⁻¹).toWord = FreeGroup.invRev ((padGen c a).toWord)
  rw [FreeGroup.toWord_inv]

/-- `invRev` of a block-shaped word. -/
theorem pcr_invRev_block {β : Type*} (x : β) (t : Bool) (m : ℕ) :
    FreeGroup.invRev ((some x, true) :: (List.replicate m (((none : Option β)), t) ++
        [(some x, true)])) =
      (some x, false) :: (List.replicate m (((none : Option β)), !t) ++ [(some x, false)]) := by
  simp [FreeGroup.invRev]

/-- The explicit form of the block of an inverse-letter. -/
theorem pcr_padBlock_eq_false (c : α → ℤ) (a : α) :
    padBlock c (a, false) =
      (some a, false) :: (List.replicate ((c a).natAbs) (((none : PadT α)), !(decide (0 < c a))) ++
        [(some a, false)]) := by
  rw [pcr_padBlock_false_eq_invRev, pcr_padBlock_eq_true]
  exact pcr_invRev_block a (decide (0 < c a)) ((c a).natAbs)

theorem pcr_padBlock_ne_nil (c : α → ℤ) (p : α × Bool) : padBlock c p ≠ [] := by
  obtain ⟨a, b⟩ := p
  cases b
  · rw [pcr_padBlock_eq_false]; simp
  · rw [pcr_padBlock_eq_true]; simp

theorem pcr_padBlock_head (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).head? = some (some p.1, p.2) := by
  obtain ⟨a, b⟩ := p
  cases b
  · rw [pcr_padBlock_eq_false]; simp
  · rw [pcr_padBlock_eq_true]; simp

/-- The last letter of a list `x :: (W ++ [x])` is `x`. -/
theorem pcr_getLast?_cons_append_self {β : Type*} (x : β × Bool) (W : List (β × Bool)) :
    (x :: (W ++ [x])).getLast? = some x := by
  rw [List.getLast?_cons, List.getLast?_concat]
  simp

theorem pcr_padBlock_getLast (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).getLast? = some (some p.1, p.2) := by
  obtain ⟨a, b⟩ := p
  cases b
  · rw [pcr_padBlock_eq_false]; exact pcr_getLast?_cons_append_self _ _
  · rw [pcr_padBlock_eq_true]; exact pcr_getLast?_cons_append_self _ _

theorem pcr_padBlock_isReduced (c : α → ℤ) (p : α × Bool) :
    FreeGroup.IsReduced (padBlock c p) := by
  obtain ⟨a, b⟩ := p
  cases b
  · rw [pcr_padBlock_eq_false]
    exact pcr_isReduced_some_cons_replicate_append a false _ _
  · rw [pcr_padBlock_eq_true]
    exact pcr_isReduced_some_cons_replicate_append a true _ _

/-! ### The list of blocks -/

theorem pcr_padList_append (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    padList c (L₁ ++ L₂) = padList c L₁ ++ padList c L₂ := by
  simp [padList, List.map_append, List.flatten_append]

theorem pcr_padList_cons (c : α → ℤ) (p : α × Bool) (L : List (α × Bool)) :
    padList c (p :: L) = padBlock c p ++ padList c L := by
  simp [padList]

/-- **The blocks of a reduced word concatenate without cancellation.** -/
theorem pcr_padList_isReduced (c : α → ℤ) {L : List (α × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (padList c L) := by
  classical
  have hne : ([] : List (PadT α × Bool)) ∉ L.map (padBlock c) := by
    intro h
    obtain ⟨p, -, hp⟩ := List.mem_map.mp h
    exact pcr_padBlock_ne_nil c p hp
  rw [padList, FreeGroup.IsReduced, List.isChain_flatten hne]
  refine ⟨?_, ?_⟩
  · rintro l hl
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
    exact pcr_padBlock_isReduced c p
  · refine List.isChain_map_of_isChain (f := padBlock c) ?_ hL
    intro p q hpq x hx y hy
    rw [pcr_padBlock_getLast] at hx
    rw [pcr_padBlock_head] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    rw [← hx, ← hy]
    exact fun h => hpq (by simpa using h)

/-! ### The product of the blocks -/

theorem pcr_mk_pair_true (a : α) :
    FreeGroup.mk [(a, true)] = (FreeGroup.of a : FreeGroup α) := rfl

theorem pcr_mk_pair_false (a : α) : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  show FreeGroup.mk [(a, false)] = (FreeGroup.mk [(a, true)])⁻¹
  rw [FreeGroup.inv_mk,
    show FreeGroup.invRev [(a, true)] = [(a, false)] from by simp [FreeGroup.invRev]]

/-- The product of one block is the corresponding image of a single generator. -/
theorem pcr_mk_padBlock (c : α → ℤ) (a : α) (b : Bool) :
    FreeGroup.mk (padBlock c (a, b)) =
      (if b then padGen c a else (padGen c a)⁻¹ : FreeGroup (PadT α)) := by
  classical
  cases b
  · show FreeGroup.mk (padBlock c (a, false)) = (padGen c a)⁻¹
    exact FreeGroup.mk_toWord (x := (padGen c a)⁻¹)
  · show FreeGroup.mk (padBlock c (a, true)) = padGen c a
    exact FreeGroup.mk_toWord (x := padGen c a)

theorem pcr_padHom_pair_true (c : α → ℤ) (a : α) :
    padHom c (FreeGroup.mk [(a, true)]) = FreeGroup.mk (padBlock c (a, true)) := by
  rw [pcr_mk_pair_true, pcr_mk_padBlock, padHom_of, if_pos rfl]

theorem pcr_padHom_pair_false (c : α → ℤ) (a : α) :
    padHom c (FreeGroup.mk [(a, false)]) = FreeGroup.mk (padBlock c (a, false)) := by
  rw [pcr_mk_pair_false, pcr_mk_padBlock, _root_.map_inv, padHom_of, if_neg (by simp)]

/-- **The product of the blocks of a word is the padding of the word.** -/
theorem pcr_mk_padList (c : α → ℤ) (L : List (α × Bool)) :
    FreeGroup.mk (padList c L) = padHom c (FreeGroup.mk L) := by
  classical
  induction L with
  | nil =>
    show FreeGroup.mk ([] : List (PadT α × Bool)) =
      padHom c (FreeGroup.mk ([] : List (α × Bool)))
    rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl, (padHom c).map_one]
    exact (FreeGroup.one_eq_mk).symm
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [pcr_padList_cons, ← FreeGroup.mul_mk]
    rw [show FreeGroup.mk ((a, b) :: L) = FreeGroup.mk [(a, b)] * FreeGroup.mk L from rfl,
      _root_.map_mul]
    cases b
    · rw [pcr_padHom_pair_false, ← ih]
    · rw [pcr_padHom_pair_true, ← ih]

/-- **The reduced word of the padded relator is the list of blocks of the reduced word of the
relator** — the `toWord_padHom` of the padding sub-project.

The `DecidableEq` instances are *explicit* arguments here on purpose: `FreeGroup.toWord` takes its
`DecidableEq` instance as an argument, and inside `IsCyclicallyReducedRelator` / `relatorNorm` it is
instantiated with the `Classical` instance, which is not the instance that type class search would
find for `Option α`.  Making the instances explicit keeps the two sides of the equation in the same
instance. -/
theorem pcr_pad_isCyclicallyReduced {α : Type u} (c : α → ℤ) (I : DecidableEq α)
    (J : DecidableEq (PadT α)) {r : FreeGroup α}
    (h : FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α I r)) :
    FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord (PadT α) J (padHom c r)) := by
  rw [FreeGroup.isCyclicallyReduced_iff] at h ⊢
  have hL : FreeGroup.IsReduced (@FreeGroup.toWord α I r ++ @FreeGroup.toWord α I r) :=
    List.isChain_append.2 ⟨h.1, h.1, h.2⟩
  have hW : FreeGroup.IsReduced (padList c (@FreeGroup.toWord α I r ++ @FreeGroup.toWord α I r)) :=
    pcr_padList_isReduced c hL
  rw [pcr_padList_append] at hW
  have hred : FreeGroup.IsReduced (padList c (@FreeGroup.toWord α I r)) :=
    List.IsChain.left_of_append hW
  have hcyc : ∀ a ∈ (padList c (@FreeGroup.toWord α I r)).getLast?,
      ∀ b ∈ (padList c (@FreeGroup.toWord α I r)).head?, a.1 = b.1 → a.2 = b.2 :=
    (List.isChain_append.1 hW).2.2
  have hmk : FreeGroup.mk (padList c (@FreeGroup.toWord α I r)) = padHom c r := by
    rw [pcr_mk_padList]
    exact congrArg (padHom c) (@FreeGroup.mk_toWord α I r)
  have htw : @FreeGroup.toWord (PadT α) J (padHom c r) =
      padList c (@FreeGroup.toWord α I r) := by
    rw [← hmk, @FreeGroup.toWord_mk (PadT α) (padList c (@FreeGroup.toWord α I r)) J,
      @FreeGroup.IsReduced.reduce_eq (PadT α) (padList c (@FreeGroup.toWord α I r)) J hred]
  rw [htw]
  exact ⟨hred, hcyc⟩

theorem pad_isCyclicallyReduced {α : Type u} (c : α → ℤ) {r : FreeGroup α}
    (h : Work.OROneRel.IsCyclicallyReducedRelator r) :
    Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.padRel c r) := by
  unfold IsCyclicallyReducedRelator at h ⊢
  rw [show Work.OROneRel.padRel c r = padHom c r from rfl]
  exact pcr_pad_isCyclicallyReduced c _ _ h

end Work.OROneRel
