/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The reduced length of the padding of a word

`padHom c : F α →* F (Option α)` sends the generator `a` to the block

`a * z ^ (c a) * a`      (`z` = `none` the fresh padding letter).

Every block begins and ends with its own letter `some a`, so the concatenation of the images of the
letters of a *reduced* word is again reduced: no cancellation can occur.  Hence the reduced length
of `padHom c u` is the sum of the lengths `2 + |c a|` of the blocks over the letters `a` of the
reduced word of `u` -- the statement proved below.

The proof decomposes as follows.

* `mk_flatten`, `mk_replicate_cond`, `cond_pow_natAbs_eq_zpow` compute `mk` of (a repetition of) a
  letter as a group power;
* `isReduced_replicate_append_singleton` / `isReduced_cons_replicate_append_singleton` show that a
  repeated letter followed by a further letter of a different generator is reduced;
* `toWord_padGen_general` identifies the reduced word of a block, and `invRev_...` handles the
  inverse orientation;
* `padBlock_eq` then gives the explicit shape of a padding block, from which its length, its first
  and last letter, and its reducedness follow;
* `mk_padList` shows that `mk` of a padded word is the padding of `mk`, and `padList_isReduced`
  shows that `padList c L` is reduced whenever `L` is;
* the main theorem is then `norm = length of toWord = length of padList = sum of block lengths`.
-/
import Mathlib
import Submission.Work.OROneRel.padDefs
import Submission.Work.OROneRel.weinbaumMonoDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Elementary computations with `FreeGroup.mk` -/

/-- `mk` of a flattened list of words is the product of the `mk`s of the words. -/
private lemma mk_flatten {β : Type*} (L : List (List (β × Bool))) :
    FreeGroup.mk (L.flatten) = (L.map FreeGroup.mk).prod := by
  induction L with
  | nil => rfl
  | cons l ls ih => rw [List.flatten_cons, List.map_cons, List.prod_cons, ← FreeGroup.mul_mk, ih]

/-- `mk` of a repetition of a positively oriented letter is a power. -/
private lemma mk_replicate_true {β : Type*} (b : β) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, true)) = (FreeGroup.of b) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, ← List.singleton_append, ← FreeGroup.mul_mk,
      show FreeGroup.mk [(b, true)] = FreeGroup.of b from rfl, ih, pow_succ']

/-- `mk` of a repetition of a negatively oriented letter is the inverse power. -/
private lemma mk_replicate_false {β : Type*} (b : β) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, false)) = ((FreeGroup.of b) ^ n)⁻¹ := by
  have h : List.replicate n (b, false) = FreeGroup.invRev (List.replicate n (b, true)) := by
    simp [FreeGroup.invRev, List.map_replicate]
  rw [h, ← FreeGroup.inv_mk, mk_replicate_true]

/-- `mk` of a repetition of a letter with prescribed orientation `d`. -/
private lemma mk_replicate_cond {β : Type*} (b : β) (d : Bool) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, d)) =
      (cond d (FreeGroup.of b) ((FreeGroup.of b)⁻¹)) ^ n := by
  cases d
  · show FreeGroup.mk (List.replicate n (b, false)) = ((FreeGroup.of b)⁻¹) ^ n
    rw [mk_replicate_false, inv_pow]
  · show FreeGroup.mk (List.replicate n (b, true)) = (FreeGroup.of b) ^ n
    rw [mk_replicate_true]

/-- In a group, the `|m|`-th power of `g` or of `g⁻¹` according to the sign of `m` is `g ^ m`. -/
private lemma cond_pow_natAbs_eq_zpow {G : Type*} [Group G] (g : G) (m : ℤ) :
    (cond (decide (0 ≤ m)) g g⁻¹) ^ m.natAbs = g ^ m := by
  by_cases h : 0 ≤ m
  · have hd : decide (0 ≤ m) = true := decide_eq_true h
    rw [hd]
    show g ^ m.natAbs = g ^ m
    rw [← zpow_natCast, Int.natAbs_of_nonneg h]
  · have hm : m < 0 := not_le.mp h
    have hd : decide (0 ≤ m) = false := decide_eq_false h
    rw [hd]
    show (g⁻¹) ^ m.natAbs = g ^ m
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hm)]
    ring

/-- Inverting and reversing a repetition flips the orientation of every letter. -/
private lemma invRev_replicate {β : Type*} (b : β) (d : Bool) (n : ℕ) :
    FreeGroup.invRev (List.replicate n (b, d)) = List.replicate n (b, !d) := by
  simp [FreeGroup.invRev, List.map_replicate]

/-! ### Reducedness of a repeated letter followed by a further letter -/

/-- A repeated letter followed by a letter with a different generator is reduced. -/
private lemma isReduced_replicate_append_singleton {β : Type*} (u v : β × Bool)
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

/-- The same, with the repeated letter preceded by the further letter. -/
private lemma isReduced_cons_replicate_append_singleton {β : Type*} (u v : β × Bool)
    (h : v.1 ≠ u.1) (n : ℕ) : FreeGroup.IsReduced (v :: (List.replicate n u ++ [v])) := by
  refine List.IsChain.cons (isReduced_replicate_append_singleton u v (Ne.symm h) n) ?_
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

/-! ### The reduced word of a single padding block -/

/-- The reduced word of `of x * (of z) ^ m * of x`, for two distinct generators `x ≠ z`. -/
private lemma toWord_padGen_general {β : Type*} [DecidableEq β] (x z : β) (m : ℤ) (h : x ≠ z) :
    (FreeGroup.of x * (FreeGroup.of z) ^ m * FreeGroup.of x).toWord =
      (x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)]) := by
  have hred : FreeGroup.IsReduced
      ((x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)])) :=
    isReduced_cons_replicate_append_singleton (z, decide (0 ≤ m)) (x, true)
      (by simpa using h) m.natAbs
  have hmk : FreeGroup.mk
        ((x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)])) =
      FreeGroup.of x * (FreeGroup.of z) ^ m * FreeGroup.of x := by
    rw [show (x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)]) =
        [(x, true)] ++ (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)]) from rfl]
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    rw [show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl, mk_replicate_cond,
      cond_pow_natAbs_eq_zpow, mul_assoc]
  rw [← hmk, FreeGroup.toWord_mk]
  exact hred.reduce_eq

/-- Inverting and reversing the reduced word of `of x * (of z)^m * of x`. -/
private lemma invRev_cons_replicate_cons {β : Type*} (x z : β) (d : Bool) (n : ℕ) :
    FreeGroup.invRev ((x, true) :: (List.replicate n (z, d) ++ [(x, true)])) =
      (x, false) :: (List.replicate n (z, !d) ++ [(x, false)]) := by
  rw [FreeGroup.invRev_cons, FreeGroup.invRev_append, invRev_replicate]
  simp [FreeGroup.invRev]

/-- The explicit shape of a padding block. -/
private lemma padBlock_eq (c : α → ℤ) (p : α × Bool) :
    padBlock c p =
      (some p.1, p.2) ::
        (List.replicate (c p.1).natAbs
            (none, cond p.2 (decide (0 ≤ c p.1)) (!(decide (0 ≤ c p.1)))) ++
          [(some p.1, p.2)]) := by
  classical
  obtain ⟨a, b⟩ := p
  cases b
  · show padBlock c (a, false) = (some a, false) ::
        (List.replicate (c a).natAbs (none, !(decide (0 ≤ c a))) ++ [(some a, false)])
    have h1 : padBlock c (a, false) = ((padGen c a)⁻¹).toWord := rfl
    rw [h1, FreeGroup.toWord_inv, padGen,
      toWord_padGen_general (some a) (none : PadT α) (c a) (by simp)]
    exact invRev_cons_replicate_cons (some a) (none : PadT α) (decide (0 ≤ c a)) (c a).natAbs
  · show padBlock c (a, true) = (some a, true) ::
        (List.replicate (c a).natAbs (none, decide (0 ≤ c a)) ++ [(some a, true)])
    have h1 : padBlock c (a, true) = (padGen c a).toWord := rfl
    rw [h1, padGen,
      toWord_padGen_general (some a) (none : PadT α) (c a) (by simp)]

/-! ### Basic properties of a padding block -/

/-- The length of a padding block. -/
private lemma padBlock_length (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).length = 2 + (c p.1).natAbs := by
  rw [padBlock_eq]
  simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
  omega

/-- The first letter of a padding block. -/
private lemma padBlock_head (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).head? = some (some p.1, p.2) := by
  rw [padBlock_eq, List.head?_cons]

/-- The last letter of a padding block. -/
private lemma padBlock_getLast (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).getLast? = some (some p.1, p.2) := by
  rw [padBlock_eq]
  rw [show (some p.1, p.2) ::
        (List.replicate (c p.1).natAbs
            (none, cond p.2 (decide (0 ≤ c p.1)) (!(decide (0 ≤ c p.1)))) ++
          [(some p.1, p.2)]) =
      ((some p.1, p.2) :: List.replicate (c p.1).natAbs
            (none, cond p.2 (decide (0 ≤ c p.1)) (!(decide (0 ≤ c p.1))))) ++
        [(some p.1, p.2)] from rfl]
  rw [List.getLast?_concat]

/-- A padding block is nonempty. -/
private lemma padBlock_ne_nil (c : α → ℤ) (p : α × Bool) : padBlock c p ≠ [] := by
  rw [padBlock_eq]
  simp

/-- A padding block is reduced. -/
private lemma padBlock_isReduced (c : α → ℤ) (p : α × Bool) :
    FreeGroup.IsReduced (padBlock c p) := by
  classical
  obtain ⟨a, b⟩ := p
  cases b
  · have h1 : padBlock c (a, false) = ((padGen c a)⁻¹).toWord := rfl
    rw [h1]
    exact FreeGroup.isReduced_toWord
  · have h1 : padBlock c (a, true) = (padGen c a).toWord := rfl
    rw [h1]
    exact FreeGroup.isReduced_toWord

/-! ### `mk` and the length of `padList` -/

/-- `mk` of a padding block is the corresponding padded generator. -/
private lemma mk_padBlock (c : α → ℤ) (p : α × Bool) :
    FreeGroup.mk (padBlock c p) =
      cond p.2 (padGen c p.1) ((padGen c p.1)⁻¹) := by
  classical
  obtain ⟨a, b⟩ := p
  cases b
  · show FreeGroup.mk (padBlock c (a, false)) = (padGen c a)⁻¹
    have h1 : padBlock c (a, false) = ((padGen c a)⁻¹).toWord := rfl
    rw [h1]
    exact FreeGroup.mk_toWord
  · show FreeGroup.mk (padBlock c (a, true)) = padGen c a
    have h1 : padBlock c (a, true) = (padGen c a).toWord := rfl
    rw [h1]
    exact FreeGroup.mk_toWord

/-- `mk` of the padding of a word is the padding of `mk`. -/
private lemma mk_padList (c : α → ℤ) (L : List (α × Bool)) :
    FreeGroup.mk (padList c L) = padHom c (FreeGroup.mk L) := by
  rw [padList, mk_flatten, List.map_map, padHom, FreeGroup.lift_mk]
  congr 1
  exact List.map_congr_left (fun p _ => mk_padBlock c p)

/-- The length of `padList` is the sum of the block lengths. -/
private lemma padList_length (c : α → ℤ) (L : List (α × Bool)) :
    (padList c L).length = (L.map (fun p : α × Bool => 2 + (c p.1).natAbs)).sum := by
  rw [padList, List.length_flatten]
  congr 1
  rw [List.map_map]
  exact List.map_congr_left (fun p _ => padBlock_length c p)

/-! ### `padList` of a reduced word is reduced -/

/-- Padding a reduced word gives a reduced word: the blocks do not cancel against each other. -/
private lemma padList_isReduced (c : α → ℤ) {L : List (α × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (padList c L) := by
  have hne : ([] : List (PadT α × Bool)) ∉ L.map (padBlock c) := by
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, -, hp⟩ := hmem
    exact padBlock_ne_nil c p hp
  rw [padList, FreeGroup.IsReduced, List.isChain_flatten hne]
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨p, -, rfl⟩ := hl
    exact padBlock_isReduced c p
  · refine List.isChain_map_of_isChain (padBlock c) ?_ hL
    intro p q hpq
    intro x hx y hy
    rw [padBlock_getLast] at hx
    rw [padBlock_head] at hy
    obtain hx' : (some p.1, p.2) = x := Option.mem_some_iff.mp hx
    obtain hy' : (some q.1, q.2) = y := Option.mem_some_iff.mp hy
    subst hx'
    subst hy'
    intro hxy
    exact hpq (Option.some.inj hxy)

/-! ### The reduced length of a padding -/

/-- The reduced word of `wordOf u` is reduced. -/
private lemma wordOf_isReduced (u : FreeGroup α) : FreeGroup.IsReduced (wordOf u) :=
  @FreeGroup.isReduced_toWord α (Classical.decEq α) u

/-- `norm` of a padding, for an arbitrary `DecidableEq` instance on the padded generators. -/
private lemma norm_padHom_aux (i : DecidableEq (PadT α)) (c : α → ℤ) (u : FreeGroup α) :
    @FreeGroup.norm (PadT α) i (padHom c u) = (padList c (wordOf u)).length := by
  letI := i
  have hmk : padHom c u = FreeGroup.mk (padList c (wordOf u)) := by
    have h := mk_padList c (wordOf u)
    rw [mk_wordOf u] at h
    exact h.symm
  rw [FreeGroup.norm, hmk, FreeGroup.toWord_mk,
    FreeGroup.IsReduced.reduce_eq (padList_isReduced c (wordOf_isReduced u))]

theorem relatorNorm_padHom {α : Type u} (c : α → ℤ) (u : FreeGroup α) :
    Work.OROneRel.relatorNorm (Work.OROneRel.padHom c u) =
      ((Work.OROneRel.wordOf u).map (fun p : α × Bool => 2 + (c p.1).natAbs)).sum := by
  rw [show relatorNorm (padHom c u) =
      @FreeGroup.norm (PadT α) (fun a b : PadT α => Classical.propDecidable (a = b))
        (padHom c u) from rfl]
  rw [norm_padHom_aux (fun a b : PadT α => Classical.propDecidable (a = b)) c u]
  exact padList_length c (wordOf u)

end Work.OROneRel
