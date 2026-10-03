import Mathlib
import Submission.Work.OROneRel.padDefs

/-!
# The elementary properties of a single padding block

For `p = (a, b) : α × Bool` the padding block is

`padBlock c p = (if b then padGen c a else (padGen c a)⁻¹).toWord`,
where `padGen c a = a * z ^ (c a) * a` and `z = none` is the fresh padding letter.

Every block begins and ends with its own letter `some a` and its interior letters are the fresh
letter `none`, so its reduced word has the explicit shape

`(some a, b) :: ((none, ·)^|c a| ++ [(some a, b)])`

from which `padBlock_props` follows at once: a block is reduced, and its first and its last letter
are both `(some a, b)`.

The file is self-contained: it rests only on `padDefs` and Mathlib.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Elementary computations with `FreeGroup.mk` -/

private lemma pbp_mk_replicate_true {β : Type*} (b : β) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, true)) = (FreeGroup.of b) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, ← List.singleton_append, ← FreeGroup.mul_mk,
      show FreeGroup.mk [(b, true)] = FreeGroup.of b from rfl, ih, pow_succ']

private lemma pbp_mk_replicate_false {β : Type*} (b : β) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, false)) = ((FreeGroup.of b) ^ n)⁻¹ := by
  have h : List.replicate n (b, false) = FreeGroup.invRev (List.replicate n (b, true)) := by
    simp [FreeGroup.invRev, List.map_replicate]
  rw [h, ← FreeGroup.inv_mk, pbp_mk_replicate_true]

private lemma pbp_mk_replicate_cond {β : Type*} (b : β) (d : Bool) (n : ℕ) :
    FreeGroup.mk (List.replicate n (b, d)) =
      (cond d (FreeGroup.of b) ((FreeGroup.of b)⁻¹)) ^ n := by
  cases d
  · show FreeGroup.mk (List.replicate n (b, false)) = ((FreeGroup.of b)⁻¹) ^ n
    rw [pbp_mk_replicate_false, inv_pow]
  · show FreeGroup.mk (List.replicate n (b, true)) = (FreeGroup.of b) ^ n
    rw [pbp_mk_replicate_true]

/-- In a group, the `|m|`-th power of `g` or of `g⁻¹` according to the sign of `m` is `g ^ m`. -/
private lemma pbp_cond_pow_natAbs_eq_zpow {G : Type*} [Group G] (g : G) (m : ℤ) :
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
private lemma pbp_invRev_replicate {β : Type*} (b : β) (d : Bool) (n : ℕ) :
    FreeGroup.invRev (List.replicate n (b, d)) = List.replicate n (b, !d) := by
  simp [FreeGroup.invRev, List.map_replicate]

/-! ### Reducedness of a repeated letter followed by a further letter -/

/-- A repeated letter followed by a letter with a different generator is reduced. -/
private lemma pbp_isReduced_replicate_append_singleton {β : Type*} (u v : β × Bool)
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
private lemma pbp_isReduced_cons_replicate_append_singleton {β : Type*} (u v : β × Bool)
    (h : v.1 ≠ u.1) (n : ℕ) : FreeGroup.IsReduced (v :: (List.replicate n u ++ [v])) := by
  refine List.IsChain.cons (pbp_isReduced_replicate_append_singleton u v (Ne.symm h) n) ?_
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
private lemma pbp_toWord_padGen_general {β : Type*} [DecidableEq β] (x z : β) (m : ℤ)
    (h : x ≠ z) :
    (FreeGroup.of x * (FreeGroup.of z) ^ m * FreeGroup.of x).toWord =
      (x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)]) := by
  have hred : FreeGroup.IsReduced
      ((x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)])) :=
    pbp_isReduced_cons_replicate_append_singleton (z, decide (0 ≤ m)) (x, true)
      (by simpa using h) m.natAbs
  have hmk : FreeGroup.mk
        ((x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)])) =
      FreeGroup.of x * (FreeGroup.of z) ^ m * FreeGroup.of x := by
    rw [show (x, true) :: (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)]) =
        [(x, true)] ++ (List.replicate m.natAbs (z, decide (0 ≤ m)) ++ [(x, true)]) from rfl]
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    rw [show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl, pbp_mk_replicate_cond,
      pbp_cond_pow_natAbs_eq_zpow, mul_assoc]
  rw [← hmk, FreeGroup.toWord_mk]
  exact hred.reduce_eq

/-- Inverting and reversing the reduced word of `of x * (of z)^m * of x`. -/
private lemma pbp_invRev_cons_replicate_cons {β : Type*} (x z : β) (d : Bool) (n : ℕ) :
    FreeGroup.invRev ((x, true) :: (List.replicate n (z, d) ++ [(x, true)])) =
      (x, false) :: (List.replicate n (z, !d) ++ [(x, false)]) := by
  rw [FreeGroup.invRev_cons, FreeGroup.invRev_append, pbp_invRev_replicate]
  simp [FreeGroup.invRev]

/-- The explicit shape of a padding block. -/
private lemma pbp_padBlock_eq (c : α → ℤ) (p : α × Bool) :
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
    have h1 : padBlock c (a, false) = ((padGen c a)⁻¹).toWord := by
      unfold padBlock
      simp
    rw [h1, FreeGroup.toWord_inv, padGen,
      pbp_toWord_padGen_general (some a) (none : PadT α) (c a) (by simp)]
    exact pbp_invRev_cons_replicate_cons (some a) (none : PadT α) (decide (0 ≤ c a)) (c a).natAbs
  · show padBlock c (a, true) = (some a, true) ::
        (List.replicate (c a).natAbs (none, decide (0 ≤ c a)) ++ [(some a, true)])
    have h1 : padBlock c (a, true) = (padGen c a).toWord := by
      unfold padBlock
      simp
    rw [h1, padGen,
      pbp_toWord_padGen_general (some a) (none : PadT α) (c a) (by simp)]

/-! ### Basic properties of a padding block

These are stated without any `DecidableEq` hypothesis on `α`: this keeps the instances used for
`FreeGroup.toWord` in the proofs identical to the ones fixed inside the definition of `padBlock`,
so that `pbp_padBlock_eq` applies directly. -/

/-- A padding block is reduced. -/
private lemma pbp_padBlock_isReduced (c : α → ℤ) (p : α × Bool) :
    FreeGroup.IsReduced (padBlock c p) := by
  rw [pbp_padBlock_eq]
  exact pbp_isReduced_cons_replicate_append_singleton
    (none, cond p.2 (decide (0 ≤ c p.1)) (!(decide (0 ≤ c p.1)))) (some p.1, p.2)
    (by simp) (c p.1).natAbs

/-- The first letter of a padding block. -/
private lemma pbp_padBlock_head (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).head? = some (some p.1, p.2) := by
  rw [pbp_padBlock_eq, List.head?_cons]

/-- The last letter of a padding block. -/
private lemma pbp_padBlock_getLast (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).getLast? = some (some p.1, p.2) := by
  rw [pbp_padBlock_eq]
  rw [show (some p.1, p.2) ::
        (List.replicate (c p.1).natAbs
            (none, cond p.2 (decide (0 ≤ c p.1)) (!(decide (0 ≤ c p.1)))) ++
          [(some p.1, p.2)]) =
      ((some p.1, p.2) ::
        List.replicate (c p.1).natAbs
            (none, cond p.2 (decide (0 ≤ c p.1)) (!(decide (0 ≤ c p.1))))) ++
        [(some p.1, p.2)] from rfl]
  rw [List.getLast?_concat]

theorem padBlock_props {α : Type*} [DecidableEq α] (c : α → ℤ) (p : α × Bool) :
    FreeGroup.IsReduced (Work.OROneRel.padBlock c p) ∧
    (Work.OROneRel.padBlock c p).head? = some (some p.1, p.2) ∧
    (Work.OROneRel.padBlock c p).getLast? = some (some p.1, p.2) :=
  ⟨pbp_padBlock_isReduced c p, pbp_padBlock_head c p, pbp_padBlock_getLast c p⟩

end Work.OROneRel
