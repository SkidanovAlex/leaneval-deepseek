/-
Copyright (c) 2026 The team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A recursion for compositions none of whose blocks is divisible by `q`

Let `A(m)` be the number of compositions of `m` all of whose blocks avoid the multiples of `q`.
Splitting off the first block gives the recursion

`A(m) = ∑_{i < m, q ∤ i+1} A(m - (i+1))`   (`m ≥ 1`),

implemented below as `av_card_rec`.  When `q + 1 ≤ n ≤ 2q - 2`, the only multiple of `q` that can
occur as a block of a composition of `n` is `q` itself, and applying the recursion both at `n` and
at `n - q` (where `n - q ≤ q - 2`, so *no* block can be divisible by `q`) collapses the recursion
to the clean form

`A(n) = ∑_{i < q} A(n - (i+1))`.

This is the counting identity needed for the Zagier–Hoffman problem in positive characteristic.
-/

open scoped BigOperators

namespace Commons.Combinatorics.Composition

/-- The type of compositions of `m` none of whose blocks is divisible by `q`. -/
private abbrev Av (q m : ℕ) : Type := {c : Composition m // ∀ b ∈ c.blocks, ¬ q ∣ b}

/-- Possible values of `(size of the first block) - 1` for a composition of `m` whose first block
is not divisible by `q`. -/
private abbrev IdxR (q m : ℕ) : Type :=
  {i : ℕ // i ∈ (Finset.range m).filter (fun i => ¬ q ∣ (i + 1))}

private lemma blocks_ne_nil {n : ℕ} (c : Composition n) (hn : 1 ≤ n) : c.blocks ≠ [] := by
  intro h
  rw [← c.blocks_sum, h] at hn
  simp at hn

/-- Splitting off the first block of a composition all of whose blocks avoid the multiples of `q`. -/
private noncomputable def splitMap (q m : ℕ) (hm : 1 ≤ m) :
    Av q m → Σ i : IdxR q m, Av q (m - (i.1 + 1)) := fun c => by
  have hnil : c.1.blocks ≠ [] := blocks_ne_nil c.1 hm
  have hcons : c.1.blocks.head hnil :: c.1.blocks.tail = c.1.blocks := List.cons_head_tail hnil
  have hmem : c.1.blocks.head hnil ∈ c.1.blocks := List.head_mem hnil
  have hpos : 1 ≤ c.1.blocks.head hnil := c.1.blocks_pos hmem
  have hle : c.1.blocks.head hnil ≤ m := c.1.blocks_le hmem
  have hsum : c.1.blocks.head hnil + c.1.blocks.tail.sum = m := by
    have h := c.1.blocks_sum
    rw [← hcons, List.sum_cons] at h
    exact h
  refine ⟨⟨c.1.blocks.head hnil - 1, ?_⟩, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel hpos]
    exact c.2 _ hmem
  · refine ⟨⟨c.1.blocks.tail, ?_, ?_⟩, ?_⟩
    · intro b hb
      exact c.1.blocks_pos (by rw [← hcons]; exact List.mem_cons_of_mem _ hb)
    · show c.1.blocks.tail.sum = m - (c.1.blocks.head hnil - 1 + 1)
      rw [Nat.sub_add_cancel hpos]
      omega
    · intro b hb
      exact c.2 b (by rw [← hcons]; exact List.mem_cons_of_mem _ hb)

/-- Gluing a first block of size `i + 1` onto a composition all of whose blocks avoid the multiples
of `q`. -/
private noncomputable def glueMap (q m : ℕ) :
    (Σ i : IdxR q m, Av q (m - (i.1 + 1))) → Av q m := fun p => by
  obtain ⟨i, d⟩ := p
  have hq : ¬ q ∣ (i.1 + 1) := (Finset.mem_filter.mp i.2).2
  have hlt : i.1 + 1 ≤ m := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp i.2).1
    omega
  refine ⟨Composition.cast (Composition.append (Composition.single (i.1 + 1) (Nat.succ_pos _)) d.1)
      (by omega), ?_⟩
  intro b hb
  rw [Composition.cast_blocks, Composition.append_blocks, Composition.single_blocks] at hb
  rw [List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | hb
  · rw [hb]; exact hq
  · exact d.2 b hb

@[simp] private lemma splitMap_fst (q m : ℕ) (hm : 1 ≤ m) (c : Av q m) :
    (splitMap q m hm c).1.1 = c.1.blocks.head (blocks_ne_nil c.1 hm) - 1 := rfl

@[simp] private lemma splitMap_snd_blocks (q m : ℕ) (hm : 1 ≤ m) (c : Av q m) :
    (splitMap q m hm c).2.1.blocks = c.1.blocks.tail := rfl

@[simp] private lemma glueMap_blocks (q m : ℕ) (i : IdxR q m) (d : Av q (m - (i.1 + 1))) :
    (glueMap q m ⟨i, d⟩).1.blocks = (i.1 + 1) :: d.1.blocks := by
  simp only [glueMap, Composition.cast_blocks, Composition.append_blocks,
    Composition.single_blocks, List.singleton_append]

@[simp] private lemma glueMap_blocks' (q m : ℕ) (p : Σ i : IdxR q m, Av q (m - (i.1 + 1))) :
    (glueMap q m p).1.blocks = (p.1.1 + 1) :: p.2.1.blocks := by
  obtain ⟨i, d⟩ := p
  exact glueMap_blocks q m i d

/-- A composition all of whose blocks avoid the multiples of `q` is determined by the size of its
first block together with the composition formed by the remaining blocks. -/
private noncomputable def avEquiv (q m : ℕ) (hm : 1 ≤ m) :
    Av q m ≃ Σ i : IdxR q m, Av q (m - (i.1 + 1)) where
  toFun := splitMap q m hm
  invFun := glueMap q m
  left_inv c := by
    apply Subtype.ext
    apply Composition.ext
    have hnil : c.1.blocks ≠ [] := blocks_ne_nil c.1 hm
    have hpos : 1 ≤ c.1.blocks.head hnil := c.1.blocks_pos (List.head_mem hnil)
    simp only [glueMap_blocks', splitMap_fst, splitMap_snd_blocks]
    rw [Nat.sub_add_cancel hpos]
    exact List.cons_head_tail hnil
  right_inv p := by
    obtain ⟨i, d⟩ := p
    apply Sigma.ext
    · apply Subtype.ext
      simp only [splitMap_fst, glueMap_blocks, List.head_cons]
      omega
    · apply heq_of_eq
      apply Subtype.ext
      apply Composition.ext
      simp only [splitMap_snd_blocks, glueMap_blocks, List.tail_cons]

/-- **Recursion for compositions avoiding multiples of `q`.**  Splitting off the first block gives
`A(m) = ∑_{i < m, q ∤ i+1} A(m - (i+1))` for `m ≥ 1`. -/
private lemma av_card_rec (q m : ℕ) (hm : 1 ≤ m) :
    Nat.card (Av q m)
      = ∑ i ∈ Finset.range m, (if q ∣ (i + 1) then 0 else Nat.card (Av q (m - (i + 1)))) := by
  have h1 : Nat.card (Av q m) = Nat.card (Sigma fun i : IdxR q m => Av q (m - (i.1 + 1))) :=
    Nat.card_congr (avEquiv q m hm)
  rw [h1, Nat.card_sigma]
  rw [← Finset.sum_subtype ((Finset.range m).filter (fun i => ¬ q ∣ (i + 1))) (fun x => Iff.rfl)
    (fun i => Nat.card (Av q (m - (i + 1))))]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : q ∣ (i + 1) <;> simp [h]

/-- Collapsing the recursion when `q + 1 ≤ n ≤ 2q - 2`:  the terms of the recursion at `n` beyond
the first `q` blocks recombine into the single term `A(n - q)`, by the recursion at `n - q` (where
no block can be a multiple of `q`). -/
private lemma sum_identity (q n : ℕ) (hq1 : 1 ≤ q) (h1 : q + 1 ≤ n) (h2 : n ≤ 2 * q - 2) :
    ∑ i ∈ Finset.range n, (if q ∣ (i + 1) then 0 else Nat.card (Av q (n - (i + 1))))
      = ∑ i : Fin q, Nat.card (Av q (n - (i + 1))) := by
  have hqn : q ≤ n := by omega
  have hd1 : 1 ≤ n - q := by omega
  have hdq : n - q ≤ q - 2 := by omega
  have hfin : (∑ i : Fin q, Nat.card (Av q (n - (i + 1))))
      = ∑ i ∈ Finset.range q, Nat.card (Av q (n - (i + 1))) := by
    rw [Finset.sum_range]
  have hsplit : ∑ i ∈ Finset.range n, (if q ∣ (i + 1) then 0 else Nat.card (Av q (n - (i + 1))))
      = (∑ i ∈ Finset.range q, (if q ∣ (i + 1) then 0 else Nat.card (Av q (n - (i + 1)))))
        + (∑ i ∈ Finset.range (n - q),
            (if q ∣ (q + i + 1) then 0 else Nat.card (Av q (n - (q + i + 1))))) := by
    have hr : Finset.range n = Finset.range (q + (n - q)) := by rw [Nat.add_sub_of_le hqn]
    rw [hr, Finset.sum_range_add]
  have hA : (∑ i ∈ Finset.range q, (if q ∣ (i + 1) then 0 else Nat.card (Av q (n - (i + 1)))))
      = ∑ i ∈ Finset.range (q - 1), Nat.card (Av q (n - (i + 1))) := by
    have hr : Finset.range q = Finset.range ((q - 1) + 1) := by rw [Nat.sub_add_cancel hq1]
    have hlast : (if q ∣ ((q - 1) + 1) then 0 else Nat.card (Av q (n - ((q - 1) + 1)))) = 0 := by
      rw [Nat.sub_add_cancel hq1, if_pos (dvd_refl q)]
    rw [hr, Finset.sum_range_succ, hlast, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < q - 1 := Finset.mem_range.mp hi
    have hnd : ¬ q ∣ (i + 1) := fun hd => by
      have := Nat.le_of_dvd (Nat.succ_pos i) hd
      omega
    rw [if_neg hnd]
  have hB : (∑ i ∈ Finset.range (n - q),
        (if q ∣ (q + i + 1) then 0 else Nat.card (Av q (n - (q + i + 1)))))
      = Nat.card (Av q (n - q)) := by
    rw [av_card_rec q (n - q) hd1]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n - q := Finset.mem_range.mp hi
    have hnd : ¬ q ∣ (i + 1) := fun hd => by
      have := Nat.le_of_dvd (Nat.succ_pos i) hd
      omega
    have hnd2 : ¬ q ∣ (q + i + 1) := by
      intro hd
      apply hnd
      have hsub : q ∣ (q + i + 1) - q := Nat.dvd_sub hd (dvd_refl q)
      rwa [show q + i + 1 - q = i + 1 by omega] at hsub
    have harg : n - (q + i + 1) = (n - q) - (i + 1) := by omega
    rw [if_neg hnd, if_neg hnd2, harg]
  have hC : (∑ i ∈ Finset.range q, Nat.card (Av q (n - (i + 1))))
      = (∑ i ∈ Finset.range (q - 1), Nat.card (Av q (n - (i + 1))))
        + Nat.card (Av q (n - q)) := by
    have hr : Finset.range q = Finset.range ((q - 1) + 1) := by rw [Nat.sub_add_cancel hq1]
    have hlast : Nat.card (Av q (n - ((q - 1) + 1))) = Nat.card (Av q (n - q)) := by
      rw [Nat.sub_add_cancel hq1]
    rw [hr, Finset.sum_range_succ, hlast]
  rw [hfin, hsplit, hA, hB, hC]

/-- **General recursion for compositions avoiding multiples of `q`.**  For `m ≥ 1`, the number of
compositions of `m` all of whose blocks avoid the multiples of `q` equals the sum, over the possible
sizes `i + 1` of the first block (with `q ∤ i + 1`), of the numbers of such compositions of
`m - (i + 1)`. -/
theorem card_avoid_dvd_rec (q m : ℕ) (hm : 1 ≤ m) :
    Nat.card {c : Composition m // ∀ b ∈ c.blocks, ¬ q ∣ b}
      = ∑ i ∈ Finset.range m,
          (if q ∣ (i + 1) then 0
           else Nat.card {c : Composition (m - (i + 1)) // ∀ b ∈ c.blocks, ¬ q ∣ b}) :=
  av_card_rec q m hm

/-- **Recursion for compositions avoiding multiples of `q` in the range `q + 1 ≤ n ≤ 2q - 2`.**
The number of compositions of `n` none of whose blocks is divisible by `q` equals the sum, over the
first block sizes `1, …, q`, of the numbers of such compositions of `n - (i+1)`. -/
theorem avoid_dvd_card_rec (q n : ℕ) (hq : 2 ≤ q) (h1 : q + 1 ≤ n) (h2 : n ≤ 2 * q - 2) :
    Nat.card {c : Composition n // ∀ b ∈ c.blocks, ¬ q ∣ b}
      = ∑ i : Fin q, Nat.card {c : Composition (n - (i + 1)) // ∀ b ∈ c.blocks, ¬ q ∣ b} := by
  have hq1 : 1 ≤ q := by omega
  have hn1 : 1 ≤ n := by omega
  change Nat.card (Av q n) = ∑ i : Fin q, Nat.card (Av q (n - (i + 1)))
  rw [av_card_rec q n hn1]
  exact sum_identity q n hq1 h1 h2

end Commons.Combinatorics.Composition
