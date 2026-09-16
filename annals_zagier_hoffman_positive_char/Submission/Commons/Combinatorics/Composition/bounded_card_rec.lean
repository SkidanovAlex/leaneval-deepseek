import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum.Ineq

open scoped BigOperators

namespace Commons.Combinatorics.Composition

/-- Compositions of `n` whose blocks are all `≤ B`. -/
private abbrev Bnd (B n : ℕ) : Type := {c : Composition n // ∀ b ∈ c.blocks, b ≤ B}

/-- Possible sizes of the first block in a composition of `n` with blocks `≤ B`. -/
private abbrev Idx (B n : ℕ) : Type := {a : ℕ // a ∈ Finset.Icc 1 (Nat.min B n)}

private lemma blocks_ne_nil {n : ℕ} (c : Composition n) (hn : 1 ≤ n) : c.blocks ≠ [] := by
  intro h
  rw [← c.blocks_sum, h] at hn
  simp at hn

private def idxToFin (B n : ℕ) (a : Idx B n) : Fin (Nat.min B n) :=
  ⟨a.1 - 1, by obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp a.2; omega⟩

private def finToIdx (B n : ℕ) (i : Fin (Nat.min B n)) : Idx B n :=
  ⟨i.1 + 1, by rw [Finset.mem_Icc]; have := i.2; omega⟩

private lemma idxToFin_finToIdx (B n : ℕ) (i : Fin (Nat.min B n)) :
    idxToFin B n (finToIdx B n i) = i := by
  ext
  simp only [idxToFin, finToIdx, Subtype.coe_mk]
  omega

private lemma finToIdx_idxToFin (B n : ℕ) (a : Idx B n) : finToIdx B n (idxToFin B n a) = a := by
  have h := (Finset.mem_Icc.mp a.2).1
  ext
  simp only [idxToFin, finToIdx, Subtype.coe_mk]
  omega

private def idxFinEquiv (B n : ℕ) : Idx B n ≃ Fin (Nat.min B n) where
  toFun := idxToFin B n
  invFun := finToIdx B n
  left_inv := finToIdx_idxToFin B n
  right_inv := idxToFin_finToIdx B n

/-- Splitting off the first block of a composition with bounded blocks, as an element of the
disjoint union over the possible first-block sizes. -/
private noncomputable def splitMap (B n : ℕ) (hn : 1 ≤ n) :
    Bnd B n → Σ a : Idx B n, Bnd B (n - a.1) :=
  fun c => by
    have hnil : c.1.blocks ≠ [] := blocks_ne_nil c.1 hn
    have hcons : c.1.blocks.head hnil :: c.1.blocks.tail = c.1.blocks := List.cons_head_tail hnil
    have hmem : c.1.blocks.head hnil ∈ c.1.blocks := List.head_mem hnil
    have hsum : c.1.blocks.head hnil + c.1.blocks.tail.sum = n := by
      have h := c.1.blocks_sum
      rw [← hcons, List.sum_cons] at h
      exact h
    exact ⟨⟨c.1.blocks.head hnil,
              Finset.mem_Icc.mpr ⟨c.1.blocks_pos hmem,
                Nat.le_min.mpr ⟨c.2 _ hmem, c.1.blocks_le hmem⟩⟩⟩,
           ⟨{ blocks := c.1.blocks.tail
              blocks_pos := fun {b} hb => c.1.blocks_pos (by rw [← hcons]; exact List.mem_cons_of_mem _ hb)
              blocks_sum := by
                show c.1.blocks.tail.sum = n - c.1.blocks.head hnil
                exact (Nat.add_sub_cancel_left _ _).symm.trans (by rw [hsum]) },
            fun b hb => c.2 b (by rw [← hcons]; exact List.mem_cons_of_mem _ hb)⟩⟩

/-- Gluing a first block onto a composition with bounded blocks. -/
private noncomputable def glueMap (B n : ℕ) : (Σ a : Idx B n, Bnd B (n - a.1)) → Bnd B n :=
  fun p => by
    rcases p with ⟨a, d⟩
    have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
    have ham : a.1 ≤ Nat.min B n := (Finset.mem_Icc.mp a.2).2
    have han : a.1 ≤ n := le_trans ham (Nat.min_le_right _ _)
    have haB : a.1 ≤ B := le_trans ham (Nat.min_le_left _ _)
    refine ⟨Composition.cast (Composition.append (Composition.single a.1 (by omega)) d.1)
        (by omega), ?_⟩
    intro b hb
    rw [Composition.cast_blocks, Composition.append_blocks, Composition.single_blocks] at hb
    rw [List.mem_append, List.mem_singleton] at hb
    rcases hb with rfl | hb
    · exact haB
    · exact d.2 b hb

@[simp] private lemma splitMap_fst (B n : ℕ) (hn : 1 ≤ n) (c : Bnd B n) :
    (splitMap B n hn c).1.1 = c.1.blocks.head (blocks_ne_nil c.1 hn) := rfl

@[simp] private lemma splitMap_snd_blocks (B n : ℕ) (hn : 1 ≤ n) (c : Bnd B n) :
    (splitMap B n hn c).2.1.blocks = c.1.blocks.tail := rfl

@[simp] private lemma glueMap_blocks (B n : ℕ) (a : Idx B n) (d : Bnd B (n - a.1)) :
    (glueMap B n ⟨a, d⟩).1.blocks = a.1 :: d.1.blocks := by
  simp only [glueMap, Composition.cast_blocks, Composition.append_blocks,
    Composition.single_blocks, List.singleton_append]

@[simp] private lemma glueMap_blocks' (B n : ℕ) (p : Σ a : Idx B n, Bnd B (n - a.1)) :
    (glueMap B n p).1.blocks = p.1.1 :: p.2.1.blocks := by
  rcases p with ⟨a, d⟩
  exact glueMap_blocks B n a d

/-- The bijection expressing that a composition with bounded blocks is determined by its first
block together with the composition formed by the remaining blocks. -/
private noncomputable def bndEquiv (B n : ℕ) (hn : 1 ≤ n) :
    Bnd B n ≃ Σ a : Idx B n, Bnd B (n - a.1) where
  toFun := splitMap B n hn
  invFun := glueMap B n
  left_inv c := by
    apply Subtype.ext
    apply Composition.ext
    refine (glueMap_blocks' B n (splitMap B n hn c)).trans ?_
    exact List.cons_head_tail (blocks_ne_nil c.1 hn)
  right_inv p := by
    rcases p with ⟨a, d⟩
    apply Sigma.ext
    · apply Subtype.ext
      rw [splitMap_fst]
      exact List.head_cons
    · apply heq_of_eq
      apply Subtype.ext
      apply Composition.ext
      rw [splitMap_snd_blocks, glueMap_blocks, List.tail_cons]

/-- **Recursion for compositions with bounded parts.**  Splitting off the first part gives
`#{compositions of n with parts ≤ B} = Σ_{i < min B n} #{compositions of n − (i+1) with parts ≤ B}`. -/
theorem bounded_card_rec (B n : ℕ) (hB : 1 ≤ B) (hn : 1 ≤ n) :
    Nat.card {c : Composition n // ∀ b ∈ c.blocks, b ≤ B}
      = ∑ i ∈ Finset.range (Nat.min B n),
          Nat.card {c : Composition (n - (i + 1)) // ∀ b ∈ c.blocks, b ≤ B} := by
  have _hB := hB
  change Nat.card (Bnd B n) = ∑ i ∈ Finset.range (Nat.min B n), Nat.card (Bnd B (n - (i + 1)))
  rw [Nat.card_congr (bndEquiv B n hn), Nat.card_sigma]
  rw [Finset.sum_range]
  refine Fintype.sum_equiv (idxFinEquiv B n)
    (fun a : Idx B n => Nat.card (Bnd B (n - a.1))) _ ?_
  intro a
  have h1 : (((idxFinEquiv B n a : Fin (Nat.min B n)) : ℕ)) + 1 = a.1 := by
    have h := (Finset.mem_Icc.mp a.2).1
    simp only [idxFinEquiv, Equiv.coe_fn_mk, idxToFin]
    omega
  rw [h1]

end Commons.Combinatorics.Composition