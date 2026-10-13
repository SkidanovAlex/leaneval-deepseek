/-
DSSER: the enumeration of words `w : Fin d → ℕ` by total degree.

`wordList d N` lists each word of total degree `< N` exactly once, block by block in increasing
degree (`wordBlk d k` is the block of degree `k`).  These are exactly the monomials `z^w` occurring
in `𝔪^N` (see `Work.DSSER.maximalIdeal_pow_eq_span`).
-/
import Submission.Work.DSSER.Basic

universe u

namespace Work.DSSER

/-- Membership in `wordList d N`: the words of total degree `< N`. -/
theorem mem_wordList {d N : ℕ} {w : Fin d → ℕ} : w ∈ wordList d N ↔ ∑ i, w i < N := by
  simp only [wordList, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hwk⟩
    rw [mem_wordBlk.mp hwk]
    exact hk
  · intro h
    exact ⟨∑ i, w i, h, mem_wordBlk.mpr rfl⟩

/-- Splitting `wordList d N` at `M ≤ N`. -/
theorem wordList_eq_append {d M N : ℕ} (h : M ≤ N) :
    wordList d N = wordList d M ++ wordRest d M N := by
  have hN : N = M + (N - M) := (Nat.add_sub_of_le h).symm
  simp only [wordList, wordRest]
  conv_lhs => rw [hN, List.range_add, List.flatMap_append]

/-- Every word in `wordRest d M N` has total degree at least `M`. -/
theorem mem_wordRest {d M N : ℕ} (_h : M ≤ N) {w : Fin d → ℕ}
    (hw : w ∈ wordRest d M N) : M ≤ ∑ i, w i := by
  simp only [wordRest, List.mem_flatMap, List.mem_map, List.mem_range] at hw
  obtain ⟨b, ⟨j, hj, rfl⟩, hwb⟩ := hw
  rw [mem_wordBlk.mp hwb]
  omega

/-- The block of degree `0` consists of the single zero word. -/
theorem wordBlk_zero (d : ℕ) : wordBlk d 0 = [fun _ => 0] := by
  have hF : ((Fintype.piFinset (fun _ : Fin d => Finset.range 1)).filter
      (fun w : Fin d → ℕ => ∑ i, w i = 0)) = {fun _ => 0} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun i => Nat.one_pos, ?_⟩
      exact Finset.sum_eq_zero (fun i _ => rfl)
    · intro x hx
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hx
      funext i
      have hle := Finset.single_le_sum (f := x) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
  rw [wordBlk, hF]
  exact Finset.toList_singleton _

theorem wordList_zero (d : ℕ) : wordList d 0 = [] := rfl

theorem wordList_succ (d N : ℕ) : wordList d (N + 1) = wordList d N ++ wordBlk d N := by
  simp only [wordList, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The words of degree `< 1`: only the zero word. -/
theorem wordList_one (d : ℕ) : wordList d 1 = [fun _ => 0] := by
  rw [wordList_succ, wordList_zero, List.nil_append, wordBlk_zero]

/-- The list `wordList d N` is a duplicate-free enumeration of `wordFinset d N`, hence a list sum
over it is the corresponding `Finset` sum. -/
theorem wordList_sum (d N : ℕ) {S : Type u} [AddCommMonoid S] (g : (Fin d → ℕ) → S) :
    ((wordList d N).map g).sum = ∑ w ∈ wordFinset d N, g w := by
  induction N with
  | zero => simp [wordList, wordFinset]
  | succ N ih =>
    have h1 := wordList_succ d N
    have h2 : wordFinset d (N + 1) = wordFinset d N ∪ (wordBlk d N).toFinset := by
      ext w
      simp only [wordFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
        Finset.mem_union, List.mem_toFinset, mem_wordBlk]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hN : ∑ i, w i < N
        · exact Or.inl ⟨fun i => lt_of_le_of_lt
            (Finset.single_le_sum (f := w) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)) hN, hN⟩
        · exact Or.inr (by omega)
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨fun i => lt_of_lt_of_le (h1 i) (Nat.le_succ N), by omega⟩
        · refine ⟨fun i => ?_, by omega⟩
          have := Finset.single_le_sum (f := w) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
    rw [h1, List.map_append, List.sum_append, ih, h2]
    rw [Finset.sum_union]
    · rw [← List.sum_toFinset g (wordBlk_nodup d N)]
    · rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [mem_wordFinset] at hw1
      rw [List.mem_toFinset, mem_wordBlk] at hw2
      omega

end Work.DSSER
