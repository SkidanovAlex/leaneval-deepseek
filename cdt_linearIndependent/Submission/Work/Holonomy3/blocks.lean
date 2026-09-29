import Mathlib
import Submission.Work.Holonomy3.defs

/-!
# The block decomposition of `[0,1]` by the weights `w`

For a family of positive weights `w : Fin (l+1) → ℝ` with `∑ k, w k = 1`, the `k`-th block is
`[blockStart w k, blockStart w k + w k)`, and these blocks tile `[0,1)`.  This module records the
(purely arithmetic) facts about them that the patched function `patched w φ` and its rearrangement
integral need.

The auxiliary prefix-sum function `bstart w i = ∑_{j < i} w j` (an ordinary `ℕ`-indexed prefix sum)
is used for the inductive interval-splitting arguments; `blockStart w k = bstart w k` for `k : Fin n`.

Main facts:
* `blockStart_add_self` : `blockStart w k + w k = bstart w (k+1)` (the next block start);
* `not_mem_block_of_ne` : distinct blocks are disjoint;
* `exists_mem_block`   : the blocks cover `[0,1)`;
* `patched_eq_on_block`: on its block, `patched w φ` is `circleLog (φ k)` composed with the affine
  rescaling of that block onto `[0,1]`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open MeasureTheory Set
open scoped BigOperators

/-- `bstart w i = ∑_{j < i} w j` : the `ℕ`-indexed prefix sum of the weights. -/
noncomputable def bstart {n : ℕ} (w : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < i), w j

theorem bstart_zero {n : ℕ} (w : Fin n → ℝ) : bstart w 0 = 0 := by
  simp [bstart]

theorem bstart_succ {n : ℕ} (w : Fin n → ℝ) {i : ℕ} (hi : i < n) :
    bstart w (i + 1) = bstart w i + w ⟨i, hi⟩ := by
  have hset : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < i + 1))
      = insert ⟨i, hi⟩ (Finset.univ.filter (fun j : Fin n => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (h | h)
      · rw [h]; exact Nat.lt_succ_self i
      · exact Nat.lt_succ_of_lt h
  rw [bstart, bstart, hset, Finset.sum_insert (by simp), add_comm]

theorem bstart_top {n : ℕ} (w : Fin n → ℝ) : bstart w n = ∑ k, w k := by
  simp [bstart]

theorem bstart_mono {n : ℕ} {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) {i j : ℕ} (h : i ≤ j) :
    bstart w i ≤ bstart w j := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact lt_of_lt_of_le hx h
  · intro x _ _
    exact hw x

theorem bstart_lt {n : ℕ} {w : Fin n → ℝ} (hw : ∀ k, 0 < w k) {i j : ℕ} (h : i < j)
    (hj : j ≤ n) : bstart w i < bstart w j := by
  have hi : i < n := lt_of_lt_of_le h hj
  have h1 : bstart w i + w ⟨i, hi⟩ ≤ bstart w j := by
    rw [← bstart_succ w hi]
    exact bstart_mono (fun k => le_of_lt (hw k)) (Nat.succ_le_of_lt h)
  linarith [hw ⟨i, hi⟩]

theorem bstart_nonneg {n : ℕ} {w : Fin n → ℝ} (hw : ∀ k, 0 < w k) (i : ℕ) : 0 ≤ bstart w i := by
  refine Finset.sum_nonneg (fun j _ => ?_)
  exact le_of_lt (hw j)

theorem blockStart_eq_bstart {l : ℕ} (w : Fin (l + 1) → ℝ) (k : Fin (l + 1)) :
    blockStart w k = bstart w (k : ℕ) := by
  simp only [blockStart, bstart, Fin.lt_def]

theorem blockStart_nonneg {l : ℕ} {w : Fin (l + 1) → ℝ} (hw : ∀ k, 0 < w k) (k : Fin (l + 1)) :
    0 ≤ blockStart w k := by
  rw [blockStart_eq_bstart]
  exact bstart_nonneg hw _

/-- The right end of the `k`-th block is the next prefix sum (and, for the last block, `1`
when `∑ k, w k = 1`). -/
theorem blockStart_add_self {l : ℕ} (w : Fin (l + 1) → ℝ) (k : Fin (l + 1)) :
    blockStart w k + w k = bstart w ((k : ℕ) + 1) := by
  have hlt : (k : ℕ) < l + 1 := k.isLt
  rw [blockStart_eq_bstart, ← bstart_succ w hlt]

theorem blockStart_add_le_one {l : ℕ} {w : Fin (l + 1) → ℝ} (hw : ∀ k, 0 < w k)
    (hsum : ∑ k, w k = 1) (k : Fin (l + 1)) : blockStart w k + w k ≤ 1 := by
  rw [blockStart_add_self w k]
  calc bstart w ((k : ℕ) + 1) ≤ bstart w (l + 1) :=
        bstart_mono (fun j => le_of_lt (hw j)) (Nat.succ_le_of_lt k.isLt)
    _ = ∑ j, w j := bstart_top w
    _ = 1 := hsum

/-- Distinct blocks are disjoint. -/
theorem not_mem_block_of_ne {l : ℕ} {w : Fin (l + 1) → ℝ} (hw : ∀ k, 0 < w k)
    {i j : Fin (l + 1)} (hij : i ≠ j) {t : ℝ}
    (ht : t ∈ Set.Ico (blockStart w i) (blockStart w i + w i)) :
    t ∉ Set.Ico (blockStart w j) (blockStart w j + w j) := by
  intro hj
  rw [Set.mem_Ico] at ht hj
  rw [blockStart_add_self w i] at ht
  rw [blockStart_add_self w j] at hj
  rw [blockStart_eq_bstart] at ht hj
  rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
  · have hle : bstart w ((i : ℕ) + 1) ≤ bstart w (j : ℕ) :=
      bstart_mono (fun k => le_of_lt (hw k)) (Nat.succ_le_of_lt h)
    linarith [hle, ht.1, ht.2, hj.1, hj.2]
  · have hle : bstart w ((j : ℕ) + 1) ≤ bstart w (i : ℕ) :=
      bstart_mono (fun k => le_of_lt (hw k)) (Nat.succ_le_of_lt h)
    linarith [hle, ht.1, ht.2, hj.1, hj.2]

/-- The blocks cover `[0,1)`. -/
theorem exists_mem_block {l : ℕ} {w : Fin (l + 1) → ℝ} (hw : ∀ k, 0 < w k)
    (hsum : ∑ k, w k = 1) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ∃ k : Fin (l + 1), t ∈ Set.Ico (blockStart w k) (blockStart w k + w k) := by
  set S : Finset (Fin (l + 1)) :=
    Finset.univ.filter (fun k : Fin (l + 1) => t < bstart w ((k : ℕ) + 1)) with hS
  have hne : S.Nonempty := by
    refine ⟨⟨l, by omega⟩, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [bstart_top, hsum]
    exact ht.2
  obtain ⟨k, hkS, hkmin⟩ : ∃ k : Fin (l + 1), k ∈ S ∧ ∀ j ∈ S, k ≤ j :=
    ⟨S.min' hne, Finset.min'_mem S hne, fun j hj => Finset.min'_le S j hj⟩
  have hkS' : t < bstart w ((k : ℕ) + 1) := (Finset.mem_filter.mp hkS).2
  have hk_le : bstart w (k : ℕ) ≤ t := by
    rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
    · rw [h0, bstart_zero]; exact ht.1
    · obtain ⟨m, hm⟩ : ∃ m, (k : ℕ) = m + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hnot : ¬ (t < bstart w (k : ℕ)) := by
        intro hc
        rw [hm] at hc
        have hmS : (⟨m, by omega⟩ : Fin (l + 1)) ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hc
        have := hkmin ⟨m, by omega⟩ hmS
        simp only [Fin.le_def] at this
        omega
      exact not_lt.mp hnot
  refine ⟨k, ?_, ?_⟩
  · show blockStart w k ≤ t
    rw [blockStart_eq_bstart]
    exact hk_le
  · show t < blockStart w k + w k
    rw [blockStart_add_self w k]
    exact hkS'

/-- On its own block, `patched w φ` equals `circleLog (φ k)` composed with the affine rescaling
of that block onto `[0,1]`. -/
theorem patched_eq_on_block {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ)
    (hw : ∀ k, 0 < w k) (k : Fin (l + 1)) {t : ℝ}
    (ht : t ∈ Set.Ico (blockStart w k) (blockStart w k + w k)) :
    patched w φ t = circleLog (φ k) ((t - blockStart w k) / w k) := by
  unfold patched
  rw [Finset.sum_eq_single k]
  · rw [if_pos ht]
  · intro b _ hb
    rw [if_neg]
    exact fun h => not_mem_block_of_ne hw (fun h' => hb h'.symm) ht h
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem patched_eq_on_Ioo {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ)
    (hw : ∀ k, 0 < w k) (k : Fin (l + 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo (blockStart w k) (blockStart w k + w k)) :
    patched w φ t = circleLog (φ k) ((t - blockStart w k) / w k) :=
  patched_eq_on_block w φ hw k ⟨le_of_lt ht.1, ht.2⟩

/-- If two functions agree on the open interval `Ioo a b` (with `a ≤ b`), they agree almost
everywhere on `uIoc a b`: the two can differ only at the right endpoint. -/
theorem ae_eq_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ t ∈ Set.Ioo a b, f t = g t) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a b → f x = g x := by
  rw [Set.uIoc_of_le hab]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton b)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  by_contra hxb
  exact hx (fun hxi => h x ⟨hxi.1, lt_of_le_of_ne hxi.2 hxb⟩)

/-- `patched w φ` vanishes on `[1, ∞)`. -/
theorem patched_eq_zero_of_one_le {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ)
    (hw : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1) {t : ℝ} (ht : 1 ≤ t) :
    patched w φ t = 0 := by
  unfold patched
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [if_neg]
  intro h
  rw [Set.mem_Ico] at h
  have := blockStart_add_le_one hw hsum k
  linarith [h.2]

end Work.Holonomy3
