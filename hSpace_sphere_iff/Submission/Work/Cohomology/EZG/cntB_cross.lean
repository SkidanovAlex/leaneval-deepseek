import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

/-!
# Counting the complement of a shuffle after deleting a position

For a shuffle `A ⊆ Fin (n+1)` and a position `p : Fin (n+1)`, `delPosP A p ⊆ Fin n` is the
shuffle obtained by deleting the position `p` (which is *not* an element of `A` in the
application).  This file computes `cntB (delPosP A p) m`, the number of elements of the
complement of the deleted shuffle that lie below `m`, in terms of `cntB A` and the position `p`,
and deduces the "crossing" statement `cntB_cross` used in the Eilenberg–Zilber shuffle lemma.
-/

namespace Work.Cohomology.EZG

set_option linter.unusedVariables false

/-- The value of `Fin.succAbove p` in terms of values of `Fin`s. -/
lemma succAbove_val_ite {n : ℕ} (p : Fin (n + 1)) (t : Fin n) :
    (Fin.succAbove p t).val = if t.val < p.val then t.val else t.val + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt p t (Fin.lt_def.mpr h)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p t
      (by simp only [Fin.le_def, Fin.val_castSucc]; omega)]
    rfl

/-- The elements of the complement of `delPosP A p` that lie below `m` correspond, under
`Fin.succAbove p`, to the elements `w` of the complement of `A` which are either below `p` and
below `m`, or above `p` and at most `m`. -/
lemma cntB_delPosP_eq {n : ℕ} (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (m : ℕ) :
    cntB (delPosP A p) m =
      ((Finset.univ \ A).filter (fun w : Fin (n + 1) =>
        (w.val < p.val ∧ w.val < m) ∨ (p.val < w.val ∧ w.val ≤ m))).card := by
  have hcompl : (Finset.univ \ delPosP A p)
      = (Finset.univ : Finset (Fin n)).filter
          (fun t => Fin.succAbove p t ∈ (Finset.univ \ A)) := by
    ext t
    simp [delPosP]
  rw [cntB, hcompl, Finset.filter_filter]
  refine Finset.card_bij (fun t _ => Fin.succAbove p t) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨hB, hm⟩ := ht
    refine ⟨hB, ?_⟩
    rw [succAbove_val_ite]
    split_ifs with h
    · exact Or.inl ⟨h, hm⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · intro a _ b _ h
    exact Fin.succAbove_right_injective h
  · intro b hb
    simp only [Finset.mem_filter] at hb
    obtain ⟨hbB, hbcond⟩ := hb
    have hbne : b ≠ p := by
      rintro rfl
      rcases hbcond with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hbne
    refine ⟨t, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by rw [ht]; exact hbB, ?_⟩
      have hv : (Fin.succAbove p t).val = b.val := by rw [ht]
      rw [succAbove_val_ite] at hv
      rcases hbcond with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs at hv <;> omega
    · simpa using ht

/-- `cntB` of a deleted shuffle, evaluated below the deleted position. -/
lemma cntB_delPosP_of_le {n : ℕ} (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (m : ℕ)
    (hp : m ≤ p.val) : cntB (delPosP A p) m = cntB A m := by
  rw [cntB_delPosP_eq]
  have hf : (Finset.univ \ A).filter (fun w : Fin (n + 1) =>
        (w.val < p.val ∧ w.val < m) ∨ (p.val < w.val ∧ w.val ≤ m))
      = (Finset.univ \ A).filter (fun w : Fin (n + 1) => w.val < m) := by
    refine Finset.filter_congr ?_
    intro w _
    constructor <;> intro h <;> omega
  rw [hf, cntB]

/-- `cntB` of a deleted shuffle, evaluated above the deleted position. -/
lemma cntB_delPosP_of_ge {n : ℕ} (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (m : ℕ)
    (hp : p.val ≤ m) : cntB (delPosP A p) m = cntB A p.val +
      ((Finset.univ \ A).filter (fun w : Fin (n + 1) => p.val < w.val ∧ w.val ≤ m)).card := by
  rw [cntB_delPosP_eq, cntB]
  have hf : (Finset.univ \ A).filter (fun w : Fin (n + 1) =>
        (w.val < p.val ∧ w.val < m) ∨ (p.val < w.val ∧ w.val ≤ m))
      = ((Finset.univ \ A).filter (fun w : Fin (n + 1) => w.val < p.val))
        ∪ ((Finset.univ \ A).filter (fun w : Fin (n + 1) => p.val < w.val ∧ w.val ≤ m)) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr ?_
    intro w _
    constructor <;> intro h <;> omega
  have hdisj : Disjoint ((Finset.univ \ A).filter (fun w : Fin (n + 1) => w.val < p.val))
      ((Finset.univ \ A).filter (fun w : Fin (n + 1) => p.val < w.val ∧ w.val ≤ m)) := by
    rw [Finset.disjoint_filter]
    intro w _ h1 h2
    omega
  rw [hf, Finset.card_union_of_disjoint hdisj]

/-- Strict monotonicity of `cntB`: an element of the complement lying in `[m, m')` forces a
strict increase. -/
lemma cntB_lt_cntB {n : ℕ} (A : Finset (Fin n)) (m m' : ℕ) (h : m < m')
    (t : Fin n) (ht : t ∉ A) (h1 : m ≤ t.val) (h2 : t.val < m') :
    cntB A m < cntB A m' := by
  have hsub : ((Finset.univ \ A).filter (fun i : Fin n => i.val < m)) ⊂
      ((Finset.univ \ A).filter (fun i : Fin n => i.val < m')) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, lt_trans hi.2 h⟩
    · intro hcon
      have ht' : t ∈ (Finset.univ \ A).filter (fun i : Fin n => i.val < m) := by
        rw [hcon]
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ht⟩, h2⟩
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ht'
      omega
  rw [cntB, cntB]
  exact Finset.card_lt_card hsub

theorem cntB_cross {n : ℕ} (A : Finset (Fin (n + 1))) (q : Fin n)
    (hq : q.castSucc ∉ A) (hq' : q.succ ∉ A) (j : Fin n) :
    cntB (delPosP A q.succ) j.val ≥ cntB A q.succ.val ↔ (q : ℕ) < (j : ℕ) := by
  have hqv : q.succ.val = q.val + 1 := rfl
  have hcv : q.castSucc.val = q.val := rfl
  by_cases hj : (j : ℕ) ≤ (q : ℕ)
  · have hle : cntB (delPosP A q.succ) j.val = cntB A j.val :=
      cntB_delPosP_of_le A q.succ j.val (by omega)
    have hlt : cntB A j.val < cntB A q.succ.val :=
      cntB_lt_cntB A j.val q.succ.val (by omega) q.castSucc hq (by omega) (by omega)
    constructor
    · intro h; omega
    · intro h; omega
  · have hge : cntB (delPosP A q.succ) j.val = cntB A q.succ.val +
        ((Finset.univ \ A).filter
          (fun w : Fin (n + 1) => q.succ.val < w.val ∧ w.val ≤ j.val)).card :=
      cntB_delPosP_of_ge A q.succ j.val (by omega)
    constructor
    · intro h; omega
    · intro h; omega

end Work.Cohomology.EZG
