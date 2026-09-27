import Mathlib
import Submission.Work.Idx.WPenAppendDefs

/-!
# `Work.Idx.wPen_append_entry_facts`

The elementary entry facts relating the `z`-coefficient `wPenA X n d` of the W linearisation to
the two "coordinate" block matrices `Ecol`, `Erow` and to `BBl`, `rowb`, `wPenB`:

* `wPenA * Ecol = 0`, `Erow * wPenA = 0`, `Erow * Ecol = 1`;
* `wPenA * wPenA = wPenA` and `wPenA + Ecol * Erow = 1`;
* `wPenA * BBl + Ecol * rowb = wPenB`;
* `Erow * BBl = 0`.

Each is a finite matrix computation; the proofs unpack the `if`-valued entries and reduce the
`Finset.sum` over the block index to the single potentially non-zero term.
-/

open Matrix

namespace Work.Idx

/-- The last block `d` of `Fin (d+1)` is `dIdx d` exactly on the `d`-th coordinate. -/
lemma append_dIdx_eq_iff (d : ℕ) (a : Fin (d + 1)) :
    a = dIdx d ↔ (a : ℕ) = d :=
  ⟨fun h => congrArg Fin.val h, fun h => by ext; exact h⟩

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (n d : ℕ)

/-- The `z`-coefficient of the W linearisation annihilates the first `d` blocks, hence `Ecol`. -/
lemma wPenA_mul_Ecol : Work.KT.Idx.wPenA X n d * Ecol X n d = 0 := by
  ext i y
  simp only [Matrix.mul_apply, Work.Idx.wPenA_apply, Work.Idx.Ecol_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨dIdx d, y⟩ : WIdx n d)]
  · by_cases h : (i.1 : ℕ) = d
    · simp [h]
    · have h' : i.1 ≠ dIdx d := by intro hh; exact h (congrArg Fin.val hh)
      simp [h']
  · intro bb _ hb
    by_cases h1 : bb.1 = dIdx d
    · have h2 : ¬ (bb.2 = y) := fun h => hb (by ext <;> simp [h1, h])
      simp [h1, h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `Erow` selects the last (`d`-th) block, on which `wPenA` vanishes. -/
lemma Erow_mul_wPenA : Erow X n d * Work.KT.Idx.wPenA X n d = 0 := by
  ext x j
  simp only [Matrix.mul_apply, Work.Idx.wPenA_apply, Work.Idx.Erow_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨dIdx d, x⟩ : WIdx n d)]
  · simp [Work.Idx.dIdx_val]
  · intro bb _ hb
    by_cases h1 : bb.1 = dIdx d
    · have h2 : ¬ (x = bb.2) := fun h => hb (by ext <;> simp [h1, h])
      simp [h1, h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `Erow` is a left inverse to `Ecol`. -/
lemma Erow_mul_Ecol : Erow X n d * Ecol X n d = (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
  ext x y
  simp only [Matrix.mul_apply, Work.Idx.Erow_apply, Work.Idx.Ecol_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨dIdx d, x⟩ : WIdx n d)]
  · simp
  · intro bb _ hb
    by_cases h1 : bb.1 = dIdx d
    · have h2 : ¬ (x = bb.2) := by
        intro h; exact hb (by ext <;> simp [h1, h])
      simp [h1, h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `wPenA` is idempotent. -/
lemma wPenA_mul_self :
    Work.KT.Idx.wPenA X n d * Work.KT.Idx.wPenA X n d = Work.KT.Idx.wPenA X n d := by
  ext i j
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨i.1, i.2⟩ : WIdx n d)]
  · simp only [Work.Idx.wPenA_apply, Matrix.one_apply]
    by_cases h : (i.1 : ℕ) = d
    · simp [h]
    · simp [h]
  · intro k _ hk
    have h0 : Work.KT.Idx.wPenA X n d i k = 0 := by
      rw [Work.Idx.wPenA_apply]
      by_cases h1 : i.1 = k.1
      · by_cases h2 : (i.1 : ℕ) = d
        · simp [h2]
        · have h3 : ¬ (i.2 = k.2) := by intro h3; exact hk (by ext <;> simp [h1, h3])
          simp [h1, h2, h3, Matrix.one_apply]
      · simp [h1]
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `wPenA` and the last-block projection `Ecol * Erow` sum to the identity. -/
lemma wPenA_add_Ecol_mul_Erow :
    Work.KT.Idx.wPenA X n d + Ecol X n d * Erow X n d =
      (1 : Matrix (WIdx n d) (WIdx n d) C(X, ℂ)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (i.2 : Fin n)]
  · simp only [Work.Idx.wPenA_apply, Work.Idx.Ecol_apply, Work.Idx.Erow_apply]
    by_cases h1 : i.1 = j.1
    · by_cases h2 : i.2 = j.2
      · have hij : i = j := by ext <;> simp [h1, h2]
        by_cases h3 : (i.1 : ℕ) = d <;>
          simp_all [append_dIdx_eq_iff, hij, Matrix.one_apply, Prod.ext_iff]
      · by_cases h3 : (i.1 : ℕ) = d <;>
          simp_all [append_dIdx_eq_iff, Matrix.one_apply, Prod.ext_iff]
    · by_cases h2 : i.2 = j.2
      · by_cases h3 : (i.1 : ℕ) = d
        · have hj : ¬ ((j.1 : ℕ) = d) := fun h =>
            h1 (((append_dIdx_eq_iff d i.1).mpr h3).trans
              ((append_dIdx_eq_iff d j.1).mpr h).symm)
          simp_all [append_dIdx_eq_iff, hj, Matrix.one_apply, Prod.ext_iff]
        · simp_all [append_dIdx_eq_iff, Matrix.one_apply, Prod.ext_iff]
      · by_cases h3 : (i.1 : ℕ) = d <;>
          simp_all [append_dIdx_eq_iff, Matrix.one_apply, Prod.ext_iff]
  · intro y _ hyb
    have : ¬ (i.2 = y) := fun h => hyb h.symm
    simp [Work.Idx.Ecol_apply, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The entry identity behind the append step: `wPenA * BBl + Ecol * rowb = wPenB`. -/
lemma wPenA_mul_BBl_add_Ecol_mul_rowb
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Work.KT.Idx.wPenA X n d * BBl X n d + Ecol X n d * rowb X n d b =
      Work.KT.Idx.wPenB X n d b := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨i.1, i.2⟩ : WIdx n d)]
  · rw [Finset.sum_eq_single (i.2 : Fin n)]
    · by_cases h : (i.1 : ℕ) = d
      · have hi : i = (⟨dIdx d, i.2⟩ : WIdx n d) := by
          ext
          · simp [Work.Idx.dIdx_val, h]
          · rfl
        rw [hi]
        simp [Work.Idx.wPenA_apply, Work.Idx.BBl_apply, Work.Idx.Ecol_apply,
          Work.Idx.rowb_apply, Work.Idx.dIdx_val, Matrix.one_apply]
      · have he : ¬ (i.1 = dIdx d) := fun hh => h ((append_dIdx_eq_iff d i.1).mp hh)
        simp [Work.Idx.wPenA_apply, Work.Idx.BBl_apply, Work.Idx.Ecol_apply,
          Work.Idx.rowb_apply, Work.Idx.wPenB_apply, Work.Idx.dIdx_val, Matrix.one_apply, h, he]
    · intro y _ hyb
      have : ¬ (i.2 = y) := fun h => hyb h.symm
      simp [Work.Idx.Ecol_apply, this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    have h0 : Work.KT.Idx.wPenA X n d i k = 0 := by
      rw [Work.Idx.wPenA_apply]
      by_cases h1 : i.1 = k.1
      · by_cases h2 : (i.1 : ℕ) = d
        · simp [h2]
        · have h3 : ¬ (i.2 = k.2) := by intro h3; exact hk (by ext <;> simp [h1, h3])
          simp [h1, h2, h3, Matrix.one_apply]
      · simp [h1]
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `Erow` kills `BBl`: the superdiagonal does not reach the last block. -/
lemma Erow_mul_BBl : Erow X n d * BBl X n d = 0 := by
  ext x j
  simp only [Matrix.mul_apply, Work.Idx.BBl_apply, Work.Idx.Erow_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨dIdx d, x⟩ : WIdx n d)]
  · have hj : ¬ ((d : ℕ) + 1 = (j.1 : ℕ)) := by have := j.1.isLt; omega
    simp [Work.Idx.dIdx_val, hj]
  · intro bb _ hb
    by_cases h1 : bb.1 = dIdx d
    · have h2 : ¬ (x = bb.2) := fun h => hb (by ext <;> simp [h1, h])
      simp [h1, h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Work.Idx

namespace Work.Idx

theorem wPen_append_entry_facts (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Work.KT.Idx.wPenA X n d * Work.Idx.Ecol X n d = 0) ∧
    (Work.Idx.Erow X n d * Work.KT.Idx.wPenA X n d = 0) ∧
    (Work.Idx.Erow X n d * Work.Idx.Ecol X n d
        = (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) ∧
    (Work.KT.Idx.wPenA X n d * Work.KT.Idx.wPenA X n d = Work.KT.Idx.wPenA X n d) ∧
    (Work.KT.Idx.wPenA X n d + Work.Idx.Ecol X n d * Work.Idx.Erow X n d
        = (1 : Matrix (Work.Idx.WIdx n d) (Work.Idx.WIdx n d) C(X, ℂ))) ∧
    (Work.KT.Idx.wPenA X n d * Work.Idx.BBl X n d + Work.Idx.Ecol X n d * Work.Idx.rowb X n d b
        = Work.KT.Idx.wPenB X n d b) ∧
    (Work.Idx.Erow X n d * Work.Idx.BBl X n d = 0) := by
  exact ⟨wPenA_mul_Ecol X n d, Erow_mul_wPenA X n d, Erow_mul_Ecol X n d, wPenA_mul_self X n d,
    wPenA_add_Ecol_mul_Erow X n d, wPenA_mul_BBl_add_Ecol_mul_rowb X n d b, Erow_mul_BBl X n d⟩

end Work.Idx
