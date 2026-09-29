import Mathlib
import Submission.Work.TMC14Core.cycSetup

/-!
# `smMat_det`: the shooting determinant equals the cyclic determinant

For an arbitrary diagonal `d : ℕ → ℂ` and twist `t : ℂ` we prove

  `det (smMat Q d t) = det (cycMat Q d t)`

for every `Q ≥ 2` (and, directly, for `Q = 1`).

The proof is the classical Schur-complement computation:

* Replace row `2` of `smMat Q` by `row 2 - row 0`, and row `Q+1` by `row Q+1 - row 1`
  (two elementary row operations, determinant unchanged).  The resulting matrix `red`
  has column `0` equal to `e_0`, column `Q+1` equal to `e_1`, and its restriction to
  rows `2 … Q+1` and columns `1 … Q` is exactly `-(cycMat Q d t)`.
* Expanding once along column `0` and once along the last column (each having a single
  non-zero entry) contributes `(-1)^Q`, and `det (-(cycMat Q d t)) = (-1)^Q det (cycMat Q d t)`,
  so the two signs cancel.

This is the "Schur complement" step used in `blochDet`.
-/

set_option maxHeartbeats 4000000

open Matrix

namespace Work.TMC14Core



/-! ## 1. Entries of `smMat` by row and by column -/

lemma smMat_row0_apply (Q : ℕ) (d : ℕ → ℂ) (t : ℂ) (j : Fin (Q+2)) :
    smMat Q d t ⟨0, by omega⟩ j
      = (if j.val = 0 then (1:ℂ) else 0) + (if j.val = Q then -t⁻¹ else 0) := by
  simp only [smMat, Matrix.of_apply]
  split_ifs <;> simp_all <;> omega

lemma smMat_row1_apply (Q : ℕ) (d : ℕ → ℂ) (t : ℂ) (j : Fin (Q+2)) :
    smMat Q d t ⟨1, by omega⟩ j
      = (if j.val = 1 then -t else 0) + (if j.val = Q+1 then (1:ℂ) else 0) := by
  simp only [smMat, Matrix.of_apply]
  split_ifs <;> simp_all <;> omega

lemma smMat_row_ge2 (Q : ℕ) (d : ℕ → ℂ) (t : ℂ) (i j : Fin (Q+2)) (hi : 2 ≤ i.val) :
    smMat Q d t i j
      = (if j.val + 2 = i.val then (1:ℂ) else 0) + (if j.val + 1 = i.val then -d (i.val - 2) else 0)
        + (if j.val = i.val then (1:ℂ) else 0) := by
  simp only [smMat, Matrix.of_apply]
  rw [if_neg (by omega : ¬ (i.val = 0 ∧ j.val = 0)),
      if_neg (by omega : ¬ (i.val = 0 ∧ j.val = Q)),
      if_neg (by omega : ¬ (i.val = 1 ∧ j.val = 1)),
      if_neg (by omega : ¬ (i.val = 1 ∧ j.val = Q + 1))]
  simp only [hi, true_and]
  ring

lemma smMat_col0 (Q : ℕ) (hQ : 1 ≤ Q) (d : ℕ → ℂ) (t : ℂ) (i : Fin (Q+2)) :
    smMat Q d t i ⟨0, by omega⟩
      = (if i.val = 0 then (1:ℂ) else 0) + (if i.val = 2 then (1:ℂ) else 0) := by
  simp only [smMat, Matrix.of_apply, and_true]
  rw [if_neg (by omega : ¬ (↑i = 0 ∧ 0 = Q)),
      if_neg (by omega : ¬ (↑i = 1 ∧ 0 = 1)),
      if_neg (by omega : ¬ (↑i = 1 ∧ 0 = Q + 1)),
      if_neg (by omega : ¬ (2 ≤ ↑i ∧ 0 + 1 = ↑i)),
      if_neg (by omega : ¬ (2 ≤ ↑i ∧ 0 = ↑i))]
  simp only [show (2 ≤ (↑i : ℕ) ∧ 0 + 2 = ↑i) ↔ (↑i = 2) by omega]
  ring

lemma smMat_colLast (Q : ℕ) (hQ : 1 ≤ Q) (d : ℕ → ℂ) (t : ℂ) (i : Fin (Q+2)) :
    smMat Q d t i ⟨Q+1, by omega⟩
      = (if i.val = 1 then (1:ℂ) else 0) + (if i.val = Q+1 then (1:ℂ) else 0) := by
  simp only [smMat, Matrix.of_apply]
  rw [if_neg (by omega : ¬ (↑i = 0 ∧ Q+1 = 0)),
      if_neg (by omega : ¬ (↑i = 0 ∧ Q+1 = Q)),
      if_neg (by omega : ¬ (↑i = 1 ∧ Q+1 = 1)),
      if_neg (by omega : ¬ (2 ≤ ↑i ∧ Q+1+2 = ↑i)),
      if_neg (by omega : ¬ (2 ≤ ↑i ∧ Q+1+1 = ↑i))]
  simp only [and_true, show (2 ≤ (↑i:ℕ) ∧ Q+1 = ↑i) ↔ (↑i = Q+1) by omega]
  ring

/-! ## 2. The row-reduced matrix -/

/-- `smMat Q` with row `2` replaced by `row 2 - row 0` and row `Q+1` by `row Q+1 - row 1`. -/
noncomputable def red (Q : ℕ) (hQ : 2 ≤ Q) (d : ℕ → ℂ) (t : ℂ) :
    Matrix (Fin (Q+2)) (Fin (Q+2)) ℂ :=
  ((smMat Q d t).updateRow ⟨2, by omega⟩
      ((smMat Q d t) ⟨2, by omega⟩ + (-1 : ℂ) • (smMat Q d t) ⟨0, by omega⟩)).updateRow ⟨Q+1, by omega⟩
    (((smMat Q d t).updateRow ⟨2, by omega⟩
      ((smMat Q d t) ⟨2, by omega⟩ + (-1 : ℂ) • (smMat Q d t) ⟨0, by omega⟩)) ⟨Q+1, by omega⟩
     + (-1 : ℂ) • ((smMat Q d t).updateRow ⟨2, by omega⟩
      ((smMat Q d t) ⟨2, by omega⟩ + (-1 : ℂ) • (smMat Q d t) ⟨0, by omega⟩)) ⟨1, by omega⟩)

lemma red_apply (Q : ℕ) (hQ : 2 ≤ Q) (d : ℕ → ℂ) (t : ℂ) (i j : Fin (Q+2)) :
    red Q hQ d t i j =
      (if i = (⟨Q+1, by omega⟩ : Fin (Q+2)) then
          smMat Q d t ⟨Q+1, by omega⟩ j - smMat Q d t ⟨1, by omega⟩ j
       else if i = (⟨2, by omega⟩ : Fin (Q+2)) then
          smMat Q d t ⟨2, by omega⟩ j - smMat Q d t ⟨0, by omega⟩ j
       else smMat Q d t i j) := by
  simp only [red, Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply]
  rw [if_neg (by simp only [Fin.ext_iff]; omega :
        ¬ ((⟨Q+1, by omega⟩ : Fin (Q+2)) = ⟨2, by omega⟩)),
      if_neg (by simp only [Fin.ext_iff]; omega :
        ¬ ((⟨1, by omega⟩ : Fin (Q+2)) = ⟨2, by omega⟩))]
  split_ifs with h1 h2 <;> simp_all <;> ring

/-- Column `0` of `red` is `e_0`. -/
lemma red_col0 (Q : ℕ) (hQ : 2 ≤ Q) (d : ℕ → ℂ) (t : ℂ) (i : Fin (Q+2)) :
    red Q hQ d t i (0 : Fin (Q+2)) = (if i = (0 : Fin (Q+2)) then 1 else 0) := by
  rw [show (0 : Fin (Q+2)) = (⟨0, by omega⟩ : Fin (Q+2)) from rfl]
  have hS1 : smMat Q d t (⟨Q+1, by omega⟩ : Fin (Q+2)) ⟨0, by omega⟩ = 0 := by
    rw [smMat_col0 Q (by omega)]
    rw [if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨Q+1, by omega⟩:Fin (Q+2)).val = 0)),
        if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨Q+1, by omega⟩:Fin (Q+2)).val = 2))]
    ring
  have hS2 : smMat Q d t (⟨1, by omega⟩ : Fin (Q+2)) ⟨0, by omega⟩ = 0 := by
    rw [smMat_col0 Q (by omega)]
    rw [if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨1, by omega⟩:Fin (Q+2)).val = 0)),
        if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨1, by omega⟩:Fin (Q+2)).val = 2))]
    ring
  have hS3 : smMat Q d t (⟨2, by omega⟩ : Fin (Q+2)) ⟨0, by omega⟩ = 1 := by
    rw [smMat_col0 Q (by omega)]
    rw [if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨2, by omega⟩:Fin (Q+2)).val = 0)),
        if_pos (by simp only [Fin.val_mk])]
    ring
  have hS0 : smMat Q d t (⟨0, by omega⟩ : Fin (Q+2)) ⟨0, by omega⟩ = 1 := by
    rw [smMat_col0 Q (by omega)]
    rw [if_pos (by simp only [Fin.val_mk]),
        if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨0, by omega⟩:Fin (Q+2)).val = 2))]
    ring
  rw [red_apply, hS1, hS2, hS3, hS0]
  simp only [sub_self, Fin.ext_iff, Fin.val_mk]
  rw [smMat_col0 Q (by omega)]
  split_ifs <;> (first | (exfalso; omega) | omega | norm_num | ring)

/-- Column `Q+1` of `red` is `e_1`. -/
lemma red_colLast (Q : ℕ) (hQ : 2 ≤ Q) (d : ℕ → ℂ) (t : ℂ) (i : Fin (Q+2)) :
    red Q hQ d t i (⟨Q+1, by omega⟩ : Fin (Q+2))
      = (if i = (⟨1, by omega⟩ : Fin (Q+2)) then 1 else 0) := by
  have hS1 : smMat Q d t (⟨Q+1, by omega⟩ : Fin (Q+2)) ⟨Q+1, by omega⟩ = 1 := by
    rw [smMat_colLast Q (by omega)]
    rw [if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨Q+1, by omega⟩:Fin (Q+2)).val = 1)),
        if_pos (by simp only [Fin.val_mk])]
    ring
  have hS2 : smMat Q d t (⟨1, by omega⟩ : Fin (Q+2)) ⟨Q+1, by omega⟩ = 1 := by
    rw [smMat_colLast Q (by omega)]
    rw [if_pos (by simp only [Fin.val_mk]),
        if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨1, by omega⟩:Fin (Q+2)).val = Q+1))]
    ring
  have hS3 : smMat Q d t (⟨2, by omega⟩ : Fin (Q+2)) ⟨Q+1, by omega⟩ = 0 := by
    rw [smMat_colLast Q (by omega)]
    rw [if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨2, by omega⟩:Fin (Q+2)).val = 1)),
        if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨2, by omega⟩:Fin (Q+2)).val = Q+1))]
    ring
  have hS0 : smMat Q d t (⟨0, by omega⟩ : Fin (Q+2)) ⟨Q+1, by omega⟩ = 0 := by
    rw [smMat_colLast Q (by omega)]
    rw [if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨0, by omega⟩:Fin (Q+2)).val = 1)),
        if_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨0, by omega⟩:Fin (Q+2)).val = Q+1))]
    ring
  rw [red_apply, hS1, hS2, hS3, hS0]
  simp only [sub_self, Fin.ext_iff, Fin.val_mk]
  rw [smMat_colLast Q (by omega)]
  split_ifs <;> (first | (exfalso; omega) | omega | norm_num | ring)

/-- On the "interior" block (rows `2 … Q+1`, columns `1 … Q`), `red` is `-(cycMat Q d t)`. -/
lemma red_block (Q : ℕ) (hQ : 2 ≤ Q) (d : ℕ → ℂ) (t : ℂ) (a b : Fin Q) :
    red Q hQ d t (⟨a.val + 2, by omega⟩ : Fin (Q+2)) (⟨b.val + 1, by omega⟩ : Fin (Q+2))
      = - (cycMat Q d t) a b := by
  rw [red_apply]
  simp only [Fin.ext_iff]
  rw [smMat_row_ge2 Q d t (⟨Q+1, by omega⟩ : Fin (Q+2)) ⟨b.val+1, by omega⟩
        (by show 2 ≤ Q+1; omega),
      smMat_row1_apply Q d t ⟨b.val+1, by omega⟩,
      smMat_row_ge2 Q d t (⟨2, by omega⟩ : Fin (Q+2)) ⟨b.val+1, by omega⟩
        (by show 2 ≤ 2; omega),
      smMat_row0_apply Q d t ⟨b.val+1, by omega⟩,
      smMat_row_ge2 Q d t (⟨a.val+2, by omega⟩ : Fin (Q+2)) ⟨b.val+1, by omega⟩
        (by show 2 ≤ a.val+2; omega)]
  simp only [cycMat, Matrix.of_apply]
  split_ifs
  all_goals (try (first | (exfalso; omega) | omega | ring | norm_num))
  all_goals (first | (congr 1; congr 1; omega) | skip)

theorem smMat_det_gen (Q : ℕ) (hQ : 2 ≤ Q) (d : ℕ → ℂ) (t : ℂ) :
    (smMat Q d t).det = (cycMat Q d t).det := by
  have hrow : (red Q hQ d t).det = (smMat Q d t).det := by
    have h2 := Matrix.det_updateRow_add_smul_self
      ((smMat Q d t).updateRow ⟨2, by omega⟩
        ((smMat Q d t) ⟨2, by omega⟩ + (-1 : ℂ) • (smMat Q d t) ⟨0, by omega⟩))
      (i := (⟨Q+1, by omega⟩ : Fin (Q+2))) (j := (⟨1, by omega⟩ : Fin (Q+2)))
      (by simp only [ne_eq, Fin.ext_iff]; omega) (-1)
    have h1 := Matrix.det_updateRow_add_smul_self (smMat Q d t)
      (i := (⟨2, by omega⟩ : Fin (Q+2))) (j := (⟨0, by omega⟩ : Fin (Q+2)))
      (by simp only [ne_eq, Fin.ext_iff]; omega) (-1)
    simpa only [red] using h2.trans h1
  have hN : (red Q hQ d t).det
      = ((red Q hQ d t).submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_column_zero (red Q hQ d t),
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (Q+2))]
    · rw [red_col0, if_pos (by rfl),
        show (⟨0, by omega⟩ : Fin (Q+2)).succAbove = Fin.succ from Fin.succAbove_zero]
      simp
    · intro b _ hb
      rw [red_col0 Q (by omega) d t b, if_neg (by simpa using hb)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hlast : ∀ b : Fin (Q+1),
      (red Q hQ d t).submatrix Fin.succ Fin.succ b (Fin.last Q)
        = (if b = (⟨0, by omega⟩ : Fin (Q+1)) then 1 else 0) := by
    intro b
    have hiff : (Fin.succ b = (⟨1, by omega⟩ : Fin (Q+2))) ↔ (b = (⟨0, by omega⟩ : Fin (Q+1))) := by
      constructor
      · intro h
        have h' : (Fin.succ b).val = (⟨1, by omega⟩ : Fin (Q+2)).val := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_mk] at h'
        exact Fin.ext (by simp only [Fin.val_mk]; omega)
      · intro h; rw [h]; rfl
    show red Q hQ d t (Fin.succ b) (⟨Q+1, by omega⟩ : Fin (Q+2))
        = (if b = (⟨0, by omega⟩ : Fin (Q+1)) then 1 else 0)
    rw [red_colLast]
    simp only [hiff]
  have hB : ((red Q hQ d t).submatrix Fin.succ Fin.succ).det
      = (-1)^Q * (((red Q hQ d t).submatrix Fin.succ Fin.succ).submatrix Fin.succ
          Fin.castSucc).det := by
    rw [Matrix.det_succ_column _ (Fin.last Q),
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (Q+1))]
    · rw [hlast, if_pos (by rfl),
        show (⟨0, by omega⟩ : Fin (Q+1)).succAbove = Fin.succ from Fin.succAbove_zero,
        show (Fin.last Q).succAbove = Fin.castSucc from Fin.succAbove_last]
      simp
    · intro b _ hb
      rw [hlast b, if_neg hb]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hBmat : ((red Q hQ d t).submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.castSucc
      = -(cycMat Q d t) := by
    ext a b
    show red Q hQ d t (⟨a.val + 2, by omega⟩ : Fin (Q+2))
        (⟨b.val + 1, by omega⟩ : Fin (Q+2)) = -(cycMat Q d t) a b
    rw [red_block]
  have hdetB : (((red Q hQ d t).submatrix Fin.succ Fin.succ).submatrix Fin.succ
        Fin.castSucc).det
      = (-1)^Q * (cycMat Q d t).det := by
    rw [hBmat, Matrix.det_neg]
    simp [Fintype.card_fin]
  have hsign : (-1 : ℂ)^Q * (-1)^Q = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨Q, by ring⟩
  rw [← hrow, hN, hB, hdetB, ← mul_assoc, hsign, one_mul]


/-! ## 4. The `Q = 1` case and the requested statement -/

theorem smMat_det_one (d : ℕ → ℂ) (t : ℂ) :
    (smMat 1 d t).det = (cycMat 1 d t).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_one]
  simp only [smMat, cycMat, Matrix.of_apply]
  norm_num
  ring

theorem smMat_det (q : ℕ) (d : ℕ → ℂ) (t : ℂ) :
    (Work.TMC14Core.smMat (q+1) d t).det = (Work.TMC14Core.cycMat (q+1) d t).det := by
  rcases q with _ | q
  · exact smMat_det_one d t
  · exact smMat_det_gen (q+2) (by omega) d t

end Work.TMC14Core
