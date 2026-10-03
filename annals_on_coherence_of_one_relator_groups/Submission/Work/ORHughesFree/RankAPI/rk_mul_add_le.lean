import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin

set_option autoImplicit false

namespace Work.ORHughesFree.RankAPI

open Matrix Work.ORHughesFree

/-- The exchange equivalence `Fin (a+b) ≃ Fin (b+a)` interchanging the two summands. -/
def swapFin (a b : ℕ) : Fin (a + b) ≃ Fin (b + a) :=
  Equiv.trans (Equiv.symm (finSumFinEquiv (m := a) (n := b)))
    (Equiv.trans (Equiv.sumComm (Fin a) (Fin b))
      (finSumFinEquiv (m := b) (n := a)))

/-- The block matrix `[[A, B], [C, D]]`, with the block rows/columns normalized to `Fin`. -/
def blk {R : Type*} {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin n) (Fin q) R)
    (C : Matrix (Fin p) (Fin m) R) (D : Matrix (Fin p) (Fin q) R) :
    Matrix (Fin (n + p)) (Fin (m + q)) R :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Negating a matrix does not change its rank. -/
theorem rk_neg {R : Type*} [Ring R] (rk : SylvesterRank R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : rk.rk n m (-A) = rk.rk n m A := by
  have h := SylvesterRank.rk_eq_of_left_inverse_mul rk (-1 : Matrix (Fin n) (Fin n) R)
    (-1 : Matrix (Fin n) (Fin n) R) (by simp) A
  simpa [Matrix.neg_mul, Matrix.one_mul] using h

/-- If a matrix is zero outside the rows indexed by `e` and the columns indexed by `f`
(with `e`, `f` injective), its rank is at most the rank of the corresponding submatrix. -/
theorem rk_le_of_support_submatrix {R : Type*} [Ring R] (rk : SylvesterRank R)
    {N K t s : ℕ} (e : Fin t → Fin N) (f : Fin s → Fin K)
    (he : Function.Injective e) (hf : Function.Injective f)
    (M : Matrix (Fin N) (Fin K) R)
    (hrow : ∀ i, i ∉ Set.range e → ∀ j, M i j = 0)
    (hcol : ∀ j, j ∉ Set.range f → ∀ i, M i j = 0) :
    rk.rk N K M ≤ rk.rk t s (M.submatrix e f) := by
  have hA : M = colSel (R := R) e * (M.submatrix e id) := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hi
      rw [Finset.sum_eq_single a]
      · simp [colSel]
      · intro b _ hb
        have hne : ¬ (e a = e b) := fun h => hb (he h).symm
        simp [colSel, hne]
      · intro h; exact absurd (Finset.mem_univ a) h
    · have hne : ∀ a : Fin t, ¬ (i = e a) := fun a h => hi ⟨a, h.symm⟩
      have hterm : ∀ a : Fin t, colSel (R := R) e i a * (M.submatrix e id) a j = 0 := by
        intro a; simp [colSel, hne a]
      rw [Finset.sum_eq_zero (fun a _ => hterm a)]
      exact hrow i hi j
  have hB : M.submatrix e id = (M.submatrix e f) * rowSel (R := R) f := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hj : j ∈ Set.range f
    · obtain ⟨l, hl⟩ := hj
      rw [Finset.sum_eq_single l]
      · simp [Matrix.submatrix_apply, rowSel, hl]
      · intro b _ hb
        have hne : f b ≠ j := fun h => hb (hf (by rw [h, hl]))
        simp [rowSel, hne]
      · intro h; exact absurd (Finset.mem_univ l) h
    · have hsum : (∑ b, (M.submatrix e f) i b * rowSel (R := R) f b j) = 0 := by
        rw [Finset.sum_eq_zero]
        intro b _
        have hne : f b ≠ j := fun h => hj ⟨b, h⟩
        simp [rowSel, hne]
      rw [hsum, Matrix.submatrix_apply]
      exact hcol j hj (e i)
  have hdecomp : M = colSel (R := R) e * (M.submatrix e f * rowSel (R := R) f) := by
    calc M = colSel (R := R) e * (M.submatrix e id) := hA
      _ = colSel (R := R) e * (M.submatrix e f * rowSel (R := R) f) := by rw [hB]
  calc rk.rk N K M
      = rk.rk N K (colSel (R := R) e * (M.submatrix e f * rowSel (R := R) f)) :=
        congrArg (fun X => rk.rk N K X) hdecomp
    _ ≤ rk.rk t K (M.submatrix e f * rowSel (R := R) f) := rk.rk_mul_le_right _ _
    _ ≤ rk.rk t s (M.submatrix e f) := rk.rk_mul_le_left _ _

/-- Reindexing `blockUpperFin X Y 1` along the block-exchange equivalences gives `blk Y 0 1 X`,
so the two matrices have the same rank. -/
theorem rk_blockUpperFin_eq_rk_blk {R : Type*} [Ring R] (rk : SylvesterRank R) {n m k : ℕ}
    (X : Matrix (Fin m) (Fin k) R) (Y : Matrix (Fin n) (Fin m) R) :
    rk.rk (m + n) (k + m) (blockUpperFin X Y (1 : Matrix (Fin m) (Fin m) R))
      = rk.rk (n + m) (m + k) (blk Y (0 : Matrix (Fin n) (Fin k) R)
          (1 : Matrix (Fin m) (Fin m) R) X) := by
  have hre : Matrix.reindex (swapFin m n) (swapFin k m)
      (blockUpperFin X Y (1 : Matrix (Fin m) (Fin m) R))
      = blk Y (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R) X := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, blk, blockUpperFin, swapFin,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.sumComm_symm]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂]
  have h := rk_reindex rk (swapFin m n) (swapFin k m)
    (blockUpperFin X Y (1 : Matrix (Fin m) (Fin m) R))
  rw [hre] at h
  exact h.symm

/-- The block-upper-triangular matrix `[[1, -X], [0, 1]]` is a right inverse of `[[1, X], [0, 1]]`. -/
theorem blockUpperFin_neg_mul_self {R : Type*} [Ring R] {m k : ℕ}
    (X : Matrix (Fin m) (Fin k) R) :
    blockUpperFin (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin k) (Fin k) R) (-X)
      * blockUpperFin (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin k) (Fin k) R) X = 1 := by
  rw [blockUpperFin, blockUpperFin, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    add_neg_cancel]
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv (finSumFinEquiv.symm)

/-- Multiplying `blk Y 0 1 X` on the right by `[[1, -X], [0, 1]]` produces the block matrix
`[[Y, -YX], [1, 0]]`. -/
theorem blk_mul_blockUpperFin_neg {R : Type*} [Ring R] {n m k : ℕ}
    (X : Matrix (Fin m) (Fin k) R) (Y : Matrix (Fin n) (Fin m) R) :
    blk Y (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R) X
        * blockUpperFin (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin k) (Fin k) R) (-X)
      = blk Y (-(Y * X)) (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin k) R) := by
  rw [blk, blockUpperFin, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg,
    add_zero, neg_add_cancel, blk]

/-- `blk Y (-YX) 1 0` splits as the sum of `blk Y 0 1 0` (the terms involving `Y` and `1_m`)
and `blk 0 (-YX) 0 0` (the terms involving `YX`). -/
theorem blk_add_split {R : Type*} [Ring R] {n m k : ℕ}
    (X : Matrix (Fin m) (Fin k) R) (Y : Matrix (Fin n) (Fin m) R) :
    blk Y (-(Y * X)) (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin k) R)
      = blk Y (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R)
          (0 : Matrix (Fin m) (Fin k) R)
        + blk (0 : Matrix (Fin n) (Fin m) R) (-(Y * X)) (0 : Matrix (Fin m) (Fin m) R)
          (0 : Matrix (Fin m) (Fin k) R) := by
  ext i j
  simp only [blk, Matrix.submatrix_apply]
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

/-- The matrix `blk Y 0 1 0 = [[Y, 0], [1_m, 0]]` has rank at most `m`. -/
theorem rk_blk_Y_0_1_0_le {R : Type*} [Ring R] (rk : SylvesterRank R) {n m k : ℕ}
    (Y : Matrix (Fin n) (Fin m) R) :
    rk.rk (n + m) (m + k)
        (blk Y (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R)
          (0 : Matrix (Fin m) (Fin k) R)) ≤ (m : ℝ) := by
  refine le_trans (rk_le_of_support_submatrix rk (e := id) (f := Fin.castAdd k)
    Function.injective_id (Fin.castAdd_injective m k) _ ?_ ?_) (rk_le_right rk _)
  · intro i hi
    exact absurd ⟨i, rfl⟩ hi
  · intro j hj i
    cases i using Fin.addCases with
    | left i' =>
      cases j using Fin.addCases with
      | left j' => exact absurd ⟨j', rfl⟩ hj
      | right j'' =>
        simp only [blk, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    | right i'' =>
      cases j using Fin.addCases with
      | left j' => exact absurd ⟨j', rfl⟩ hj
      | right j'' =>
        simp only [blk, Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

/-- The matrix `blk 0 (-YX) 0 0 = [[0, -YX], [0, 0]]` has rank at most `rk (YX)`. -/
theorem rk_blk_0_negYX_0_0_le {R : Type*} [Ring R] (rk : SylvesterRank R) {n m k : ℕ}
    (X : Matrix (Fin m) (Fin k) R) (Y : Matrix (Fin n) (Fin m) R) :
    rk.rk (n + m) (m + k)
        (blk (0 : Matrix (Fin n) (Fin m) R) (-(Y * X)) (0 : Matrix (Fin m) (Fin m) R)
          (0 : Matrix (Fin m) (Fin k) R)) ≤ rk.rk n k (Y * X) := by
  have hsub : (blk (0 : Matrix (Fin n) (Fin m) R) (-(Y * X)) (0 : Matrix (Fin m) (Fin m) R)
        (0 : Matrix (Fin m) (Fin k) R)).submatrix (Fin.castAdd m) (Fin.natAdd m)
      = -(Y * X) := by
    ext i j
    simp only [blk, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]
  calc rk.rk (n + m) (m + k)
        (blk (0 : Matrix (Fin n) (Fin m) R) (-(Y * X)) (0 : Matrix (Fin m) (Fin m) R)
          (0 : Matrix (Fin m) (Fin k) R))
      ≤ rk.rk n k ((blk (0 : Matrix (Fin n) (Fin m) R) (-(Y * X))
          (0 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin k) R)).submatrix
            (Fin.castAdd m) (Fin.natAdd m)) :=
        rk_le_of_support_submatrix rk (Fin.castAdd m) (Fin.natAdd m)
          (Fin.castAdd_injective n m) (Fin.natAdd_injective k m) _ ?_ ?_
    _ = rk.rk n k (-(Y * X)) := by rw [hsub]
    _ = rk.rk n k (Y * X) := rk_neg rk (Y * X)
  · intro i hi j
    cases i using Fin.addCases with
    | left i' => exact absurd ⟨i', rfl⟩ hi
    | right i'' =>
      cases j using Fin.addCases with
      | left j' =>
        simp only [blk, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      | right j'' =>
        simp only [blk, Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · intro j hj i
    cases j using Fin.addCases with
    | right j'' => exact absurd ⟨j'', rfl⟩ hj
    | left j' =>
      cases i using Fin.addCases with
      | left i' =>
        simp only [blk, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
          Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      | right i'' =>
        simp only [blk, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem rk_mul_add_le {R : Type*} [Ring R] (rk : SylvesterRank R) {n m k : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) : rk.rk n m A + rk.rk m k B ≤ rk.rk n k (A * B) + (m : ℝ) := by
  have hprod := blk_mul_blockUpperFin_neg (R := R) (n := n) B A
  have hsplit := blk_add_split (R := R) (n := n) B A
  have hinv := blockUpperFin_neg_mul_self (R := R) (m := m) (k := k) B
  have hkey : rk.rk (n + m) (m + k)
      (blk A (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R) B)
      ≤ rk.rk n k (A * B) + (m : ℝ) := by
    calc rk.rk (n + m) (m + k)
          (blk A (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R) B)
        = rk.rk (n + m) (m + k) (blk A (0 : Matrix (Fin n) (Fin k) R)
            (1 : Matrix (Fin m) (Fin m) R) B
            * blockUpperFin (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin k) (Fin k) R) (-B)) :=
          (SylvesterRank.rk_eq_of_mul_right_inverse rk _
            (blockUpperFin (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin k) (Fin k) R) (-B))
            (blockUpperFin (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin k) (Fin k) R) B) hinv).symm
      _ = rk.rk (n + m) (m + k)
            (blk A (-(A * B)) (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin k) R)) := by
            rw [hprod]
      _ = rk.rk (n + m) (m + k)
            (blk A (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R)
                (0 : Matrix (Fin m) (Fin k) R)
              + blk (0 : Matrix (Fin n) (Fin m) R) (-(A * B))
                (0 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin k) R)) := by
            rw [hsplit]
      _ ≤ rk.rk (n + m) (m + k)
            (blk A (0 : Matrix (Fin n) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R)
              (0 : Matrix (Fin m) (Fin k) R))
          + rk.rk (n + m) (m + k)
            (blk (0 : Matrix (Fin n) (Fin m) R) (-(A * B))
              (0 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin k) R)) :=
          rk_add_le rk _ _
      _ ≤ (m : ℝ) + rk.rk n k (A * B) :=
          add_le_add (rk_blk_Y_0_1_0_le rk A) (rk_blk_0_negYX_0_0_le rk B A)
      _ = rk.rk n k (A * B) + (m : ℝ) := by ring
  have h1 : rk.rk m k B + rk.rk n m A
      ≤ rk.rk (m + n) (k + m) (blockUpperFin B A (1 : Matrix (Fin m) (Fin m) R)) :=
    rk.rk_blockUpper B A 1
  have h2 := rk_blockUpperFin_eq_rk_blk (R := R) rk B A
  linarith [h1, h2, hkey]

end Work.ORHughesFree.RankAPI
