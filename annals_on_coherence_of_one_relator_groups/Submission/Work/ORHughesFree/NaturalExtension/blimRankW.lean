import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.blim_add
import Submission.Work.ORHughesFree.NaturalExtension.blim_mono
import Submission.Work.ORHughesFree.NaturalExtension.blim_congr
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.RankAPI.rk_diagonal_eq_sum
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.MatrixBlocks.exists_sylvesterRank_matrix
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_exists

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORHughesFree.NaturalExtension

open Matrix
open Work.ORHughesFree.MatrixBlocks

/-! ## The `n`-th coordinate of `W U` as a ring homomorphism -/

/-- Evaluation of `W U = ∏_{n} M_{n+1}(U)` at the `n`-th coordinate, as a ring
homomorphism. -/
def evalW (U : Type) [Ring U] (n : ℕ) : W U →+* Matrix (Fin (n+1)) (Fin (n+1)) U where
  toFun := fun x => x n
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-- The `n`-th block flattening of a matrix over `W U` is the flattening of its `n`-th
coordinate. -/
lemma flatW_eq_map_evalW {U : Type} [Ring U] {k m : ℕ}
    (A : Matrix (Fin k) (Fin m) (W U)) (n : ℕ) :
    flatW k m A n = flattenBlocks (A.map (evalW U n)) := by
  ext i j
  rfl

lemma flatW_zero {U : Type} [Ring U] {k m : ℕ} (n : ℕ) :
    flatW k m (0 : Matrix (Fin k) (Fin m) (W U)) n = 0 := by
  ext i j
  simp [flatW, flattenBlocks]

lemma flatW_one {U : Type} [Ring U] (n : ℕ) :
    flatW 1 1 (1 : Matrix (Fin 1) (Fin 1) (W U)) n =
      Matrix.reindex ((finCongr (Nat.one_mul (n+1))).symm)
        ((finCongr (Nat.one_mul (n+1))).symm)
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) U) := by
  rw [flatW_eq_map_evalW]
  have h : (1 : Matrix (Fin 1) (Fin 1) (W U)).map (evalW U n)
      = oneByOne (1 : Matrix (Fin (n+1)) (Fin (n+1)) U) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.map_apply, Matrix.one_apply, oneByOne]
  rw [h, flattenBlocks_oneByOne]

lemma flatW_mul {U : Type} [Ring U] {k m p : ℕ} (A : Matrix (Fin k) (Fin m) (W U))
    (B : Matrix (Fin m) (Fin p) (W U)) (n : ℕ) :
    flatW k p (A * B) n = flatW k m A n * flatW m p B n := by
  rw [flatW_eq_map_evalW, flatW_eq_map_evalW, flatW_eq_map_evalW,
    Matrix.map_mul, flattenBlocks_mul]

lemma flatW_blockDiag {U : Type} [Ring U] {k l p q : ℕ} (A : Matrix (Fin k) (Fin l) (W U))
    (B : Matrix (Fin p) (Fin q) (W U)) (n : ℕ) :
    flatW (k+p) (l+q) (blockDiagFin A B) n =
      Matrix.reindex ((finCongr (Nat.add_mul k p (n+1))).symm)
        ((finCongr (Nat.add_mul l q (n+1))).symm)
        (blockDiagFin (flatW k l A n) (flatW p q B n)) := by
  rw [flatW_eq_map_evalW, blockDiagFin_map, flattenBlocks_blockDiagFin]
  rw [← flatW_eq_map_evalW A n, ← flatW_eq_map_evalW B n]

lemma flatW_blockUpper {U : Type} [Ring U] {k l p q : ℕ} (A : Matrix (Fin k) (Fin l) (W U))
    (B : Matrix (Fin p) (Fin q) (W U)) (C : Matrix (Fin k) (Fin q) (W U)) (n : ℕ) :
    flatW (k+p) (l+q) (blockUpperFin A B C) n =
      Matrix.reindex ((finCongr (Nat.add_mul k p (n+1))).symm)
        ((finCongr (Nat.add_mul l q (n+1))).symm)
        (blockUpperFin (flatW k l A n) (flatW p q B n) (flatW k q C n)) := by
  rw [flatW_eq_map_evalW, blockUpperFin_map, blockUpperFin_flattenBlocks]
  rw [← flatW_eq_map_evalW A n, ← flatW_eq_map_evalW B n, ← flatW_eq_map_evalW C n]

/-! ## The normalized flattened rank sequence and its boundedness -/

/-- The rank of the `n`-th block flattening of `A`, normalized by `n+1`. -/
noncomputable def rankSeqW {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    (k m : ℕ) (A : Matrix (Fin k) (Fin m) (W U)) : ℕ → ℝ :=
  fun n => rk.rk (k * (n+1)) (m * (n+1)) (flatW k m A n) / ((n+1 : ℕ) : ℝ)

@[simp] theorem blimRank_eq {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    (k m : ℕ) (A : Matrix (Fin k) (Fin m) (W U)) :
    blimRank ω rk k m A = blim ω (rankSeqW ω rk k m A) := rfl

theorem rankSeqW_nonneg {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    {k m : ℕ} (A : Matrix (Fin k) (Fin m) (W U)) (n : ℕ) :
    0 ≤ rankSeqW ω rk k m A n :=
  div_nonneg (rk.rk_nonneg _ _ _) (Nat.cast_nonneg _)

theorem abs_rankSeqW_le {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    {k m : ℕ} (A : Matrix (Fin k) (Fin m) (W U)) :
    ∀ n, |rankSeqW ω rk k m A n| ≤ max (k : ℝ) (m : ℝ) := by
  intro n
  have hpos : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  rw [abs_of_nonneg (rankSeqW_nonneg ω rk A n), rankSeqW, div_le_iff₀ hpos]
  calc rk.rk (k * (n+1)) (m * (n+1)) (flatW k m A n)
      ≤ ((k * (n+1) : ℕ) : ℝ) := RankAPI.rk_le_left rk _
    _ = (k : ℝ) * ((n+1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ max (k : ℝ) (m : ℝ) * ((n+1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem abs_rankSeqW_le_max {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    {k m N M : ℕ} (hk : k ≤ N) (hm : m ≤ M) (A : Matrix (Fin k) (Fin m) (W U)) :
    ∀ n, |rankSeqW ω rk k m A n| ≤ max (N : ℝ) (M : ℝ) :=
  fun n => le_trans (abs_rankSeqW_le ω rk A n)
    (max_le_max (Nat.cast_le.mpr hk) (Nat.cast_le.mpr hm))

/-! ## `blimRank` is a Sylvester rank function -/

theorem blimRankW {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U) :
    ∃ rk_W : SylvesterRank (W U), ∀ (k m : ℕ) (A : Matrix (Fin k) (Fin m) (W U)),
      rk_W.rk k m A = blimRank ω rk k m A := by
  refine ⟨{ rk := fun k m A => blimRank ω rk k m A,
            rk_nonneg := ?_,
            rk_zero := ?_,
            rk_one := ?_,
            rk_mul_le_left := ?_,
            rk_mul_le_right := ?_,
            rk_blockDiag := ?_,
            rk_blockUpper := ?_ }, ?_⟩
  · intro k m A
    rw [blimRank_eq]
    exact blim_nonneg ω (abs_rankSeqW_le ω rk A) (fun n => rankSeqW_nonneg ω rk A n)
  · intro k m
    rw [blimRank_eq]
    have h : rankSeqW ω rk k m (0 : Matrix (Fin k) (Fin m) (W U)) = fun _ => 0 := by
      funext n
      simp [rankSeqW, flatW_zero, rk.rk_zero]
    rw [h, blim_const]
  · rw [blimRank_eq]
    have h : rankSeqW ω rk 1 1 (1 : Matrix (Fin 1) (Fin 1) (W U)) = fun _ => 1 := by
      funext n
      rw [rankSeqW, flatW_one, RankAPI.rk_reindex, RankAPI.rk_one_fin]
      exact div_self (by positivity)
    rw [h, blim_const]
  · intro k m p A B
    rw [blimRank_eq, blimRank_eq]
    refine blim_mono ω (abs_rankSeqW_le ω rk (A * B))
      (abs_rankSeqW_le ω rk A) (fun n => ?_)
    rw [rankSeqW, rankSeqW, flatW_mul]
    exact div_le_div_of_nonneg_right (rk.rk_mul_le_left _ _) (Nat.cast_nonneg _)
  · intro k m p A B
    rw [blimRank_eq, blimRank_eq]
    refine blim_mono ω (abs_rankSeqW_le ω rk (A * B))
      (abs_rankSeqW_le ω rk B) (fun n => ?_)
    rw [rankSeqW, rankSeqW, flatW_mul]
    exact div_le_div_of_nonneg_right (rk.rk_mul_le_right _ _) (Nat.cast_nonneg _)
  · intro k l p q A B
    rw [blimRank_eq, blimRank_eq, blimRank_eq]
    have hpt : ∀ n, rankSeqW ω rk (k+p) (l+q) (blockDiagFin A B) n =
        rankSeqW ω rk k l A n + rankSeqW ω rk p q B n := by
      intro n
      rw [rankSeqW, rankSeqW, rankSeqW, flatW_blockDiag, RankAPI.rk_reindex,
        rk.rk_blockDiag, add_div]
    rw [funext hpt]
    exact blim_add ω
      (abs_rankSeqW_le_max ω rk (Nat.le_add_right k p) (Nat.le_add_right l q) A)
      (abs_rankSeqW_le_max ω rk (Nat.le_add_left p k) (Nat.le_add_left q l) B)
  · intro k l p q A B C
    rw [blimRank_eq, blimRank_eq, blimRank_eq]
    have hpt : ∀ n, rankSeqW ω rk k l A n + rankSeqW ω rk p q B n ≤
        rankSeqW ω rk (k+p) (l+q) (blockUpperFin A B C) n := by
      intro n
      rw [rankSeqW, rankSeqW, rankSeqW, flatW_blockUpper, RankAPI.rk_reindex, ← add_div]
      exact div_le_div_of_nonneg_right (rk.rk_blockUpper _ _ _) (Nat.cast_nonneg _)
    calc blim ω (rankSeqW ω rk k l A) + blim ω (rankSeqW ω rk p q B)
        = blim ω (rankSeqW ω rk k l A + rankSeqW ω rk p q B) :=
          (blim_add ω
            (abs_rankSeqW_le_max ω rk (Nat.le_add_right k p) (Nat.le_add_right l q) A)
            (abs_rankSeqW_le_max ω rk (Nat.le_add_left p k) (Nat.le_add_left q l) B)).symm
      _ ≤ blim ω (rankSeqW ω rk (k+p) (l+q) (blockUpperFin A B C)) :=
          blim_mono ω
            (M := max (k : ℝ) (l : ℝ) + max (p : ℝ) (q : ℝ))
            (fun n => le_trans (abs_add_le _ _) (add_le_add
              (abs_rankSeqW_le ω rk A n) (abs_rankSeqW_le ω rk B n)))
            (abs_rankSeqW_le ω rk (blockUpperFin A B C)) hpt
  · intro k m A
    rfl

end Work.ORHughesFree.NaturalExtension
