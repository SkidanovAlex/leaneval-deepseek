import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_le_left

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Entrywise description of `blockDiagFam`. -/
lemma blockDiagFam_apply {U : Type} [Zero U] {a b k : ℕ}
    (B : Fin k → Matrix (Fin a) (Fin b) U) (x : Fin (k * a)) (y : Fin (k * b)) :
    blockDiagFam B x y = if x.divNat = y.divNat then B x.divNat x.modNat y.modNat else 0 := rfl

/-- The `Fin (k * a) ⊕ Fin a`-decomposition of `Fin ((k+1) * a)` given by
`Nat.succ_mul`, read off through `finSumFinEquiv`: the index `x` lies in the *last* block
(`Sum.inr`) exactly when `x.divNat` is the last element of `Fin (k+1)`, and otherwise it is the
`(x.divNat, x.modNat)` entry of `Fin k × Fin a`. -/
lemma finSumFinEquiv_symm_finCongr_succ_mul {a k : ℕ} (x : Fin ((k + 1) * a)) :
    finSumFinEquiv.symm (finCongr (Nat.succ_mul k a) x) =
      (if h : (x.divNat : ℕ) < k
        then Sum.inl (finProdFinEquiv (⟨(x.divNat : ℕ), h⟩, x.modNat) : Fin (k * a))
        else Sum.inr x.modNat) := by
  by_cases h : ((x.divNat : Fin (k + 1)) : ℕ) < k
  · rw [dif_pos h]
    rw [show Sum.inl (finProdFinEquiv (⟨(x.divNat : ℕ), h⟩, x.modNat) : Fin (k * a))
          = finSumFinEquiv.symm (finSumFinEquiv
              (Sum.inl (finProdFinEquiv (⟨(x.divNat : ℕ), h⟩, x.modNat) : Fin (k * a))))
        from (Equiv.symm_apply_apply _ _).symm]
    congr 1
    rw [finSumFinEquiv_apply_left]
    apply Fin.ext
    simp only [Fin.castAdd, Fin.castLE, finCongr_apply, Fin.val_cast, Equiv.coe_fn_mk,
      finProdFinEquiv, Fin.val_mk]
    have hkey : (x.val : ℕ) = x.modNat.val + a * (x.divNat : ℕ) := by
      have hx' : (x.val : ℕ) = a * (x.divNat : ℕ) + x.modNat.val := by
        have h1 : ((x.divNat : Fin (k + 1)) : ℕ) = x.val / a := rfl
        have h2 : ((x.modNat : Fin a) : ℕ) = x.val % a := rfl
        rw [h1, h2]; exact (Nat.div_add_mod x.val a).symm
      rw [hx', Nat.add_comm]
    exact hkey
  · rw [dif_neg h]
    rw [show Sum.inr x.modNat = finSumFinEquiv.symm (finSumFinEquiv (Sum.inr x.modNat))
          from (Equiv.symm_apply_apply _ _).symm]
    congr 1
    rw [finSumFinEquiv_apply_right]
    apply Fin.ext
    simp only [Fin.natAdd, finCongr_apply, Fin.val_cast, Fin.modNat, Fin.val_mk]
    have hdiv : x.val / a = k := by
      have := x.divNat.isLt
      have hd : ((x.divNat : Fin (k + 1)) : ℕ) = x.val / a := rfl
      omega
    have hkey : (x.val : ℕ) = k * a + x.modNat.val := by
      have hx' : (x.val : ℕ) = a * (x.val / a) + x.val % a := (Nat.div_add_mod x.val a).symm
      have hm : ((x.modNat : Fin a) : ℕ) = x.val % a := rfl
      have h1 : (x.val : ℕ) = a * k + x.modNat.val := by rw [hx', hdiv, hm]
      rw [h1, Nat.mul_comm a k]
    exact hkey

/-- `blockDiagFam` is the block diagonal, in the sense of `blockDiagFin`, of the first `k`
blocks and the last one, up to the raw identification `(k+1)*a = k*a + a` of the index sets. -/
lemma blockDiagFam_succ {U : Type} [Zero U] {a b k : ℕ}
    (B : Fin (k + 1) → Matrix (Fin a) (Fin b) U) :
    blockDiagFam B =
      Matrix.reindex (finCongr (Nat.succ_mul k a)).symm (finCongr (Nat.succ_mul k b)).symm
        (blockDiagFin (blockDiagFam (fun i => B i.castSucc)) (B (Fin.last k))) := by
  ext x y
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_symm, blockDiagFin, Matrix.submatrix_apply, blockDiagFam_apply]
  rw [finSumFinEquiv_symm_finCongr_succ_mul (a := a) x,
    finSumFinEquiv_symm_finCongr_succ_mul (a := b) y]
  by_cases hx : ((x.divNat : Fin (k + 1)) : ℕ) < k
  · rw [dif_pos hx]
    by_cases hy : ((y.divNat : Fin (k + 1)) : ℕ) < k
    · rw [dif_pos hy]
      by_cases hxy : x.divNat = y.divNat
      · rw [if_pos hxy, Matrix.fromBlocks_apply₁₁, blockDiagFam_apply,
          MatrixBlocks.finProdFinEquiv_fst, MatrixBlocks.finProdFinEquiv_snd,
          MatrixBlocks.finProdFinEquiv_fst, MatrixBlocks.finProdFinEquiv_snd]
        have hcond : (⟨(x.divNat : ℕ), hx⟩ : Fin k) = ⟨(y.divNat : ℕ), hy⟩ := by
          apply Fin.ext
          exact congrArg (fun z : Fin (k + 1) => (z : ℕ)) hxy
        rw [if_pos hcond]
        rw [show (⟨(x.divNat : ℕ), hx⟩ : Fin k).castSucc = x.divNat from Fin.ext rfl]
      · rw [if_neg hxy, Matrix.fromBlocks_apply₁₁, blockDiagFam_apply,
          MatrixBlocks.finProdFinEquiv_fst, MatrixBlocks.finProdFinEquiv_snd,
          MatrixBlocks.finProdFinEquiv_fst, MatrixBlocks.finProdFinEquiv_snd]
        have hcond : ¬ ((⟨(x.divNat : ℕ), hx⟩ : Fin k) = ⟨(y.divNat : ℕ), hy⟩) := by
          intro heq
          exact hxy (Fin.ext (congrArg (fun z : Fin k => (z : ℕ)) heq))
        rw [if_neg hcond]
    · rw [dif_neg hy]
      by_cases hxy : x.divNat = y.divNat
      · exfalso
        exact absurd (show ((y.divNat : Fin (k + 1)) : ℕ) < k from by rw [← hxy]; exact hx) hy
      · rw [if_neg hxy, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [dif_neg hx]
    by_cases hy : ((y.divNat : Fin (k + 1)) : ℕ) < k
    · rw [dif_pos hy]
      by_cases hxy : x.divNat = y.divNat
      · exfalso
        exact absurd (show ((x.divNat : Fin (k + 1)) : ℕ) < k from by rw [hxy]; exact hy) hx
      · rw [if_neg hxy, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · rw [dif_neg hy]
      have hxl : x.divNat = Fin.last k := by
        apply Fin.ext
        rw [Fin.val_last]
        have := x.divNat.isLt
        omega
      by_cases hxy : x.divNat = y.divNat
      · rw [if_pos hxy, Matrix.fromBlocks_apply₂₂, hxl]
      · exfalso
        have hyl : y.divNat = Fin.last k := by
          apply Fin.ext
          rw [Fin.val_last]
          have := y.divNat.isLt
          omega
        exact absurd (by rw [hxl, hyl]) hxy

/-- The rank of a block diagonal matrix with `k` blocks is the sum of the ranks of its
blocks.  This is the generalisation of the block-diagonal axiom `(SMat3)` of a Sylvester rank
function from two blocks to an arbitrary finite family. -/
theorem rk_blockDiagFam {R : Type} [Ring R] (rk : SylvesterRank R) {a b k : ℕ}
    (B : Fin k → Matrix (Fin a) (Fin b) R) :
    rk.rk (k * a) (k * b) (blockDiagFam B) = ∑ r : Fin k, rk.rk a b (B r) := by
  revert B
  induction k with
  | zero =>
    intro B
    have h : rk.rk (0 * a) (0 * b) (blockDiagFam B) = 0 := by
      refine le_antisymm ?_ (rk.rk_nonneg _ _ _)
      calc rk.rk (0 * a) (0 * b) (blockDiagFam B) ≤ ((0 * a : ℕ) : ℝ) :=
            RankAPI.rk_le_left rk _
        _ = 0 := by simp
    rw [h]
    simp
  | succ k ih =>
    intro B
    rw [blockDiagFam_succ B]
    rw [RankAPI.rk_reindex rk (finCongr (Nat.succ_mul k a)).symm
        (finCongr (Nat.succ_mul k b)).symm
        (blockDiagFin (blockDiagFam (fun i => B i.castSucc)) (B (Fin.last k)))]
    rw [rk.rk_blockDiag]
    rw [ih (fun i => B i.castSucc)]
    rw [Fin.sum_univ_castSucc (fun r => rk.rk a b (B r))]

end Work.ORHughesFree.NaturalExtension
