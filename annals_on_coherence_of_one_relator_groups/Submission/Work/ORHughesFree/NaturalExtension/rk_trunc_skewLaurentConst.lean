import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.NaturalExtension.rk_blockDiagFam
import Submission.Work.ORHughesFree.NaturalExtension.trunc_skewLaurentConst_eq_diagInner

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The bijection `Fin (a * k) ≃ Fin (k * a)` that swaps the two factors.  It sends the index
`finProdFinEquiv (i, j) = i * k + j` to `finProdFinEquiv (j, i) = j * a + i`, and thus converts
between the two ways of flattening a block matrix with `k` blocks of size `a`: with the block
index varying fastest (`diagInner`) and with the block index varying slowest (`blockDiagFam`). -/
def blockSwap (a k : ℕ) : Fin (a * k) ≃ Fin (k * a) :=
  (finProdFinEquiv (m := a) (n := k)).symm.trans
    ((Equiv.prodComm (Fin a) (Fin k)).trans (finProdFinEquiv (m := k) (n := a)))

theorem blockSwap_apply {a k : ℕ} (x : Fin (a * k)) :
    blockSwap a k x = finProdFinEquiv (x.modNat, x.divNat) := by
  simp [blockSwap, finProdFinEquiv_symm_apply]

theorem blockSwap_divNat {a k : ℕ} (x : Fin (a * k)) :
    (blockSwap a k x).divNat = x.modNat := by
  rw [blockSwap_apply]
  exact Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst x.modNat x.divNat

theorem blockSwap_modNat {a k : ℕ} (x : Fin (a * k)) :
    (blockSwap a k x).modNat = x.divNat := by
  rw [blockSwap_apply]
  exact Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd x.modNat x.divNat

/-- `diagInner` and `blockDiagFam` differ only by the order in which the block structure is
flattened: reindexing `blockDiagFam B` by `blockSwap` recovers `diagInner B`. -/
theorem diagInner_eq_reindex_blockDiagFam {R : Type} [Zero R] {a b k : ℕ}
    (B : Fin k → Matrix (Fin a) (Fin b) R) :
    diagInner B = Matrix.reindex (blockSwap a k).symm (blockSwap b k).symm (blockDiagFam B) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, blockDiagFam,
    diagInner, blockSwap_divNat, blockSwap_modNat]

/-- The rank of `(ofAdd r) • A` equals the rank of `A` for every `r : ℕ`, given that the rank is
invariant under the generator `ofAdd 1` of `Multiplicative ℤ`. -/
theorem rk_smul_ofAdd_nat {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (r : ℕ) :
    rk.rk n m ((Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A) = rk.rk n m A := by
  have hstep : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) U),
      rk.rk p q ((Multiplicative.ofAdd (1 : ℤ)) • M) = rk.rk p q M := by
    intro p q M
    have h : (Multiplicative.ofAdd (1 : ℤ)) • M
        = M.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a) := rfl
    rw [h]
    exact hτ p q M
  have hmain : ∀ r : ℕ, ∀ (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m ((Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A) = rk.rk n m A := by
    intro r
    induction r with
    | zero => intro A; simp
    | succ r ih =>
      intro A
      show rk.rk n m ((Multiplicative.ofAdd (((r + 1 : ℕ) : ℤ))) • A) = rk.rk n m A
      have hcast : (((r + 1 : ℕ) : ℤ)) = ((r : ℕ) : ℤ) + 1 := by simp
      rw [hcast, ofAdd_add, mul_smul,
        ih (Multiplicative.ofAdd (1 : ℤ) • A), hstep A]
  exact hmain r A

theorem rk_trunc_skewLaurentConst {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (i : ℕ) :
    rk.rk (n * i) (m * i) (trunc i (skewLaurentConst n m A)) = (i : ℝ) * rk.rk n m A := by
  rw [trunc_skewLaurentConst_eq_diagInner]
  rw [diagInner_eq_reindex_blockDiagFam (a := n) (b := m) (k := i)
        (B := fun r : Fin i => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A)]
  rw [Work.ORHughesFree.RankAPI.rk_reindex rk (blockSwap n i).symm (blockSwap m i).symm
        (blockDiagFam (fun r : Fin i => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A))]
  rw [rk_blockDiagFam (rk := rk) (a := n) (b := m) (k := i)
        (B := fun r : Fin i => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A)]
  have hterm : ∀ r : Fin i,
      rk.rk n m ((Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A) = rk.rk n m A :=
    fun r => rk_smul_ofAdd_nat rk hτ A r
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.ORHughesFree.NaturalExtension
