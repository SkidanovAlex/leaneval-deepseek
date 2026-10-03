/-
Generated universe-`u` copies of the universe-0 lemmas needed for the
universe-polymorphic natural extension theorem.
-/

import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_le_left

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORHughesFree.NaturalExtensionGen.SkewConst

open Matrix
open Work.ORHughesFree.NaturalExtension

/- copy of NaturalExtension/rk_blockDiagFam.lean -/

open Matrix

/-- Entrywise description of `blockDiagFam`. -/
lemma blockDiagFam_apply {U : Type u} [Zero U] {a b k : ℕ}
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
lemma blockDiagFam_succ {U : Type u} [Zero U] {a b k : ℕ}
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
theorem rk_blockDiagFam {R : Type u} [Ring R] (rk : SylvesterRank R) {a b k : ℕ}
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

/- copy of NaturalExtension/trunc_skewLaurentConst_eq_diagInner.lean -/

open Matrix

/-- Every `x : Fin (a * b)` is `finProdFinEquiv` applied to its block index and `t`-degree. -/
lemma Fin_eq_finProdFinEquiv {a b : ℕ} (x : Fin (a * b)) :
    x = finProdFinEquiv (x.divNat, x.modNat) := by
  have h := Equiv.apply_symm_apply (finProdFinEquiv (m := a) (n := b)) x
  rw [finProdFinEquiv_symm_apply] at h
  exact h.symm

/-- Evaluation of `diagInner` on a `finProdFinEquiv`-indexed pair. -/
lemma diagInner_apply {U : Type u} [Zero U] {a b k : ℕ} (B : Fin k → Matrix (Fin a) (Fin b) U)
    (q : Fin a) (r : Fin k) (p : Fin b) (s : Fin k) :
    diagInner B (finProdFinEquiv (q, r)) (finProdFinEquiv (p, s))
      = if r = s then B r q p else 0 := by
  simp only [diagInner, Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst,
    Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]

/-- The `k`-th coefficient of the monomial `a t^{0}` inside `U[t^{±1};τ]`. -/
lemma coeffElt_single {U : Type u} [AddMonoid U] (a : U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) k = if k = 0 then a else 0 := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg, if_neg hk]
    intro h
    exact hk ((Equiv.injective (Multiplicative.ofAdd (α := ℤ))) h).symm

/-- The coefficient matrices of a constant matrix are `A` in degree `0` and `0` elsewhere. -/
lemma coeffMat_skewLaurentConst {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (k : ℤ) :
    coeffMat (skewLaurentConst n m A) k = if k = 0 then A else 0 := by
  ext i j
  rw [coeffMat_apply]
  simp only [skewLaurentConst, Matrix.map_apply]
  rw [coeffElt_single, Matrix.ite_apply, Matrix.zero_apply]

/-- The entries of the truncation of a constant matrix: the `(q,r),(p,s)` entry is
`t^r · A_{q,p}` when `r = s` and `0` otherwise. -/
lemma trunc_skewLaurentConst_apply {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (i : ℕ)
    (q : Fin n) (r : Fin i) (p : Fin m) (s : Fin i) :
    trunc i (skewLaurentConst n m A) (finProdFinEquiv (q, r)) (finProdFinEquiv (p, s))
      = if r = s then (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A q p else 0 := by
  rw [trunc_apply', coeffMat_skewLaurentConst]
  rw [Matrix.smul_apply, Matrix.ite_apply, Matrix.zero_apply]
  by_cases hrs : r = s
  · subst hrs; simp
  · have hne : ¬ ((((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)) = 0) := by
      intro h
      apply hrs
      have h1 : ((s : ℕ) : ℤ) = ((r : ℕ) : ℤ) := by omega
      have h2 : (s : ℕ) = (r : ℕ) := by exact_mod_cast h1
      exact (Fin.ext h2).symm
    rw [if_neg hne, if_neg hrs, smul_zero]

theorem trunc_skewLaurentConst_eq_diagInner {U : Type u} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (i : ℕ) :
    trunc i (skewLaurentConst n m A)
      = diagInner (fun r : Fin i => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A) := by
  ext x y
  conv_lhs => rw [Fin_eq_finProdFinEquiv x, Fin_eq_finProdFinEquiv y]
  conv_rhs => rw [Fin_eq_finProdFinEquiv x, Fin_eq_finProdFinEquiv y]
  rw [trunc_skewLaurentConst_apply, diagInner_apply]
  simp only [Matrix.smul_apply]

/- copy of NaturalExtension/rk_trunc_skewLaurentConst.lean -/

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
theorem diagInner_eq_reindex_blockDiagFam {R : Type u} [Zero R] {a b k : ℕ}
    (B : Fin k → Matrix (Fin a) (Fin b) R) :
    diagInner B = Matrix.reindex (blockSwap a k).symm (blockSwap b k).symm (blockDiagFam B) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, blockDiagFam,
    diagInner, blockSwap_divNat, blockSwap_modNat]

/-- The rank of `(ofAdd r) • A` equals the rank of `A` for every `r : ℕ`, given that the rank is
invariant under the generator `ofAdd 1` of `Multiplicative ℤ`. -/
theorem rk_smul_ofAdd_nat {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
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

theorem rk_trunc_skewLaurentConst {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
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

end Work.ORHughesFree.NaturalExtensionGen.SkewConst
