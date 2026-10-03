import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Every `x : Fin (a * b)` is `finProdFinEquiv` applied to its block index and `t`-degree. -/
lemma Fin_eq_finProdFinEquiv {a b : ℕ} (x : Fin (a * b)) :
    x = finProdFinEquiv (x.divNat, x.modNat) := by
  have h := Equiv.apply_symm_apply (finProdFinEquiv (m := a) (n := b)) x
  rw [finProdFinEquiv_symm_apply] at h
  exact h.symm

/-- Evaluation of `diagInner` on a `finProdFinEquiv`-indexed pair. -/
lemma diagInner_apply {U : Type} [Zero U] {a b k : ℕ} (B : Fin k → Matrix (Fin a) (Fin b) U)
    (q : Fin a) (r : Fin k) (p : Fin b) (s : Fin k) :
    diagInner B (finProdFinEquiv (q, r)) (finProdFinEquiv (p, s))
      = if r = s then B r q p else 0 := by
  simp only [diagInner, Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst,
    Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]

/-- The `k`-th coefficient of the monomial `a t^{0}` inside `U[t^{±1};τ]`. -/
lemma coeffElt_single {U : Type} [AddMonoid U] (a : U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) k = if k = 0 then a else 0 := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg, if_neg hk]
    intro h
    exact hk ((Equiv.injective (Multiplicative.ofAdd (α := ℤ))) h).symm

/-- The coefficient matrices of a constant matrix are `A` in degree `0` and `0` elsewhere. -/
lemma coeffMat_skewLaurentConst {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (k : ℤ) :
    coeffMat (skewLaurentConst n m A) k = if k = 0 then A else 0 := by
  ext i j
  rw [coeffMat_apply]
  simp only [skewLaurentConst, Matrix.map_apply]
  rw [coeffElt_single, Matrix.ite_apply, Matrix.zero_apply]

/-- The entries of the truncation of a constant matrix: the `(q,r),(p,s)` entry is
`t^r · A_{q,p}` when `r = s` and `0` otherwise. -/
lemma trunc_skewLaurentConst_apply {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
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

theorem trunc_skewLaurentConst_eq_diagInner {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) U) (i : ℕ) :
    trunc i (skewLaurentConst n m A)
      = diagInner (fun r : Fin i => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • A) := by
  ext x y
  conv_lhs => rw [Fin_eq_finProdFinEquiv x, Fin_eq_finProdFinEquiv y]
  conv_rhs => rw [Fin_eq_finProdFinEquiv x, Fin_eq_finProdFinEquiv y]
  rw [trunc_skewLaurentConst_apply, diagInner_apply]
  simp only [Matrix.smul_apply]

end Work.ORHughesFree.NaturalExtension
