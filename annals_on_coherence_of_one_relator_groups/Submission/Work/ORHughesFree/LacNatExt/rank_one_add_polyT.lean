/-
# `rk (1 + B·diag(t)) = n` for `B` of non-negative degree

Let `rk'` be a Sylvester rank function on `R[t^{±1};τ]` such that `rk'(I + A·t) = N` for every
constant matrix `A` over `R` and every `N` (`onePlusAt N A`).  Then the same holds for a matrix
polynomial `B ∈ Mₙ(R[t;τ])` of non-negative degree, i.e. `rk'(1 + B·diag(t)) = n`.

The proof linearizes the matrix polynomial: writing `B = ∑_k C_k t^k` with `C_k ∈ Mₙ(R)`, the
matrix `1 + B·diag(t) = 1 + ∑_k C_k t^{k+1}` is the Schur complement of the companion matrix

  `lacComp = [[1 + C_0 t, C_1 t, …, C_d t], [t·1, -1, 0, …], [0, t·1, -1, …], …]`

with respect to the trailing block `W = -1 + t·N` (`N` the downward shift), which is invertible
with inverse `lacWiB`.  Concretely `lacComp = U · blockDiag(1 + ∑ C_k t^{k+1}, W) · V` with `U`, `V`
unipotent block matrices built from `Y·lacWiB` and `lacWiB·Z`, so

  `rk' lacComp = rk'(1 + B·diag(t)) + rk' W = rk'(1 + B·diag(t)) + d·n`.

On the other hand `lacComp = C·1 + A·diag(t)` with `C = 1 ⊕ (-1)` constant and invertible and `A`
constant, so `rk' lacComp = n + d·n` by the hypothesis on constant matrices; the claim follows.

The five auxiliary statements used here are proved in the sibling modules
`…NaturalExtension.lacMDiag_eq_target` (the coefficient decomposition of `B`),
`…NaturalExtension.lacWB_mul_WiB` (the invertibility of the trailing block),
`…NaturalExtension.lacXB_sub_YB_WiB_ZB` (the Schur complement), `…NaturalExtension.lacComp_eq_const_add`
(the constant decomposition of the companion) and `…NaturalExtension.lacCmat_mul_Cmat`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs
import Submission.Work.ORHughesFree.LacNatExt.MDiag_eq_target
import Submission.Work.ORHughesFree.LacNatExt.WB_mul_WiB
import Submission.Work.ORHughesFree.LacNatExt.XB_sub_YB_WiB_ZB
import Submission.Work.ORHughesFree.LacNatExt.Comp_eq_const_add
import Submission.Work.ORHughesFree.LacNatExt.Cmat_mul_Cmat
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.MatrixBlocks
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

universe u

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-! ## Elementary lemmas on `laccstElt`, `lacmulTElt` -/

private lemma lacpolyT_cstElt_zero : laccstElt (R := R) 0 = 0 := by simp [laccstElt]

private lemma laccstElt_one : laccstElt (R := R) 1 = 1 := by simp [laccstElt]

private lemma lacpolyT_mulTElt_zero : lacmulTElt (R := R) 0 = 0 := by simp [lacmulTElt]

private lemma laccstElt_add (a b : R) : laccstElt (a + b) = laccstElt a + laccstElt b := by
  simp [laccstElt, SkewMonoidAlgebra.single_add]

private lemma lacmulTElt_add (a b : R) : lacmulTElt (a + b) = lacmulTElt a + lacmulTElt b := by
  simp [lacmulTElt, SkewMonoidAlgebra.single_add]

private lemma laccstElt_mul (a b : R) : laccstElt a * laccstElt b = laccstElt (a * b) := by
  show SkewMonoidAlgebra.single 1 a * SkewMonoidAlgebra.single 1 b = _
  rw [SkewMonoidAlgebra.single_mul_single]
  simp [laccstElt]

private lemma laccstElt_mul_mulTElt (a b : R) : laccstElt a * lacmulTElt b = lacmulTElt (a * b) := by
  show SkewMonoidAlgebra.single 1 a * SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) b = _
  rw [SkewMonoidAlgebra.single_mul_single]
  simp [lacmulTElt]

private lemma lacsum_cstElt_mul_mulTElt {ι : Type*} (s : Finset ι) (a b : ι → R) :
    (∑ i ∈ s, laccstElt (a i) * lacmulTElt (b i)) = lacmulTElt (∑ i ∈ s, a i * b i) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => laccstElt_mul_mulTElt (a i) (b i))]
  induction s using Finset.induction with
  | empty => simp [lacmulTElt]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ih, lacmulTElt_add]

private lemma lacsum_cstElt_mul_cstElt {ι : Type*} (s : Finset ι) (a b : ι → R) :
    (∑ i ∈ s, laccstElt (a i) * laccstElt (b i)) = laccstElt (∑ i ∈ s, a i * b i) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => laccstElt_mul (a i) (b i))]
  induction s using Finset.induction with
  | empty => simp [laccstElt]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ih, laccstElt_add]

private lemma lacmap_cstElt_mul_map_mulTElt (N : ℕ) (C D : Matrix (Fin N) (Fin N) R) :
    (C.map laccstElt) * (D.map lacmulTElt) = (C * D).map lacmulTElt := by
  apply Matrix.ext
  intro u v
  simp only [Matrix.mul_apply, Matrix.map_apply]
  exact lacsum_cstElt_mul_mulTElt Finset.univ (fun w => C u w) (fun w => D w v)

private lemma lacmap_cstElt_mul_map_cstElt (N : ℕ) (C D : Matrix (Fin N) (Fin N) R) :
    (C.map laccstElt) * (D.map laccstElt) = (C * D).map laccstElt := by
  apply Matrix.ext
  intro u v
  simp only [Matrix.mul_apply, Matrix.map_apply]
  exact lacsum_cstElt_mul_cstElt Finset.univ (fun w => C u w) (fun w => D w v)

/-! ## The assembly -/

section Assembly

variable (n : ℕ) (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ)

/-- The companion factor `[[1, Y·W⁻¹], [0, 1]]`. -/
private noncomputable def lacUfac : Matrix (Fin (n + d * n)) (Fin (n + d * n)) (SkewL R) :=
  (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (lacYB B d * lacWiB (R := R) d n) 0 1).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- The inverse of `lacUfac`. -/
private noncomputable def lacUinv : Matrix (Fin (n + d * n)) (Fin (n + d * n)) (SkewL R) :=
  (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (-(lacYB B d * lacWiB (R := R) d n)) 0
    1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The companion factor `[[1, 0], [W⁻¹·Z, 1]]`. -/
private noncomputable def lacVfac : Matrix (Fin (n + d * n)) (Fin (n + d * n)) (SkewL R) :=
  (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) 0 (lacWiB (R := R) d n * lacZB (R := R) d n)
    1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The inverse of `lacVfac`. -/
private noncomputable def lacVinv : Matrix (Fin (n + d * n)) (Fin (n + d * n)) (SkewL R) :=
  (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) 0 (-(lacWiB (R := R) d n * lacZB (R := R) d n))
    1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private lemma lacUfac_mul_Uinv : lacUfac (R := R) n B d * lacUinv (R := R) n B d = 1 := by
  unfold lacUfac lacUinv
  rw [Matrix.submatrix_mul_equiv
    (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (lacYB B d * lacWiB (R := R) d n) 0 1)
    (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (-(lacYB B d * lacWiB (R := R) d n)) 0 1)
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    neg_add_cancel, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private lemma lacUinv_mul_Ufac : lacUinv (R := R) n B d * lacUfac (R := R) n B d = 1 := by
  unfold lacUfac lacUinv
  rw [Matrix.submatrix_mul_equiv
    (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (-(lacYB B d * lacWiB (R := R) d n)) 0 1)
    (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (lacYB B d * lacWiB (R := R) d n) 0 1)
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    add_neg_cancel, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private lemma lacVfac_mul_Vinv : lacVfac (R := R) n d * lacVinv (R := R) n d = 1 := by
  unfold lacVfac lacVinv
  rw [Matrix.submatrix_mul_equiv
    (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) 0 (lacWiB (R := R) d n * lacZB (R := R) d n) 1)
    (fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) 0 (-(lacWiB (R := R) d n * lacZB (R := R) d n)) 1)
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    add_neg_cancel, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private theorem lacComp_eq_gauss :
    lacComp B d = lacUfac (R := R) n B d * blockDiagFin (lacMDiag B (d + 1)) (lacWB (R := R) d n) *
      lacVfac (R := R) n d := by
  have hsum : fromBlocks (lacXB B) (lacYB B d) (lacZB (R := R) d n) (lacWB (R := R) d n) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) (lacYB B d * lacWiB (R := R) d n) 0 1 *
        (fromBlocks (lacXB B - lacYB B d * (lacWiB (R := R) d n * lacZB (R := R) d n)) 0 0
          (lacWB (R := R) d n)) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) (SkewL R)) 0 (lacWiB (R := R) d n * lacZB (R := R) d n) 1 := by
    have hY : (lacYB B d * lacWiB (R := R) d n) * lacWB (R := R) d n = lacYB B d := by
      rw [Matrix.mul_assoc, (lacWB_mul_WiB (R := R) d n).2, Matrix.mul_one]
    have hZ : lacWB (R := R) d n * (lacWiB (R := R) d n * lacZB (R := R) d n) = lacZB (R := R) d n := by
      rw [← Matrix.mul_assoc, (lacWB_mul_WiB (R := R) d n).1, Matrix.one_mul]
    have hX : lacXB B - lacYB B d * (lacWiB (R := R) d n * lacZB (R := R) d n) +
        lacYB B d * (lacWiB (R := R) d n * lacZB (R := R) d n) = lacXB B := sub_add_cancel _ _
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
    rw [hY]
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
    rw [hZ, hX]
  unfold lacComp lacUfac lacVfac Work.ORHughesFree.blockDiagFin
  rw [hsum]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, lacXB_sub_YB_WiB_ZB B d]

end Assembly

section Ranks

variable (n d : ℕ)

/-- The rank of the companion is maximal, since the companion is `I + A·diag(t)` with `A` constant. -/
theorem lacrk_Comp (n d : ℕ) (rk' : SylvesterRank (SkewL R)) (B : Matrix (Fin n) (Fin n) (SkewL R))
    (hb : ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) R), rk'.rk N N (onePlusAt N A) = (N : ℝ)) :
    rk'.rk (n + d * n) (n + d * n) (lacComp (R := R) B d) = ((n + d * n : ℕ) : ℝ) := by
  have hC : (lacCmat (R := R) d n).map (laccstElt (R := R)) * (lacCmat (R := R) d n).map (laccstElt (R := R))
      = (1 : Matrix (Fin (n + d * n)) (Fin (n + d * n)) (SkewL R)) := by
    rw [lacmap_cstElt_mul_map_cstElt, lacCmat_mul_Cmat]
    exact Matrix.map_one (laccstElt (R := R)) lacpolyT_cstElt_zero laccstElt_one
  have h1 : lacComp (R := R) B d
      = (lacCmat (R := R) d n).map (laccstElt (R := R)) *
        onePlusAt (n + d * n) (lacCmat (R := R) d n * lacAmat (R := R) B d) := by
    rw [lacComp_eq_const_add (R := R) B d]
    show (lacCmat (R := R) d n).map (laccstElt (R := R)) + (lacAmat (R := R) B d).map (lacmulTElt (R := R))
      = (lacCmat (R := R) d n).map (laccstElt (R := R)) *
        (1 + (lacCmat (R := R) d n * lacAmat (R := R) B d).map (lacmulTElt (R := R)))
    rw [mul_add, mul_one, lacmap_cstElt_mul_map_mulTElt (R := R), ← Matrix.mul_assoc, lacCmat_mul_Cmat,
      Matrix.one_mul]
  rw [h1]
  rw [SylvesterRank.rk_eq_of_left_inverse_mul rk' ((lacCmat (R := R) d n).map (laccstElt (R := R)))
    ((lacCmat (R := R) d n).map (laccstElt (R := R))) hC
    (onePlusAt (n + d * n) (lacCmat (R := R) d n * lacAmat (R := R) B d))]
  exact hb (n + d * n) (lacCmat (R := R) d n * lacAmat (R := R) B d)

/-- The trailing block of the companion is invertible, hence of maximal rank. -/
theorem lacrk_WB (n d : ℕ) (rk' : SylvesterRank (SkewL R)) :
    rk'.rk (d * n) (d * n) (lacWB (R := R) d n) = ((d * n : ℕ) : ℝ) := by
  refine le_antisymm (Work.ORHughesFree.RankAPI.rk_le_right rk' _) ?_
  rw [← Work.ORHughesFree.RankAPI.rk_one_fin rk' (d * n), ← (lacWB_mul_WiB (R := R) d n).1]
  exact rk'.rk_mul_le_left _ _

theorem lacrank_one_add_polyT {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (rk' : SylvesterRank (SkewL R)) (hb : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), rk'.rk n n (onePlusAt n A) = (n : ℝ)) {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (hB : ∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) : rk'.rk n n ((1 : Matrix (Fin n) (Fin n) (SkewL R)) + B * Matrix.diagonal (fun _ => skewLaurentT)) = (n : ℝ) := by
  set d := upperDeg B with hd
  have hMD := lacMDiag_eq_target (R := R) B hB d (le_of_eq hd.symm)
  rw [← hMD]
  have hG := lacComp_eq_gauss (R := R) n B d
  have hbk : rk'.rk (n + d * n) (n + d * n)
      (blockDiagFin (lacMDiag B (d + 1)) (lacWB (R := R) d n))
      = rk'.rk n n (lacMDiag B (d + 1)) + rk'.rk (d * n) (d * n) (lacWB (R := R) d n) :=
    SylvesterRank.rk_blockDiag rk' _ _
  have hunit : rk'.rk (n + d * n) (n + d * n) (lacComp (R := R) B d)
      = rk'.rk (n + d * n) (n + d * n) (blockDiagFin (lacMDiag B (d + 1)) (lacWB (R := R) d n)) := by
    rw [hG, Matrix.mul_assoc]
    rw [SylvesterRank.rk_eq_of_left_inverse_mul rk' (lacUfac (R := R) n B d) (lacUinv (R := R) n B d)
      (lacUinv_mul_Ufac (R := R) n B d)
      (blockDiagFin (lacMDiag B (d + 1)) (lacWB (R := R) d n) * lacVfac (R := R) n d)]
    rw [SylvesterRank.rk_eq_of_mul_right_inverse rk' (blockDiagFin (lacMDiag B (d + 1)) (lacWB (R := R) d n))
      (lacVfac (R := R) n d) (lacVinv (R := R) n d) (lacVfac_mul_Vinv (R := R) n d)]
  have h1 : rk'.rk (n + d * n) (n + d * n) (blockDiagFin (lacMDiag B (d + 1)) (lacWB (R := R) d n))
      = ((n + d * n : ℕ) : ℝ) := by
    rw [← hunit, lacrk_Comp n d rk' B hb]
  have h2 : rk'.rk n n (lacMDiag B (d + 1)) + rk'.rk (d * n) (d * n) (lacWB (R := R) d n)
      = ((n + d * n : ℕ) : ℝ) := by
    rw [← hbk, h1]
  rw [lacrk_WB n d rk'] at h2
  have hcast : ((n + d * n : ℕ) : ℝ) - ((d * n : ℕ) : ℝ) = (n : ℝ) := by
    push_cast
    ring
  linarith

end Ranks

end Work.ORHughesFree.NaturalExtension
