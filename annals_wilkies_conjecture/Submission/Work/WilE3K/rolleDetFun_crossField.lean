/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the analytic Rolle determinant of
  the elimination step is the derivative of the eliminated arctan equation along the cross-product
  field of the remaining system.

  For `E : ETData N (rt+1) n re` the remaining system `E.psiMap` is the full system map with the
  eliminated row (`E.lastRow`, the last `arctan` equation) deleted; its level sets are curves, and
  `E.gLast` is the eliminated equation.  The content of this file is

  * `E.rolleMap` is `C²` and `E.rolleDetFun` is continuous (so that Sard's theorem applies);
  * at every point of a level set `{psiMap = y}` the Rolle determinant is the derivative of `gLast`
    along the cross-product field of `psiMap` up to the sign `(-1)^n`, `n` being the number of free
    coordinates.

  ## The sign

  Let `A = jac z` be the Jacobian of the full system map, `L` the eliminated row of `A` and `X` the
  cross product of the remaining rows, so that `det [Bᵀ | v] = ⟨X, v⟩` for the matrix `B` of the
  remaining rows.  The cofactor identity gives `det A = (-1)^(N - rt) ⟨L, X⟩`, the exponent
  `N - rt = n` counting the transpositions that move the eliminated row to the last position.  The
  identity is `rcF_det_eq_sign_mul_crossField`, a purely linear-algebraic statement about a matrix
  and the cofactor functional of its rows.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE2.KhoCount
import Submission.Work.WilE3K.evalPoly_rolleDetP
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE2.tangentField_exists
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

/-! ## §0. The cofactor identity and the sign `(-1)^(m - j)`

For `A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ` and `j : Fin (m+1)` consider the matrix `N j` whose
first `m` columns are the rows `Fin.succAbove j k` of `A` transposed and whose last column is the
transposed `j`-th row.  Passing from `j` to `j + 1` transposes the columns `j` and `m`, so the
determinant changes sign, and at `j = m` the matrix is `Aᵀ`; hence `det (N j) = (-1)^(m-j) det A`.
This is the cofactor identity of the generalised cross product, with the row bookkeeping of
`Fin.succAbove` and the sign `(-1)^(N - rt)` of the elimination step. -/

/-- The value of `Fin.succAbove`. -/
theorem rcF_val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ)
      = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h]
    have h' : (Fin.castSucc i : Fin (n + 1)) < p := by
      rw [Fin.lt_def]
      exact h
    rw [Fin.succAbove_of_castSucc_lt p i h']
    rfl
  · rw [if_neg h]
    have h' : p ≤ (Fin.castSucc i : Fin (n + 1)) := by
      rw [Fin.le_def]
      show (p : ℕ) ≤ (i : ℕ)
      omega
    rw [Fin.succAbove_of_le_castSucc p i h']
    rfl

/-- The matrix whose first `m` columns are the transposed rows of `A` other than the `j`-th (in the
order given by `Fin.succAbove`) and whose last column is the transposed `j`-th row. -/
def rcF_colMatrix {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j : Fin (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i k => if h : (k : ℕ) < m then A (Fin.succAbove j ⟨(k : ℕ), h⟩) i else A j i

/-- At `j = m` the matrix `rcF_colMatrix A j` is the transpose of `A`. -/
theorem rcF_colMatrix_last {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    rcF_colMatrix A (Fin.last m) = A.transpose := by
  ext i k
  rw [rcF_colMatrix, Matrix.of_apply, Matrix.transpose_apply]
  by_cases hk : (k : ℕ) < m
  · rw [dif_pos hk, Fin.succAbove_last]
    exact congrArg (fun r => A r i) (Fin.ext rfl)
  · have hk' : k = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    rw [dif_neg hk, hk']

/-- Moving from `j` to `j + 1` exchanges the columns `j` and `m` of `rcF_colMatrix A ·`. -/
theorem rcF_colMatrix_succ {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j : Fin m) :
    rcF_colMatrix A j.succ
      = (rcF_colMatrix A j.castSucc).submatrix id (Equiv.swap j.castSucc (Fin.last m)) := by
  ext i k
  simp only [Matrix.submatrix_apply, rcF_colMatrix, Matrix.of_apply, id_eq]
  by_cases hk : (k : ℕ) < m
  · rw [dif_pos hk]
    by_cases hkswap : (((Equiv.swap j.castSucc (Fin.last m)) k : Fin (m + 1)) : ℕ) < m
    · rw [dif_pos hkswap]
      have hk_ne_j : k ≠ j.castSucc := by
        intro h
        rw [h, Equiv.swap_apply_left, Fin.val_last] at hkswap
        omega
      have hk_ne_last : k ≠ Fin.last m := by
        intro h; rw [h, Fin.val_last] at hk; omega
      have hσval : (((Equiv.swap j.castSucc (Fin.last m)) k : Fin (m + 1)) : ℕ) = (k : ℕ) :=
        congrArg Fin.val (Equiv.swap_apply_of_ne_of_ne hk_ne_j hk_ne_last)
      have hne_val : (k : ℕ) ≠ (j : ℕ) := by
        intro h; exact hk_ne_j (Fin.ext (by rw [h]; rfl))
      congr 1
      by_cases hlt : (k : ℕ) < (j : ℕ)
      · have hA : (⟨(k : ℕ), hk⟩ : Fin m) ≤ j := by
          rw [Fin.le_def]; exact hlt.le
        have hB : (⟨(((Equiv.swap j.castSucc (Fin.last m)) k : Fin (m + 1)) : ℕ),
            hkswap⟩ : Fin m) < j := by
          rw [Fin.lt_def]
          show (((Equiv.swap j.castSucc (Fin.last m)) k : Fin (m + 1)) : ℕ) < (j : ℕ)
          rw [hσval]
          exact hlt
        rw [Fin.succAbove_succ_of_le j (⟨(k : ℕ), hk⟩ : Fin m) hA,
          Fin.succAbove_castSucc_of_lt j (⟨(((Equiv.swap j.castSucc (Fin.last m)) k
            : Fin (m + 1)) : ℕ), hkswap⟩ : Fin m) hB]
        apply Fin.ext
        simp only [Fin.val_castSucc]
        exact hσval.symm
      · have hA : j < (⟨(k : ℕ), hk⟩ : Fin m) := by
          rw [Fin.lt_def]
          show (j : ℕ) < (k : ℕ)
          omega
        have hB : j ≤ (⟨(((Equiv.swap j.castSucc (Fin.last m)) k : Fin (m + 1)) : ℕ),
            hkswap⟩ : Fin m) := by
          rw [Fin.le_def]
          show (j : ℕ) ≤ (((Equiv.swap j.castSucc (Fin.last m)) k : Fin (m + 1)) : ℕ)
          rw [hσval]
          omega
        rw [Fin.succAbove_succ_of_lt j (⟨(k : ℕ), hk⟩ : Fin m) hA,
          Fin.succAbove_castSucc_of_le j (⟨(((Equiv.swap j.castSucc (Fin.last m)) k
            : Fin (m + 1)) : ℕ), hkswap⟩ : Fin m) hB]
        apply Fin.ext
        rw [Fin.val_succ, Fin.val_succ, hσval]
    · rw [dif_neg hkswap]
      -- then `swap j (last m) k = last m`, so `k = j` and both entries are the row `j`
      have hlast : (Equiv.swap j.castSucc (Fin.last m)) k = Fin.last m := by
        refine Fin.ext ?_
        rw [Fin.val_last]
        have := ((Equiv.swap j.castSucc (Fin.last m)) k).isLt
        omega
      have hk_eq : k = j.castSucc := by
        have h1 : (Equiv.swap j.castSucc (Fin.last m))
            ((Equiv.swap j.castSucc (Fin.last m)) k) = k :=
          Equiv.swap_apply_self (j.castSucc) (Fin.last m) k
        rw [hlast, Equiv.swap_apply_right] at h1
        exact h1.symm
      have hkk : (⟨(k : ℕ), hk⟩ : Fin m) = j := by
        apply Fin.ext
        show (k : ℕ) = (j : ℕ)
        rw [congrArg Fin.val hk_eq]
        rfl
      rw [hkk, Fin.succAbove_succ_self]
  · rw [dif_neg hk]
    have hk_last : k = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    subst hk_last
    rw [Equiv.swap_apply_right]
    rw [dif_pos (by rw [Fin.val_castSucc]; exact j.isLt)]
    congr 1
    refine Fin.ext ?_
    rw [rcF_val_succAbove, if_neg (lt_irrefl ((j.castSucc : Fin (m + 1)) : ℕ))]
    rfl

/-- **The cofactor identity.**  `det (rcF_colMatrix A j) = (-1)^(m - j) * det A`. -/
theorem rcF_det_colMatrix {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    ∀ j : Fin (m + 1), (rcF_colMatrix A j).det = (-1 : ℝ) ^ (m - (j : ℕ)) * A.det := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    have hlast : (rcF_colMatrix A (Fin.last m)).det = A.det := by
      rw [rcF_colMatrix_last, Matrix.det_transpose]
    rw [hlast]
    have h0 : m - ((Fin.last m : Fin (m + 1)) : ℕ) = 0 := by rw [Fin.val_last]; omega
    rw [h0, pow_zero, one_mul]
  | cast i hi =>
    have hstep : (rcF_colMatrix A i.succ).det = - (rcF_colMatrix A i.castSucc).det := by
      rw [rcF_colMatrix_succ A i, Matrix.det_permute']
      have hsign : (↑↑(Equiv.Perm.sign (Equiv.swap i.castSucc (Fin.last m))) : ℝ) = -1 := by
        rw [Equiv.Perm.sign_swap (by simp : i.castSucc ≠ Fin.last m)]
        norm_num
      rw [hsign]
      ring
    have h' : - (rcF_colMatrix A i.castSucc).det
        = (-1 : ℝ) ^ (m - ((i.succ : Fin (m + 1)) : ℕ)) * A.det := by
      rw [← hstep, hi]
    have hpow : m - ((i.castSucc : Fin (m + 1)) : ℕ)
        = (m - ((i.succ : Fin (m + 1)) : ℕ)) + 1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    calc (rcF_colMatrix A i.castSucc).det
        = - (- (rcF_colMatrix A i.castSucc).det) := by ring
      _ = - ((-1 : ℝ) ^ (m - ((i.succ : Fin (m + 1)) : ℕ)) * A.det) := by rw [h']
      _ = (-1 : ℝ) ^ (m - ((i.castSucc : Fin (m + 1)) : ℕ)) * A.det := by
            rw [hpow, pow_succ]; ring

/-- **The determinant of a matrix against the cofactor functional of its rows.**  If `X` is the
cofactor functional of the `(m+1)`-st column of `rcF_colMatrix A r0` — i.e. `⟨X, v⟩ = det (N v)`
where `N v` is `rcF_colMatrix A r0` with the last column replaced by `v` — then

`det A = (-1)^(m - r0) * ⟨row r0 of A, X⟩`. -/
theorem rcF_det_eq_sign_mul_crossField {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (r0 : Fin (m + 1)) (X : Fin (m + 1) → ℝ)
    (hX : ∀ v : Fin (m + 1) → ℝ, (∑ i, X i * v i) =
      (Matrix.of fun (i : Fin (m + 1)) (k : Fin (m + 1)) =>
        if h : (k : ℕ) < m then A (Fin.succAbove r0 ⟨(k : ℕ), h⟩) i else v i).det) :
    A.det = (-1 : ℝ) ^ (m - (r0 : ℕ)) * (∑ i, A r0 i * X i) := by
  have h := hX (fun i => A r0 i)
  have hmat : (Matrix.of fun (i : Fin (m + 1)) (k : Fin (m + 1)) =>
        if h : (k : ℕ) < m then A (Fin.succAbove r0 ⟨(k : ℕ), h⟩) i else A r0 i)
      = rcF_colMatrix A r0 := rfl
  rw [hmat] at h
  have hdet := rcF_det_colMatrix A r0
  have he : (∑ i, A r0 i * X i) = (-1 : ℝ) ^ (m - (r0 : ℕ)) * A.det := by
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (A r0 i) (X i)), h, hdet]
  have hsq : (-1 : ℝ) ^ (m - (r0 : ℕ)) * (-1 : ℝ) ^ (m - (r0 : ℕ)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨m - (r0 : ℕ), by ring⟩
  rw [he, ← mul_assoc, hsq, one_mul]

namespace ETData

/-! ## §1. The derivative of the evaluated EA polynomial -/

/-- The Fréchet derivative of `E.evalPoly Q` is the symbolic derivative `E.dPoly`. -/
theorem rcF_evalPoly_hasFDerivAt (E : ETData N rt n re) (Q : EAPoly (N + 1) re)
    (z : Fin (N + 1) → ℝ) :
    HasFDerivAt (fun w : Fin (N + 1) → ℝ => E.evalPoly Q w)
      (∑ c : Fin (N + 1), (E.evalPoly (E.dPoly c Q) z) •
        (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
  have hfun : (fun w : Fin (N + 1) → ℝ => E.evalPoly Q w)
      = fun w => eaEval E.toChain Q w := funext fun w => E.evalPoly_eq_eaEval Q w
  have h := Work.WilE9.EaD.eaD_hasFDerivAt E.toChain Q z
  rw [← hfun] at h
  refine h.congr_fderiv ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← E.dPoly_eq_eaD, ← E.evalPoly_eq_eaEval]

/-- The evaluation `E.evalPoly Q` is smooth. -/
theorem rcF_contDiff_evalPoly (E : ETData N rt n re) (Q : EAPoly (N + 1) re) :
    ContDiff ℝ ⊤ (fun w : Fin (N + 1) → ℝ => E.evalPoly Q w) := by
  rw [show (fun w : Fin (N + 1) → ℝ => E.evalPoly Q w)
      = fun w => eaEval E.toChain Q w from funext fun w => E.evalPoly_eq_eaEval Q w]
  exact Work.WilE9.EaD.eaEval_contDiff E.toChain Q

/-- Evaluation of `∑ i, a i • proj i` at a standard basis vector. -/
theorem rcF_sum_smul_proj_single {m : ℕ} (a : Fin m → ℝ) (c : Fin m) :
    ((∑ i : Fin m, a i • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ))
      (Pi.single c 1)) = a c := by
  rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single c]
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply]
    rw [Pi.single_eq_of_ne hb, smul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

/-! ## §2. The derivative of an arctan row -/

/-- The derivative of the `j`-th arctan equation in the direction of the `c`-th standard basis
vector is `E.dTanFun j z c`. -/
theorem rcF_fderiv_tanFun (E : ETData N rt n re) (j : Fin rt) (z : Fin (N + 1) → ℝ)
    (c : Fin (N + 1)) :
    fderiv ℝ (E.tanFun j) z (Pi.single c 1) = E.dTanFun j z c := by
  have harctan : HasFDerivAt (fun w : Fin (N + 1) → ℝ => Real.arctan (w (E.tanCoord j)))
      ((1 / (1 + z (E.tanCoord j) ^ 2)) •
        (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
    have h1 : HasFDerivAt Real.arctan
        (ContinuousLinearMap.toSpanSingleton ℝ (1 / (1 + z (E.tanCoord j) ^ 2)))
        (z (E.tanCoord j)) :=
      (Real.hasDerivAt_arctan (z (E.tanCoord j))).hasFDerivAt
    have h2 : HasFDerivAt (fun w : Fin (N + 1) → ℝ => w (E.tanCoord j))
        (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ) z :=
      hasFDerivAt_apply (E.tanCoord j) z
    have h3 := h1.comp z h2
    have h4 : (ContinuousLinearMap.toSpanSingleton ℝ (1 / (1 + z (E.tanCoord j) ^ 2))
          : ℝ →L[ℝ] ℝ)
        ∘L (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)
        = (1 / (1 + z (E.tanCoord j) ^ 2)) •
          (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ) := by
      ext vc
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    rw [h4] at h3
    simpa only [Function.comp_def] using h3
  have hlin : HasFDerivAt (E.lin j)
      (∑ i : Fin n, (E.lam j i) •
        (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
    have hfun : E.lin j = fun w : Fin (N + 1) → ℝ =>
        (∑ i : Fin n, (E.lam j i) •
          (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) w
          + E.mu j := by
      funext w
      simp only [ETData.lin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hfun]
    exact (ContinuousLinearMap.hasFDerivAt _).add_const (E.mu j)
  have hsub : HasFDerivAt (E.tanFun j)
      ((1 / (1 + z (E.tanCoord j) ^ 2)) •
          (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)
        - ∑ i : Fin n, (E.lam j i) •
          (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z :=
    harctan.sub hlin
  rw [hsub.fderiv]
  have hval : ((1 / (1 + z (E.tanCoord j) ^ 2)) •
        (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)
      - ∑ i : Fin n, (E.lam j i) •
        (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ))
        (Pi.single c (1 : ℝ))
      = (1 / (1 + z (E.tanCoord j) ^ 2))
          * (Pi.single c (1 : ℝ) : Fin (N + 1) → ℝ) (E.tanCoord j)
        - ∑ i : Fin n,
            E.lam j i * (Pi.single c (1 : ℝ) : Fin (N + 1) → ℝ) (E.freeCoord i) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [hval]
  rcases E.eq_tanCoord_or_eq_freeCoord c with ⟨j', rfl⟩ | ⟨i, rfl⟩
  · rw [E.dTanFun_tan j j' z]
    have hsingle : (Pi.single (E.tanCoord j') (1 : ℝ) : Fin (N + 1) → ℝ) (E.tanCoord j)
        = if j' = j then 1 else 0 := by
      by_cases h : j' = j
      · subst h; simp
      · have hne : E.tanCoord j ≠ E.tanCoord j' :=
          fun hh => h (E.tanCoord_injective hh).symm
        rw [Pi.single_eq_of_ne hne, if_neg h]
    have hzero : (∑ b : Fin n, E.lam j b *
        (Pi.single (E.tanCoord j') (1 : ℝ) : Fin (N + 1) → ℝ) (E.freeCoord b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hne : E.freeCoord b ≠ E.tanCoord j' := by
        intro hh
        have h1 : ((E.freeCoord b : Fin (N + 1)) : ℕ) = rt + (b : ℕ) := E.freeCoord_val b
        have h2 : ((E.tanCoord j' : Fin (N + 1)) : ℕ) = (j' : ℕ) := E.tanCoord_val j'
        omega
      rw [Pi.single_eq_of_ne hne, mul_zero]
    rw [hsingle, hzero, sub_zero]
    by_cases h : j' = j
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h, if_neg h]; ring
  · rw [E.dTanFun_free j z i]
    have hsingle : (Pi.single (E.freeCoord i) (1 : ℝ) : Fin (N + 1) → ℝ) (E.tanCoord j) = 0 := by
      have hne : E.tanCoord j ≠ E.freeCoord i := by
        intro hh
        have h1 : ((E.freeCoord i : Fin (N + 1)) : ℕ) = rt + (i : ℕ) := E.freeCoord_val i
        have h2 : ((E.tanCoord j : Fin (N + 1)) : ℕ) = (j : ℕ) := E.tanCoord_val j
        omega
      exact Pi.single_eq_of_ne hne 1
    have hsum : (∑ b : Fin n, E.lam j b *
        (Pi.single (E.freeCoord i) (1 : ℝ) : Fin (N + 1) → ℝ) (E.freeCoord b)) = E.lam j i := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_one]
      · intro b _ hb
        have hne : E.freeCoord b ≠ E.freeCoord i := fun hh => hb (E.freeCoord_injective hh)
        rw [Pi.single_eq_of_ne hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsingle, hsum, mul_zero, zero_sub]

/-! ## §3. The Jacobian is the matrix of derivatives -/

/-- The Jacobian of the system map is the matrix of the derivatives of its components. -/
theorem rcF_jac_eq_fderiv (E : ETData N rt n re) (z : Fin (N + 1) → ℝ) :
    E.jac z = Matrix.of fun r c => fderiv ℝ (fun w => E.map w r) z (Pi.single c 1) := by
  ext r c
  by_cases hr : (r : ℕ) < rt
  · have h1 : E.jac z r c = E.dTanFun (E.tanIndex r hr) z c := by
      rw [show E.jac z r c = E.jac z (E.tanCoord (E.tanIndex r hr)) c from
        congrArg (fun r' => E.jac z r' c) (E.tanCoord_tanIndex r hr).symm]
      exact E.jac_tan z (E.tanIndex r hr) c
    have h2 : fderiv ℝ (fun w => E.map w r) z (Pi.single c 1)
        = E.dTanFun (E.tanIndex r hr) z c := by
      have hfun : (fun w : Fin (N + 1) → ℝ => E.map w r) = E.tanFun (E.tanIndex r hr) := by
        funext w
        rw [show E.map w r = E.map w (E.tanCoord (E.tanIndex r hr)) from
          congrArg (fun r' => E.map w r') (E.tanCoord_tanIndex r hr).symm]
        exact E.map_tan w (E.tanIndex r hr)
      rw [hfun]
      exact E.rcF_fderiv_tanFun (E.tanIndex r hr) z c
    rw [h1]
    exact h2.symm
  · have hle : rt ≤ (r : ℕ) := not_lt.mp hr
    have h1 : E.jac z r c = E.evalPoly (E.dPoly c (E.G (E.freeIndex r hle))) z := by
      rw [show E.jac z r c = E.jac z (E.freeCoord (E.freeIndex r hle)) c from
        congrArg (fun r' => E.jac z r' c) (E.freeCoord_freeIndex r hle).symm]
      exact E.jac_free z (E.freeIndex r hle) c
    have h2 : fderiv ℝ (fun w => E.map w r) z (Pi.single c 1)
        = E.evalPoly (E.dPoly c (E.G (E.freeIndex r hle))) z := by
      have hfun : (fun w : Fin (N + 1) → ℝ => E.map w r) = E.evP (E.freeIndex r hle) := by
        funext w
        rw [show E.map w r = E.map w (E.freeCoord (E.freeIndex r hle)) from
          congrArg (fun r' => E.map w r') (E.freeCoord_freeIndex r hle).symm]
        exact E.map_free w (E.freeIndex r hle)
      rw [hfun]
      change fderiv ℝ (fun w : Fin (N + 1) → ℝ => E.evalPoly (E.G (E.freeIndex r hle)) w) z
        (Pi.single c 1) = E.evalPoly (E.dPoly c (E.G (E.freeIndex r hle))) z
      rw [(E.rcF_evalPoly_hasFDerivAt (E.G (E.freeIndex r hle)) z).fderiv]
      exact rcF_sum_smul_proj_single
        (fun b => E.evalPoly (E.dPoly b (E.G (E.freeIndex r hle))) z) c
    rw [h1]
    exact h2.symm

/-! ## §4. Smoothness -/

/-- The system map is `C²`. -/
theorem rcF_contDiff_map (E : ETData N rt n re) : ContDiff ℝ 2 E.map := by
  rw [contDiff_pi]
  intro r
  by_cases hr : (r : ℕ) < rt
  · have htan : ContDiff ℝ 2 (E.tanFun (E.tanIndex r hr)) := by
      change ContDiff ℝ 2 (fun w : Fin (N + 1) → ℝ =>
        Real.arctan (w (E.tanCoord (E.tanIndex r hr))) - E.lin (E.tanIndex r hr) w)
      refine ContDiff.sub ?_ ?_
      · exact (Real.contDiff_arctan (n := 2)).comp (contDiff_apply ℝ ℝ _)
      · change ContDiff ℝ 2 (fun w : Fin (N + 1) → ℝ =>
          (∑ i : Fin n, E.lam (E.tanIndex r hr) i * w (E.freeCoord i))
            + E.mu (E.tanIndex r hr))
        exact (ContDiff.sum (fun i _ =>
          contDiff_const.mul (contDiff_apply ℝ ℝ (E.freeCoord i)))).add contDiff_const
    rw [show (fun w : Fin (N + 1) → ℝ => E.map w r) = E.tanFun (E.tanIndex r hr) from by
      funext w
      rw [show E.map w r = E.map w (E.tanCoord (E.tanIndex r hr)) from
        congrArg (fun r' => E.map w r') (E.tanCoord_tanIndex r hr).symm]
      exact E.map_tan w (E.tanIndex r hr)]
    exact htan
  · have hle : rt ≤ (r : ℕ) := not_lt.mp hr
    rw [show (fun w : Fin (N + 1) → ℝ => E.map w r) = E.evP (E.freeIndex r hle) from by
      funext w
      rw [show E.map w r = E.map w (E.freeCoord (E.freeIndex r hle)) from
        congrArg (fun r' => E.map w r') (E.freeCoord_freeIndex r hle).symm]
      exact E.map_free w (E.freeIndex r hle)]
    change ContDiff ℝ 2 (fun w : Fin (N + 1) → ℝ => E.evalPoly (E.G (E.freeIndex r hle)) w)
    exact (E.rcF_contDiff_evalPoly (E.G (E.freeIndex r hle))).of_le le_top

/-- The Rolle determinant is `C²` (a quotient of smooth functions with positive denominator). -/
theorem rcF_contDiff_rolleDetFun (E : ETData N (rt + 1) n re) : ContDiff ℝ 2 E.rolleDetFun := by
  change ContDiff ℝ 2
    (fun z : Fin (N + 1) → ℝ => E.evalPoly E.rolleDetP z / E.prodEval z)
  refine ContDiff.div ?_ ?_ ?_
  · exact (E.rcF_contDiff_evalPoly E.rolleDetP).of_le le_top
  · change ContDiff ℝ 2 (fun z : Fin (N + 1) → ℝ =>
      ∏ j : Fin (rt + 1), (1 + z (E.tanCoord j) ^ 2))
    refine contDiff_prod (t := Finset.univ)
      (f := fun (j : Fin (rt + 1)) (z : Fin (N + 1) → ℝ) => 1 + z (E.tanCoord j) ^ 2) ?_
    intro j _
    exact contDiff_const.add ((contDiff_apply ℝ ℝ (E.tanCoord j)).pow 2)
  · intro z
    exact ne_of_gt (Finset.prod_pos fun j _ => ETData.one_add_sq_pos z (E.tanCoord j))

/-- The Rolle map `(psiMap, rolleDetFun)` is `C²`. -/
theorem rcF_contDiff_rolleMap (E : ETData N (rt + 1) n re) : ContDiff ℝ 2 E.rolleMap := by
  rw [contDiff_pi]
  intro r
  by_cases hr : (r : ℕ) < N
  · rw [show (fun z : Fin (N + 1) → ℝ => E.rolleMap z r)
        = fun z => E.map z (Fin.succAbove E.lastRow ⟨(r : ℕ), hr⟩) from by
      funext z
      show (if h : (r : ℕ) < N then E.psiMap z ⟨(r : ℕ), h⟩ else E.rolleDetFun z)
        = E.map z (Fin.succAbove E.lastRow ⟨(r : ℕ), hr⟩)
      rw [dif_pos hr]
      exact E.psiMap_apply z ⟨(r : ℕ), hr⟩]
    exact (contDiff_pi.mp E.rcF_contDiff_map) (Fin.succAbove E.lastRow ⟨(r : ℕ), hr⟩)
  · rw [show (fun z : Fin (N + 1) → ℝ => E.rolleMap z r) = E.rolleDetFun from by
      funext z
      show (if h : (r : ℕ) < N then E.psiMap z ⟨(r : ℕ), h⟩ else E.rolleDetFun z)
        = E.rolleDetFun z
      rw [dif_neg hr]]
    exact E.rcF_contDiff_rolleDetFun

/-! ## §5. The cross-field identity -/

/-- The eliminated row is the row of the last `tan` coordinate. -/
theorem rcF_tanCoord_last (E : ETData N (rt + 1) n re) :
    E.tanCoord (Fin.last rt) = E.lastRow :=
  Fin.ext rfl

/-- The evaluated cross-product field of the remaining system is the cofactor functional of the
transposed Jacobian rows. -/
theorem rcF_crossField_matrix (E : ETData N (rt + 1) n re) (y : Fin N → ℝ)
    (z : Fin (N + 1) → ℝ) (v : Fin (N + 1) → ℝ) :
    (∑ i, Work.WilE2.crossField (fun w => E.psiMap w - y) z i * v i)
      = (Matrix.of fun (i : Fin (N + 1)) (k : Fin (N + 1)) =>
          if h : (k : ℕ) < N then E.jac z (Fin.succAbove E.lastRow ⟨(k : ℕ), h⟩) i
          else v i).det := by
  rw [Work.WilE2.crossField_det (fun w => E.psiMap w - y) z v]
  congr 1
  ext i k
  by_cases hk : (k : ℕ) < N
  · simp only [Work.WilE2.tangMatrix, Matrix.of_apply, dif_pos hk]
    have hfun : (fun w : Fin (N + 1) → ℝ => (E.psiMap w - y) ⟨(k : ℕ), hk⟩)
        = fun w => E.psiMap w ⟨(k : ℕ), hk⟩ - y ⟨(k : ℕ), hk⟩ := by
      funext w
      exact Pi.sub_apply _ _ _
    have hψ : (fun w : Fin (N + 1) → ℝ => E.psiMap w ⟨(k : ℕ), hk⟩)
        = fun w => E.map w (Fin.succAbove E.lastRow ⟨(k : ℕ), hk⟩) := by
      funext w
      exact E.psiMap_apply w ⟨(k : ℕ), hk⟩
    have hjac : E.jac z (Fin.succAbove E.lastRow ⟨(k : ℕ), hk⟩) i
        = fderiv ℝ (fun w => E.map w (Fin.succAbove E.lastRow ⟨(k : ℕ), hk⟩)) z
            (Pi.single i 1) := by
      rw [E.rcF_jac_eq_fderiv z]
      rfl
    rw [hfun, fderiv_sub_const, hψ, ← hjac]
  · simp only [Work.WilE2.tangMatrix, Matrix.of_apply, dif_neg hk]

/-- The derivative of the eliminated equation along the cross-product field is the pairing of its
gradient row with the cross-product field. -/
theorem rcF_fderiv_gLast_crossField (E : ETData N (rt + 1) n re) (y : Fin N → ℝ)
    (z : Fin (N + 1) → ℝ) :
    (∑ i, E.jac z E.lastRow i * Work.WilE2.crossField (fun w => E.psiMap w - y) z i)
      = fderiv ℝ E.gLast z (Work.WilE2.crossField (fun w => E.psiMap w - y) z) := by
  have hgLast : E.gLast = fun w => E.map w E.lastRow := by
    funext w
    show E.tanFun (Fin.last rt) w = E.map w E.lastRow
    rw [show E.map w E.lastRow = E.map w (E.tanCoord (Fin.last rt)) from
      congrArg (fun r => E.map w r) (E.rcF_tanCoord_last).symm, E.map_tan]
  rw [hgLast, Work.WilE2.clm_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hjac : E.jac z E.lastRow i
      = fderiv ℝ (fun w => E.map w E.lastRow) z (Pi.single i 1) := by
    rw [E.rcF_jac_eq_fderiv z]
    rfl
  rw [← hjac]
  ring

end ETData

/-! ## §6. The target -/

theorem rolleDetFun_crossField {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re) :
    ContDiff ℝ 2 E.rolleMap ∧ Continuous E.rolleDetFun ∧
    ∀ (y : Fin N → ℝ) (z : Fin (N + 1) → ℝ), E.psiMap z = y →
      E.rolleDetFun z = (-1 : ℝ) ^ n * fderiv ℝ E.gLast z
        (Work.WilE2.crossField (fun w => E.psiMap w - y) z) := by
  refine ⟨E.rcF_contDiff_rolleMap, E.rcF_contDiff_rolleDetFun.continuous, ?_⟩
  intro y z _
  have hdet : E.rolleDetFun z = (E.jac z).det := by
    have hne : E.prodEval z ≠ 0 :=
      ne_of_gt (Finset.prod_pos fun j _ => ETData.one_add_sq_pos z (E.tanCoord j))
    rw [ETData.rolleDetFun, evalPoly_rolleDetP E z, div_eq_iff hne]
    ring
  have hD := rcF_det_eq_sign_mul_crossField (E.jac z) E.lastRow
    (Work.WilE2.crossField (fun w => E.psiMap w - y) z)
    (fun v => E.rcF_crossField_matrix y z v)
  have h3 := E.rcF_fderiv_gLast_crossField y z
  rw [hdet, hD, h3]
  have hexp : N - ((E.lastRow : Fin (N + 1)) : ℕ) = n := by
    have h := E.h
    have hval : ((E.lastRow : Fin (N + 1)) : ℕ) = rt := rfl
    omega
  rw [hexp]

end Work.WilE3K
