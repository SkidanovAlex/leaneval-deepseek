import Mathlib
import Submission.Work.KT.Psi.SubIncl
import Submission.Work.KT.Psi.mul_subIncl_mul_subInclT
import Submission.Work.KT.Psi.clsM_submatrix

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- The compression of a square matrix `M` over `ι` to the block determined by a predicate `pr`:
the `{i // pr i} × {i // pr i}`-minor of `M`. -/
def subMat {R : Type} [Ring R] {ι : Type} (pr : ι → Prop) (M : Matrix ι ι R) :
    Matrix {i // pr i} {i // pr i} R :=
  M.submatrix Subtype.val Subtype.val

/-- The class in `K₀` of a non-idempotent matrix over an arbitrary finite index type vanishes. -/
theorem clsM_eq_zero_of_not_idem {R : Type} [Ring R] {ι : Type} [Fintype ι]
    {M : Matrix ι ι R} (hM : ¬ M * M = M) : clsM ι M = 0 := by
  rw [clsM_eq_cls]
  refine cls_zero_of_not_idem (fun hc => hM ?_)
  change Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M =
    Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M at hc
  have hc' : (Matrix.reindexRingEquiv R (Fintype.equivFin ι)) (M * M) =
      (Matrix.reindexRingEquiv R (Fintype.equivFin ι)) M := by
    rw [map_mul]
    exact hc
  exact (Matrix.reindexRingEquiv R (Fintype.equivFin ι)).injective hc'

/-- If `M` vanishes off the block determined by `pr`, then `M` is idempotent as soon as its
compression to the block is. -/
theorem idem_of_idem_submatrix {R : Type} [Ring R] {ι : Type} [Fintype ι] [DecidableEq ι]
    {pr : ι → Prop} [DecidablePred pr] (M : Matrix ι ι R)
    (hsupp : ∀ i j : ι, ¬ (pr i ∧ pr j) → M i j = 0)
    (hsub : subMat pr M * subMat pr M = subMat pr M) :
    M * M = M := by
  classical
  have hA : M * subIncl R pr * (subIncl R pr)ᵀ = M := mul_subIncl_mul_subInclT M hsupp
  have hQ : ∀ i k : ι,
      (subIncl R pr * (subIncl R pr)ᵀ) i k = if pr i ∧ i = k then (1 : R) else 0 := by
    intro i k
    rw [Matrix.mul_apply]
    by_cases h : pr i ∧ i = k
    · obtain ⟨hi, rfl⟩ := h
      rw [if_pos ⟨hi, rfl⟩, Finset.sum_eq_single (⟨i, hi⟩ : {x // pr x})]
      · rw [subIncl_apply, subIncl_transpose_apply, if_pos rfl, mul_one]
      · intro a _ ha
        rw [subIncl_apply, if_neg (fun hh => ha (Subtype.ext hh)), zero_mul]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg h, Finset.sum_eq_zero]
      intro a _
      by_cases hai : (a : ι) = i
      · rw [subIncl_apply, if_pos hai, subIncl_transpose_apply,
          if_neg (fun hak => h ⟨hai ▸ a.2, by rw [← hai]; exact hak⟩), mul_zero]
      · rw [subIncl_apply, if_neg hai, zero_mul]
  have hB : subIncl R pr * (subIncl R pr)ᵀ * M = M := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hi : pr i
    · rw [Finset.sum_eq_single i]
      · rw [hQ, if_pos ⟨hi, rfl⟩, one_mul]
      · intro k _ hk
        rw [hQ, if_neg (fun h => hk h.2.symm), zero_mul]
      · intro hmem; exact absurd (Finset.mem_univ i) hmem
    · rw [hsupp i j (fun h => hi h.1), Finset.sum_eq_zero]
      intro k _
      rw [hQ, if_neg (fun h => hi h.1), zero_mul]
  have hPP : (subIncl R pr)ᵀ * subIncl R pr = 1 := by
    have h := subInclT_mul_subIncl (A := R) pr (1 : Matrix ι ι R)
    rw [Matrix.mul_one] at h
    have h1 : (1 : Matrix ι ι R).submatrix Subtype.val Subtype.val =
        (1 : Matrix {i // pr i} {i // pr i} R) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.one_apply]
      by_cases hh : a = b
      · subst hh; simp
      · rw [if_neg hh, if_neg (fun h2 => hh (Subtype.ext h2))]
    rw [h1] at h
    exact h
  have hMPC : subIncl R pr * subMat pr M * (subIncl R pr)ᵀ = M := by
    have hCeq : subMat pr M = (subIncl R pr)ᵀ * M * subIncl R pr :=
      (subInclT_mul_subIncl (A := R) pr M).symm
    rw [hCeq]
    rw [show subIncl R pr * ((subIncl R pr)ᵀ * M * subIncl R pr) * (subIncl R pr)ᵀ =
        (subIncl R pr * (subIncl R pr)ᵀ) * M * (subIncl R pr * (subIncl R pr)ᵀ)
      from by simp only [Matrix.mul_assoc]]
    rw [hB, ← Matrix.mul_assoc M (subIncl R pr) (subIncl R pr)ᵀ, hA]
  rw [← hMPC]
  calc (subIncl R pr * subMat pr M * (subIncl R pr)ᵀ)
        * (subIncl R pr * subMat pr M * (subIncl R pr)ᵀ)
      = subIncl R pr * subMat pr M * ((subIncl R pr)ᵀ * subIncl R pr)
          * subMat pr M * (subIncl R pr)ᵀ := by simp only [Matrix.mul_assoc]
    _ = subIncl R pr * (subMat pr M * subMat pr M) * (subIncl R pr)ᵀ := by
        rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = subIncl R pr * subMat pr M * (subIncl R pr)ᵀ := by rw [hsub]

/-- If `M` is supported on the pairs `(i,j)` with `pr i ∧ pr j`, then its class in `K₀`
(over the full index type `ι`) equals the class of its compression to the subtype `{i // pr i}`;
here `clsM ι M = clsI M` by definition.  No idempotency hypothesis is needed: `M` is idempotent
exactly when its compression is. -/
theorem clsI_submatrix_of_support {R : Type} [Ring R] {ι : Type} [Fintype ι]
    {pr : ι → Prop} [DecidablePred pr] (M : Matrix ι ι R)
    (hsupp : ∀ i j : ι, ¬ (pr i ∧ pr j) → M i j = 0) :
    Work.KT.Psi.clsM ι M =
      Work.KT.Psi.clsM {i // pr i} (M.submatrix Subtype.val Subtype.val) := by
  classical
  by_cases hM : M * M = M
  · exact clsM_submatrix M hM hsupp
  · have hC : ¬ (subMat pr M * subMat pr M = subMat pr M) :=
      fun hc => hM (idem_of_idem_submatrix M hsupp hc)
    have h1 : clsM ι M = 0 := clsM_eq_zero_of_not_idem hM
    rw [h1]
    exact (clsM_eq_zero_of_not_idem hC).symm

end

end Work.KT.Psi
