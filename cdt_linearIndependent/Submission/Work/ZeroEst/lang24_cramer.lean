import Mathlib
import Submission.Work.ZeroEst.case_det_cramer

namespace Work.ZeroEst

/-!
# Cramer's rule for a spanning set of columns (`lang24_cramer`)

Let `M` be an `m × m` matrix over a field whose column indexed by `V : Fin r → Fin m` span all
columns of `M` (`hspan`).  Then there are coefficients `lam l j` expressing the `j`-th column of
`M` in the spanning columns:
`M k j = ∑ l, lam l j * M k (V l)`.

Moreover the *only* such coefficients are given by Cramer's rule applied to the submatrix
`M.submatrix k0 V` (rows `k0`, columns `V`): for any `k0`,
`(M.submatrix k0 V).det * lam l j = ∑ a, (M.submatrix k0 V).adjugate l a * M (k0 a) j`.

The mathematics is the single identity `adj(N) * N = det N • 1` for the auxiliary matrix
`N = M.submatrix k0 V` (Mathlib's `Matrix.adjugate_mul`, packaged as `cramer_aux`).  Note that the
nonvanishing hypothesis `hdet` of the statement is *not* needed for the conclusion: the second
clause is the adjugate identity, which holds for every square matrix.
-/

/-- **Cramer coefficients for a spanning family of columns.**  If the columns `M.col (V b)`
(`b : Fin r`) span every column of `M`, then there is a family `lam` with
`M.col j = ∑ l, lam l j • M.col (V l)`, and any such `lam` is computed from the submatrix
`M.submatrix k0 V` by the adjugate identity. -/
theorem lang24_cramer {K : Type*} [Field K] {m r : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (V k0 : Fin r → Fin m) (hdet : (M.submatrix k0 V).det ≠ 0)
    (hspan : ∀ j : Fin m, M.col j ∈ Submodule.span K (Set.range fun b : Fin r => M.col (V b))) :
    ∃ lam : Fin r → Fin m → K,
      (∀ j k, M k j = ∑ l, lam l j * M k (V l)) ∧
      (∀ l j, (M.submatrix k0 V).det * lam l j
        = ∑ a, (M.submatrix k0 V).adjugate l a * M (k0 a) j) := by
  classical
  have _ : (M.submatrix k0 V).det ≠ 0 := hdet
  -- Each column of `M` is a linear combination of the spanning columns.
  have hex : ∀ j : Fin m, ∃ c : Fin r → K, ∀ k, M k j = ∑ l, c l * M k (V l) := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan j)
    refine ⟨c, fun k => ?_⟩
    have hk := congr_fun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at hk
    exact hk.symm
  choose c hc using hex
  refine ⟨fun l j => c j l, fun j k => ?_, fun l j => ?_⟩
  · simpa using hc j k
  · -- Cramer: `N *ᵥ (fun i => c j i) = (fun a => M (k0 a) j)`, `adj N * N = det N • 1`.
    have key : ∀ a : Fin r,
        ∑ i, (M.submatrix k0 V) a i * (fun i => c j i) i = M (k0 a) j := by
      intro a
      rw [hc j (k0 a)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Matrix.submatrix_apply]
      ring
    have h := cramer_aux (M.submatrix k0 V) (fun i => c j i) l
    rw [h]
    exact Finset.sum_congr rfl (fun a _ => by rw [key a])

end Work.ZeroEst
