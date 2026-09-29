import Mathlib
set_option linter.unusedVariables false

namespace Work.ZeroEst

/-- The determinant of an `m × m` matrix of polynomials, each of `natDegree ≤ N`, has
`natDegree ≤ m * N`.  Via the Leibniz formula `det M = ∑ σ, sign σ • ∏ i, M (σ i) i`:
every summand is a product of `m` entries of degree `≤ N`, hence of degree `≤ m * N`,
and a finite sum of such polynomials again has degree `≤ m * N`. -/
theorem lang24_det_natDegree_le {m : ℕ} (A : Matrix (Fin m) (Fin m) (Polynomial ℚ)) (N : ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ N) : A.det.natDegree ≤ m * N := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  refine (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) _).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc ∑ i ∈ Finset.univ, (A (σ i) i).natDegree
      ≤ ∑ i ∈ Finset.univ, N := Finset.sum_le_sum (fun i _ => h (σ i) i)
    _ = m * N := by simp [Finset.sum_const, Finset.card_univ]

/-- Every entry of the adjugate of a square matrix of polynomials, all of whose entries
have `natDegree ≤ N`, has `natDegree ≤ (n - 1) * N`.  The `(i,j)` entry of the adjugate is
`± det` of an `(n-1) × (n-1)` submatrix of `A`, and determinants of `(n-1) × (n-1)`
matrices with entries of degree `≤ N` have degree `≤ (n-1) * N`
(`lang24_det_natDegree_le`); multiplication by the sign `±1` does not raise the degree.

For `n = 0` there is nothing to prove: there are no indices `i j : Fin 0`. -/
theorem lang24_adjugate_natDegree_le {n : ℕ} (A : Matrix (Fin n) (Fin n) (Polynomial ℚ)) (N : ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ N) : ∀ i j, (A.adjugate i j).natDegree ≤ (n - 1) * N := by
  intro i j
  -- `i : Fin n` forces `n = k + 1`, which removes the `n = 0` case as well as the subtraction.
  obtain ⟨k, rfl⟩ : ∃ k, n = Nat.succ k := ⟨n - 1, by have := i.isLt; omega⟩
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  -- the sign `(-1) ^ (j + i)` is a constant polynomial, of `natDegree 0`
  have hsign : ((-1 : Polynomial ℚ) ^ ((j : ℕ) + (i : ℕ))).natDegree = 0 := by
    have hC : (-1 : Polynomial ℚ) = Polynomial.C (-1) := by simp
    rw [hC, ← Polynomial.C_pow, Polynomial.natDegree_C]
  -- the complementary minor is a `k × k` determinant of entries of `A`
  have hdet : (A.submatrix j.succAbove i.succAbove).det.natDegree ≤ k * N :=
    lang24_det_natDegree_le _ N (fun a b => h (j.succAbove a) (i.succAbove b))
  calc (((-1 : Polynomial ℚ) ^ ((j : ℕ) + (i : ℕ)))
          * (A.submatrix j.succAbove i.succAbove).det).natDegree
      ≤ ((-1 : Polynomial ℚ) ^ ((j : ℕ) + (i : ℕ))).natDegree
          + (A.submatrix j.succAbove i.succAbove).det.natDegree := Polynomial.natDegree_mul_le
    _ = (A.submatrix j.succAbove i.succAbove).det.natDegree := by rw [hsign, zero_add]
    _ ≤ k * N := hdet

/-- Degree bound for a linear combination of the rows of `M` mediated by the adjugate of `S`:
each of the `r` summands `S.adjugate l a * M (k0 a) j` is a product of an adjugate entry of
degree `≤ (r-1) * N` with an entry of `M` of degree `≤ N`, hence of degree `≤ r * N`. -/
theorem lang24_degree {r m : ℕ} (S : Matrix (Fin r) (Fin r) (Polynomial ℚ))
    (M : Matrix (Fin m) (Fin m) (Polynomial ℚ)) (k0 : Fin r → Fin m) (N : ℕ) (hN : 1 ≤ N)
    (hS : ∀ a b, (S a b).natDegree ≤ N) (hM : ∀ i j, (M i j).natDegree ≤ N) :
    ∀ l j, (∑ a, S.adjugate l a * M (k0 a) j).natDegree ≤ r * N := by
  intro l j
  -- `l : Fin r` forces `r = k + 1`, so that `r * N = k * N + N`.
  obtain ⟨k, rfl⟩ : ∃ k, r = Nat.succ k := ⟨r - 1, by have := l.isLt; omega⟩
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hadj : (S.adjugate l a).natDegree ≤ k * N := lang24_adjugate_natDegree_le S N hS l a
  have hM' : (M (k0 a) j).natDegree ≤ N := hM _ _
  calc (S.adjugate l a).natDegree + (M (k0 a) j).natDegree
      ≤ k * N + N := add_le_add hadj hM'
    _ = Nat.succ k * N := by rw [Nat.succ_mul]

end Work.ZeroEst
