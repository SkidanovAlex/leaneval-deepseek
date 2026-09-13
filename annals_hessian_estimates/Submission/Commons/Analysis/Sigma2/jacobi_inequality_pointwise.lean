import Mathlib
import Submission.Commons.Analysis.Sigma2.jacobi_quad_nonneg_four
import Submission.Commons.Algebra.BigOperators.sum_sq_third_index_decomp_four

namespace Commons.Analysis.Sigma2

open scoped BigOperators

/-- Relabelling identity for the diagonal part of the sum of squares of a symmetric tensor
`b : Fin 4 → Fin 4 → Fin 4 → ℝ` (no symmetry needed here): the sum of the squares of the
"diagonal entries" `b j j i` splits into the off-diagonal contributions `i ≠ j` and the
purely diagonal ones `b i i i`. -/
private lemma T_eq_Q_add_R (b : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, b j j i ^ 2) =
      (∑ i : Fin 4, ∑ j : Fin 4, if i = j then 0 else b i i j ^ 2)
        + (∑ i : Fin 4, b i i i ^ 2) := by
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_four]
  simp
  ring

/-- The sum of squares of the components of a symmetric tensor `b : Fin 4 → Fin 4 → Fin 4 → ℝ`
dominates `3 * (∑_{i,j} b j j i ^ 2) - 2 * (∑_i b i i i ^ 2)`.  Equivalently, writing
`K = ∑_{k,i,j} b k i j ^ 2`, `T = ∑_{i,j} b j j i ^ 2` and `R = ∑_i b i i i ^ 2`, we have
`K - 3 * T + 2 * R = 6 * ∑_{i < j < k} b i j k ^ 2 ≥ 0`.  This is the algebraic heart of the
passage from the second differentiated sigma-2 equation (a bound on `∑_{k,i,j} b k i j ^ 2`)
to the pointwise Jacobi inequality (which only sees the diagonal contractions `b j j i`). -/
theorem sum_third_sq_ge_diag (b : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym1 : ∀ k i j, b k i j = b k j i) (hsym2 : ∀ k i j, b k i j = b i k j) :
    (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, b k i j ^ 2)
      ≥ 3 * (∑ i : Fin 4, ∑ j : Fin 4, b j j i ^ 2) - 2 * (∑ i : Fin 4, b i i i ^ 2) := by
  have hd : (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, b i j k ^ 2)
      = 6 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
              if i < j ∧ j < k then b i j k ^ 2 else 0)
        + 3 * (∑ i : Fin 4, ∑ j : Fin 4, if i = j then 0 else b i i j ^ 2)
        + (∑ i : Fin 4, b i i i ^ 2) :=
    Commons.Algebra.BigOperators.sum_sq_third_index_decomp_four b hsym1 hsym2
  have hTQR : (∑ i : Fin 4, ∑ j : Fin 4, b j j i ^ 2)
      = (∑ i : Fin 4, ∑ j : Fin 4, if i = j then 0 else b i i j ^ 2)
        + (∑ i : Fin 4, b i i i ^ 2) := T_eq_Q_add_R b
  have hP0 : 0 ≤ (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
              if i < j ∧ j < k then b i j k ^ 2 else 0) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    apply Finset.sum_nonneg; intro k _
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  have hperm : (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, b k i j ^ 2)
      = (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, b i j k ^ 2) := by
    simp only [Fin.sum_univ_four]
  linarith [hd, hTQR, hP0, hperm]

/-- The two diagonal contractions of a symmetric tensor `b : Fin 4 → Fin 4 → Fin 4 → ℝ` agree:
`∑_k (∑_i b k i i) ^ 2 = ∑_i (∑_j b j j i) ^ 2`.  Indeed `b` is fully symmetric in its three
indices, so `b k i i = b i i k` for all `i`, and both sides are the sum of the squares of the
trace over one index. -/
theorem sum_third_diag_sq_eq (b : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym1 : ∀ k i j, b k i j = b k j i) (hsym2 : ∀ k i j, b k i j = b i k j) :
    (∑ k : Fin 4, (∑ i : Fin 4, b k i i) ^ 2)
      = (∑ i : Fin 4, (∑ j : Fin 4, b j j i) ^ 2) := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hsym2 k i i, hsym1 i k i]

/- Pointwise almost-Jacobi inequality (Proposition 2.1 of Shankar-Yuan, n = 4) in abstract
coordinate form.  Here `lam` are the (antitone) eigenvalues of the diagonalized Hessian at the
point, `b k i j = u_kij` are the third partial derivatives, `d i = partial_i partial_i (Delta u)`
is the second trace-derivative, `h1` is the first differentiated equation
(`sum_j f_j b_jji = 0`, all i) and `h2` is the second differentiated equation
(`sum_i f_i d_i = sum_{kij} b_kij^2 - sum_k (Delta u_k)^2`).  Conclusion: the quantity
`S * (Delta_F b - eps |grad_F b|^2)` is nonnegative, i.e.
`sum_i f_i d_i - (delta/S) sum_i f_i (Delta u_i)^2 >= 0`, where `S = sigma_1`,
`eps = (2/9)(1/2 + lam 3/S)` and `delta = 1 + eps`.  Proof: rewrite `h2`, split
`sum_{kij} b_kij^2` with `sum_sq_third_index_decomp_four`, apply `jacobi_quad_nonneg_four` to
each `t_i := (b_jji)_j` (constraint `h1 i`), sum over `i`, and identify the resulting terms
(the relabelling `sum_{ij} b_jji^2 = sum_{ij} b_iij^2` and the symmetry-derived
`sum_j b_jji = sum_j b_ijj`). -/
open scoped BigOperators in
theorem jacobi_inequality_pointwise (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) (b : Fin 4 → Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (hsym1 : ∀ k i j, b k i j = b k j i) (hsym2 : ∀ k i j, b k i j = b i k j)
    (h1 : ∀ i : Fin 4, (∑ j : Fin 4, ((∑ t : Fin 4, lam t) - lam j) * b j j i) = 0)
    (h2 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * d i) =
            (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, b k i j ^ 2) -
              (∑ k : Fin 4, (∑ i : Fin 4, b k i i) ^ 2)) :
    let S : ℝ := ∑ t : Fin 4, lam t
    let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
    let δ : ℝ := 1 + eps
    0 ≤ (∑ i : Fin 4, (S - lam i) * d i) -
          (δ / S) * (∑ i : Fin 4, (S - lam i) * (∑ j : Fin 4, b j j i) ^ 2) := by
  dsimp only
  set S : ℝ := ∑ t : Fin 4, lam t with hS
  set eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) with heps
  set δ : ℝ := 1 + eps with hδ
  -- The pointwise almost-Jacobi inequality applied to the vector `t_i := (b j j i)_j`,
  -- whose mean under the weights `f_j = S - lam j` vanishes by the first differentiated
  -- equation `h1 i`.
  have hquad : ∀ i : Fin 4, 0 ≤ 3 * (∑ j : Fin 4, b j j i ^ 2) - 2 * b i i i ^ 2
      - (1 + δ * (S - lam i) / S) * (∑ j : Fin 4, b j j i) ^ 2 := by
    intro i
    exact jacobi_quad_nonneg_four lam hmono hσ2 hσ1 i (fun j => b j j i) (h1 i)
  -- Sum the pointwise inequalities over `i`.
  have hquadsum : 0 ≤ 3 * (∑ i : Fin 4, ∑ j : Fin 4, b j j i ^ 2)
      - 2 * (∑ i : Fin 4, b i i i ^ 2)
      - ∑ i : Fin 4, (1 + δ * (S - lam i) / S) * (∑ j : Fin 4, b j j i) ^ 2 := by
    have h := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hquad i)
    have key : (∑ i : Fin 4, (3 * (∑ j : Fin 4, b j j i ^ 2) - 2 * b i i i ^ 2
        - (1 + δ * (S - lam i) / S) * (∑ j : Fin 4, b j j i) ^ 2))
        = 3 * (∑ i : Fin 4, ∑ j : Fin 4, b j j i ^ 2)
          - 2 * (∑ i : Fin 4, b i i i ^ 2)
          - ∑ i : Fin 4, (1 + δ * (S - lam i) / S) * (∑ j : Fin 4, b j j i) ^ 2 := by
      simp only [Fin.sum_univ_four]
      ring
    rw [key] at h
    exact h
  -- Split the weights `1 + δ f_i / S` into the constant part and the `δ / S` part.
  have hg : (∑ i : Fin 4, (1 + δ * (S - lam i) / S) * (∑ j : Fin 4, b j j i) ^ 2)
      = (∑ i : Fin 4, (∑ j : Fin 4, b j j i) ^ 2)
        + (δ / S) * (∑ i : Fin 4, (S - lam i) * (∑ j : Fin 4, b j j i) ^ 2) := by
    simp only [Fin.sum_univ_four]
    ring
  -- The second differentiated equation, with `S = sigma_1`.
  have h2' : (∑ i : Fin 4, (S - lam i) * d i)
      = (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, b k i j ^ 2)
        - (∑ k : Fin 4, (∑ i : Fin 4, b k i i) ^ 2) := h2
  -- The two finite-sum identities relating the diagonal contractions of `b`.
  have hKge := sum_third_sq_ge_diag b hsym1 hsym2
  have hYZ := sum_third_diag_sq_eq b hsym1 hsym2
  have hfinal : (δ / S) * (∑ i : Fin 4, (S - lam i) * (∑ j : Fin 4, b j j i) ^ 2)
      ≤ (∑ i : Fin 4, (S - lam i) * d i) := by
    linarith [h2', hYZ, hKge, hquadsum, hg]
  linarith [hfinal]

end Commons.Analysis.Sigma2
