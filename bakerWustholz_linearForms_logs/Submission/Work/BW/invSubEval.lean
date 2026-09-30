import Mathlib
import Submission.Work.BW.stabAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `∏ (gᵢ)ᴷ` factor times the `ginv g`-monomials collapses to the
`K`-shifted monomials, using `s i.succ ≤ K` and `g i.succ ≠ 0`. -/
lemma prod_ginv_aux {N : ℕ} (K : ℕ) (g : Fin (N + 1) → ℂ) (hg : InG g)
    (s : Fin (N + 1) →₀ ℕ) (hs : ∀ i : Fin N, s i.succ ≤ K) :
    (∏ i : Fin N, (g i.succ) ^ K) *
        (∏ j : Fin (N + 1), (ginv g j) ^ (s j)) =
      (-g 0) ^ (s 0) * ∏ i : Fin N, (g i.succ) ^ (K - s i.succ) := by
  rw [Fin.prod_univ_succ (fun j : Fin (N + 1) => (ginv g j) ^ (s j))]
  simp only [ginv, Fin.cons_zero, Fin.cons_succ]
  have hAC : (∏ i : Fin N, (g i.succ) ^ K) * (∏ i : Fin N, ((g i.succ)⁻¹) ^ (s i.succ))
      = ∏ i : Fin N, (g i.succ) ^ (K - s i.succ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [inv_pow, ← pow_sub₀ (g i.succ) (hg i) (hs i)]
  rw [← hAC]
  ring

/-- Reducing the LHS to a sum over the support of `q`. -/
lemma eval_invSub {N : ℕ} (q : MvPolynomial (Fin (N + 1)) ℂ) (K : ℕ)
    (g : Fin (N + 1) → ℂ) :
    MvPolynomial.eval g (invSub K q) =
      ∑ s ∈ q.support, q.coeff s * (-g 0) ^ (s 0) *
        ∏ i : Fin N, (g i.succ) ^ (K - s i.succ) := by
  rw [invSub, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [map_mul, map_pow, map_neg, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- Reducing the RHS to the same sum over the support of `q`. -/
lemma mul_eval_ginv {N : ℕ} (q : MvPolynomial (Fin (N + 1)) ℂ) (K : ℕ)
    (hK : ∀ s ∈ q.support, ∀ i : Fin N, s i.succ ≤ K) (g : Fin (N + 1) → ℂ) (hg : InG g) :
    (∏ i : Fin N, (g i.succ) ^ K) * MvPolynomial.eval (ginv g) q =
      ∑ s ∈ q.support, q.coeff s * (-g 0) ^ (s 0) *
        ∏ i : Fin N, (g i.succ) ^ (K - s i.succ) := by
  rw [MvPolynomial.eval_eq' (ginv g) q, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have h := prod_ginv_aux K g hg s (hK s hs)
  calc (∏ i : Fin N, (g i.succ) ^ K) *
          (q.coeff s * ∏ j : Fin (N + 1), (ginv g j) ^ (s j))
      = q.coeff s * ((∏ i : Fin N, (g i.succ) ^ K) *
          ∏ j : Fin (N + 1), (ginv g j) ^ (s j)) := by ring
    _ = q.coeff s * ((-g 0) ^ (s 0) * ∏ i : Fin N, (g i.succ) ^ (K - s i.succ)) := by rw [h]
    _ = q.coeff s * (-g 0) ^ (s 0) * ∏ i : Fin N, (g i.succ) ^ (K - s i.succ) := by ring

theorem invSubEval {N : ℕ} (q : MvPolynomial (Fin (N + 1)) ℂ) (K : ℕ)
    (hK : ∀ s ∈ q.support, ∀ i : Fin N, s i.succ ≤ K) (g : Fin (N + 1) → ℂ) (hg : InG g) :
    MvPolynomial.eval g (invSub K q) =
      (∏ i : Fin N, (g i.succ) ^ K) * MvPolynomial.eval (ginv g) q := by
  rw [eval_invSub]
  exact (mul_eval_ginv q K hK g hg).symm

end Work.BW
