/-
  Work.WilE2 — area E2.  Facts about the "sphere" equation used in the Khovanskii sphere step.

  `spherePoly c = ∑_k x_k² + ψ_s² - c` in `n+1` ambient coordinates and `s+1` chain functions.
  This module proves the three facts needed downstream: its total degree is `≤ 2`, its evaluation
  along the (extended) chain `S.ravel` is `∑_k z_k² + ψ_s(init z)² - c`, and its derivative
  `∂_{x_n}` equals `2 x_n` (the other chain contributions vanish because `ravel` does not depend on
  the new coordinate).
-/
import Mathlib
import Submission.Work.WilE2.KhoSphereDefs

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-- `∂_{x_i}` of the sum of squares `∑_k x_k²` is `2 x_i`. -/
lemma pderiv_inl_sumSq (i : Fin (n + 1)) :
    MvPolynomial.pderiv (Sum.inl i)
        (∑ k : Fin (n + 1), MvPolynomial.X (Sum.inl k) * MvPolynomial.X (Sum.inl k) :
          EPoly (n + 1) (s + 1))
      = 2 * MvPolynomial.X (Sum.inl i) := by
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
    ring
  · intro b _ hb
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (by simpa using hb)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `∂_{x_i}` of a chain square `ψ_j²` is zero, since the derivative is taken in an `x`-direction. -/
lemma pderiv_inl_inr_sq (i : Fin (n + 1)) (j : Fin (s + 1)) :
    MvPolynomial.pderiv (Sum.inl i)
        (MvPolynomial.X (Sum.inr j) * MvPolynomial.X (Sum.inr j) : EPoly (n + 1) (s + 1)) = 0 := by
  rw [MvPolynomial.pderiv_mul]
  simp [MvPolynomial.pderiv_X, Pi.single_eq_of_ne]

theorem spherePoly_facts {n s : ℕ} (S : ESys n (s + 1)) (c : ℝ) :
    ((spherePoly (n := n) (s := s) c).totalDegree ≤ 2) ∧
    (∀ z : Fin (n + 1) → ℝ, (S.ravel).ev (spherePoly (n := n) (s := s) c) z =
      (∑ k : Fin (n + 1), (z k) ^ 2) + (S.psi (Fin.last s) (Fin.init z)) ^ 2 - c) ∧
    ((S.ravel).d (Fin.last n) (spherePoly (n := n) (s := s) c)
      = MvPolynomial.C (2 : ℝ) * MvPolynomial.X (Sum.inl (Fin.last n))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- total degree at most `2`: a sum of squares plus a constant
    rw [spherePoly]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
        rw [Finset.sup_le_iff]
        intro k _
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp [MvPolynomial.totalDegree_X]
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp [MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]
      norm_num
  · -- evaluation along the extended chain
    intro z
    simp only [spherePoly, ESys.ev, map_add, map_mul, map_sum, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Sum.elim_inl, Sum.elim_inr]
    rw [ESys.ravel_psi]
    simp [sq, sub_eq_add_neg]
  · -- derivative in the new coordinate
    rw [ESys.d, spherePoly]
    have hsum : (∑ j : Fin (s + 1), MvPolynomial.C ((S.ravel).a j (Fin.last n)) *
        MvPolynomial.X (Sum.inr j) *
        MvPolynomial.pderiv (Sum.inr j)
          ((∑ k : Fin (n + 1), MvPolynomial.X (Sum.inl k) * MvPolynomial.X (Sum.inl k)) +
            MvPolynomial.X (Sum.inr (Fin.last s)) * MvPolynomial.X (Sum.inr (Fin.last s)) +
            MvPolynomial.C (-c) : EPoly (n + 1) (s + 1))) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ESys.ravel_a_last, MvPolynomial.C_0, zero_mul, zero_mul]
    rw [hsum, add_zero]
    rw [map_add, map_add, pderiv_inl_sumSq, pderiv_inl_inr_sq, MvPolynomial.pderiv_C]
    rw [show (2 : EPoly (n + 1) (s + 1)) = MvPolynomial.C (2 : ℝ) from
      (map_ofNat (MvPolynomial.C : ℝ →+* MvPolynomial (Fin (n + 1) ⊕ Fin (s + 1)) ℝ) 2).symm]
    simp

end Work.WilE2
