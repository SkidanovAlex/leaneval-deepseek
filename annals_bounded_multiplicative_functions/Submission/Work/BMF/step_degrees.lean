import Mathlib
import Submission.Work.BMF.adi_descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Degree bookkeeping for one step of the ADI descent

The descent `dstep p s` replaces the state at level `s.j` by one at level `s.j - 1`.  The point
of the definition -- subtracting `(T_j/2π)·Tay_j` and `μ_j X^j` from `P`, and the top monomial
from `E` and `G` -- is precisely that the new polynomials have degree at most `s.j - 1`.

The three `s.j`-th coefficients are forced to vanish:

* for `P` by the relation `dil a P - dil b P = E + G`, whose `s.j`-th coefficient is
  `(a^j - b^j)·coeff_j P = coeff_j E + coeff_j G`, together with the definitions of `Tval`
  and `muval`;
* for `E` by the choice of `Tval`, which makes the `Tay_j` correction cancel `coeff_j E`;
* for `G` by construction, since `coeff_j G · X^j` is subtracted.
-/

namespace Work.BMF

open Polynomial Finset

/-- `C c * Tay j x` has degree at most `j`. -/
theorem natDegree_C_mul_Tay_le (c x : ℝ) (j : ℕ) : (C c * Tay j x).natDegree ≤ j :=
  le_trans (natDegree_C_mul_le c _) (tay_natDegree_le j x)

/-- A dilate of `Tay j x` has degree at most `j`. -/
theorem natDegree_dil_Tay_le (a x : ℝ) (j : ℕ) : (dil a (Tay j x)).natDegree ≤ j :=
  le_trans (natDegree_dil_le a _) (tay_natDegree_le j x)

/-- Removing the `j`-th coefficient from a polynomial of degree `≤ j` drops the degree
to at most `j - 1`. -/
theorem natDegree_sub_coeff_mul_X_pow_le (Q : ℝ[X]) (j : ℕ) (h : Q.natDegree ≤ j) :
    (Q - C (Q.coeff j) * X ^ j).natDegree ≤ j - 1 := by
  refine natDegree_le_sub_one_of ?_ ?_
  · refine le_trans (natDegree_sub_le _ _) (max_le h ?_)
    calc (C (Q.coeff j) * X ^ j : ℝ[X]).natDegree ≤ (X ^ j : ℝ[X]).natDegree :=
          natDegree_C_mul_le _ _
      _ = j := natDegree_X_pow j
  · simp only [coeff_sub, coeff_C_mul, coeff_X_pow_self, mul_one]
    ring

theorem step_degrees (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    (dstep p s).P.natDegree ≤ s.j - 1 ∧
    (dstep p s).E.natDegree ≤ s.j - 1 ∧
    (dstep p s).G.natDegree ≤ s.j - 1 := by
  obtain ⟨_, _, _, _, _, hx, _, _, _, hba, _, _⟩ := hp
  obtain ⟨_, hPdeg, hEdeg, hGdeg, hrel, _, _, _, _, _, _, _⟩ := hs
  have hBne : (s.j : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.j ≠ 0)
  have hXne : p.x ^ s.j ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  have hQne : ((qj p.a p.b s.j : ℕ) : ℝ) ≠ 0 := by
    have h := qj_pos p.a p.b s.j hba (by omega : 0 < s.j)
    exact_mod_cast (ne_of_gt h)
  have hprod : (s.j : ℝ) * p.x ^ s.j ≠ 0 := mul_ne_zero hBne hXne
  have hπne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hsgn2 : (-1 : ℝ) ^ ((s.j - 1) * 2) = 1 :=
    Even.neg_one_pow ⟨s.j - 1, by ring⟩
  -- the top coefficient of `Tay_j` times `Tval/(2π)` is exactly `coeff_j E / q_j`
  have hA : (Tval p s / (2 * Real.pi)) * (Tay s.j p.x).coeff s.j
      = s.E.coeff s.j / ((qj p.a p.b s.j : ℕ) : ℝ) := by
    rw [tay_coeff_top hj hx]
    unfold Tval
    field_simp [hπne, hprod, hQne, hBne, hXne]
    ring_nf
    rw [hsgn2]
    ring
  -- the top coefficient of `dil a (Tay_j) - dil b (Tay_j)` is `coeff_j Tay_j * q_j`
  have hW : (dil (p.a : ℝ) (Tay s.j p.x) - dil (p.b : ℝ) (Tay s.j p.x)).coeff s.j
      = (Tay s.j p.x).coeff s.j * ((qj p.a p.b s.j : ℕ) : ℝ) := by
    simp only [coeff_sub, coeff_dil]
    rw [qj_cast p.a p.b s.j (le_of_lt hba)]
    ring
  -- the invariant relation at level `s.j`
  have hrel_j : s.P.coeff s.j * (((qj p.a p.b s.j : ℕ) : ℝ))
      = s.E.coeff s.j + s.G.coeff s.j := by
    have h := congrArg (fun Q : ℝ[X] => Q.coeff s.j) hrel
    simp only [coeff_sub, coeff_add, coeff_dil] at h
    rw [qj_cast p.a p.b s.j (le_of_lt hba), mul_sub]
    exact h
  have hP : (s.P - C (Tval p s / (2 * Real.pi)) * Tay s.j p.x
      - C (muval p s) * X ^ s.j).natDegree ≤ s.j - 1 := by
    refine natDegree_le_sub_one_of ?_ ?_
    · refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_sub_le _ _) (max_le hPdeg ?_)
        exact natDegree_C_mul_Tay_le _ _ _
      · calc (C (muval p s) * X ^ s.j : ℝ[X]).natDegree ≤ (X ^ s.j : ℝ[X]).natDegree :=
              natDegree_C_mul_le _ _
          _ = s.j := natDegree_X_pow s.j
    · simp only [coeff_sub, coeff_C_mul, coeff_X_pow_self, mul_one, hA]
      unfold muval
      have hsplit : s.E.coeff s.j / ((qj p.a p.b s.j : ℕ) : ℝ)
          + s.G.coeff s.j / ((qj p.a p.b s.j : ℕ) : ℝ) = s.P.coeff s.j := by
        rw [← add_div, ← hrel_j, mul_div_cancel_right₀ _ hQne]
      linarith [hsplit]
  have hE : (s.E - C (Tval p s / (2 * Real.pi)) *
      (dil (p.a : ℝ) (Tay s.j p.x) - dil (p.b : ℝ) (Tay s.j p.x))
      + C (nval p s : ℝ)).natDegree ≤ s.j - 1 := by
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · refine natDegree_le_sub_one_of ?_ ?_
      · refine le_trans (natDegree_sub_le _ _) (max_le hEdeg ?_)
        refine le_trans (natDegree_C_mul_le _ _) ?_
        refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_) <;>
          exact natDegree_dil_Tay_le _ _ _
      · simp only [coeff_sub, coeff_C_mul, hW]
        rw [← mul_assoc, hA, div_mul_cancel₀ _ hQne]
        ring
    · rw [natDegree_C]; exact Nat.zero_le _
  have hG : (s.G - C (s.G.coeff s.j) * X ^ s.j - C (nval p s : ℝ)).natDegree ≤ s.j - 1 := by
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact natDegree_sub_coeff_mul_X_pow_le s.G s.j hGdeg
    · rw [natDegree_C]; exact Nat.zero_le _
  rw [dstep_P, dstep_E, dstep_G]
  exact ⟨hP, hE, hG⟩

end Work.BMF
