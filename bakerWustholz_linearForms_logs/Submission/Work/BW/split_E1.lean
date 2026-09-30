import Mathlib
import Submission.Work.BW.split_aux
import Submission.Work.BW.split_E1_case0
import Submission.Work.BW.split_E1_casepos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1600000

namespace Work.BW

theorem split_E1 {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, calD r d h σ i ^ e i <
        ((halfSplit r (calS r d h) m : ℝ) + 1) *
          ((halfSplit r (calT r d σ) m + m + 1).choose (m + 1) : ℝ) := by
  intro m hm e he hsum
  have hr0 : (0:ℝ) < (r:ℝ) := by
    have h : (0:ℕ) < r := by omega
    exact_mod_cast h
  set M : ℝ := pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)) with hM
  have hM0 : 0 ≤ M := by rw [hM]; exact div_nonneg (le_of_lt (pD_pos hr hd σ hσ)) (by positivity)
  have hMle : M ≤ calD r d h σ 0 := by rw [hM]; exact M_le_calD_zero hr hd h hh σ hσ
  have hc0 : (0:ℝ) ≤ calD r d h σ 0 := calD_nonneg r d h σ 0
  have hcj0 : ∀ j : Fin r, (0:ℝ) ≤ calD r d h σ j.succ := fun j => calD_nonneg r d h σ j.succ
  have hcj : ∀ j : Fin r, calD r d h σ j.succ ≤ M := by
    intro j; rw [hM]; exact calD_succ_le_M hr hd h σ hσ j
  have hprodb : ∏ i, calD r d h σ i ^ e i ≤ calD r d h σ 0 * M ^ m :=
    prod_pow_one_le he hsum hM0 hMle hc0 hcj0 hcj
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hprod0 : ∏ i, calD r d h σ i ^ e i ≤ calD r d h σ 0 := by
      simpa using hprodb
    have h1 : ((r:ℝ)+1) * ∏ i, calD r d h σ i ^ e i ≤ ((r:ℝ)+1) * calD r d h σ 0 :=
      mul_le_mul_of_nonneg_left hprod0 (by positivity)
    have h2 : calS r d h / 2 ≤ ((halfSplit r (calS r d h) 0 : ℝ)) + 1 := by
      rw [halfSplit_zero]; exact le_of_lt (Nat.lt_floor_add_one _)
    have h3 : calT r d σ / 2 ≤ ((halfSplit r (calT r d σ) 0 : ℝ)) + 1 := by
      rw [halfSplit_zero]; exact le_of_lt (Nat.lt_floor_add_one _)
    have h4 : (calS r d h / 2) * (calT r d σ / 2) ≤
        (((halfSplit r (calS r d h) 0 : ℝ)) + 1) * (((halfSplit r (calT r d σ) 0 : ℝ)) + 1) :=
      mul_le_mul h2 h3 (div_nonneg (calT_nonneg r d σ) (by norm_num)) (by positivity)
    have h5 : ((r:ℝ)+1) * calD r d h σ 0 < (calS r d h / 2) * (calT r d σ / 2) :=
      split_E1_case0 hr hd hh σ hσ
    have hdf : (((r+1).descFactorial (0+1) : ℕ) : ℝ) = (r:ℝ)+1 := by
      rw [Nat.descFactorial_one]; push_cast; ring
    have hch0 : (((halfSplit r (calT r d σ) 0 + 0 + 1).choose (0+1) : ℕ) : ℝ) =
        ((halfSplit r (calT r d σ) 0 : ℝ)) + 1 := by
      rw [Nat.choose_one_right]; push_cast; ring
    rw [hdf, hch0]
    linarith
  · have hm0' : m ≠ 0 := by omega
    have hm1 : 1 ≤ m := by omega
    have hLHS : ((r+1).descFactorial (m+1) : ℝ) * ∏ i, calD r d h σ i ^ e i
        ≤ ((r+1).descFactorial (m+1) : ℝ) * calD r d h σ 0 * M ^ m := by
      calc ((r+1).descFactorial (m+1) : ℝ) * ∏ i, calD r d h σ i ^ e i
          ≤ ((r+1).descFactorial (m+1) : ℝ) * (calD r d h σ 0 * M ^ m) :=
            mul_le_mul_of_nonneg_left hprodb (by positivity)
        _ = ((r+1).descFactorial (m+1) : ℝ) * calD r d h σ 0 * M ^ m := by ring
    have hcore' : ((r+1).descFactorial (m+1) : ℝ) * calD r d h σ 0 * M ^ m
        < (calS r d h / (2*(r:ℝ))) * (calT r d σ / (2*(r:ℝ)))^(m+1) /
            ((m+1).factorial : ℝ) := by
      rw [hM]; exact split_E1_casepos hr hd hh σ hσ m hm1 hm
    have hSq : calS r d h / (2*(r:ℝ)) ≤ ((halfSplit r (calS r d h) m : ℝ)) + 1 := by
      rw [halfSplit_ne_zero hm0' (calS r d h)]
      exact le_of_lt (Nat.lt_floor_add_one _)
    have hTq : calT r d σ / (2*(r:ℝ)) ≤ ((halfSplit r (calT r d σ) m : ℝ)) + 1 := by
      rw [halfSplit_ne_zero hm0' (calT r d σ)]
      exact le_of_lt (Nat.lt_floor_add_one _)
    have hfac : (0:ℝ) < ((m+1).factorial : ℝ) := by positivity
    have hch : (((halfSplit r (calT r d σ) m : ℝ)) + 1)^(m+1) ≤
        ((halfSplit r (calT r d σ) m + m + 1).choose (m+1) : ℝ) * ((m+1).factorial : ℝ) := by
      have h := choose_lower (halfSplit r (calT r d σ) m) (m+1)
      rw [div_le_iff₀ hfac] at h
      have harg : halfSplit r (calT r d σ) m + (m+1) = halfSplit r (calT r d σ) m + m + 1 := by omega
      rw [harg] at h
      simpa only [Nat.cast_add, Nat.cast_one] using h
    have hRHS : (calS r d h / (2*(r:ℝ))) * (calT r d σ / (2*(r:ℝ)))^(m+1) / ((m+1).factorial : ℝ)
        ≤ ((halfSplit r (calS r d h) m : ℝ) + 1) *
          ((halfSplit r (calT r d σ) m + m + 1).choose (m+1) : ℝ) := by
      have h1 : (calS r d h / (2*(r:ℝ))) * (calT r d σ / (2*(r:ℝ)))^(m+1) / ((m+1).factorial:ℝ)
          ≤ (((halfSplit r (calS r d h) m : ℝ)) + 1) * ((((halfSplit r (calT r d σ) m : ℝ)) + 1)^(m+1)) / ((m+1).factorial:ℝ) := by
        apply div_le_div_of_nonneg_right _ hfac.le
        exact mul_le_mul hSq (pow_le_pow_left₀ (div_nonneg (calT_nonneg r d σ) (by positivity)) hTq (m+1))
          (pow_nonneg (div_nonneg (calT_nonneg r d σ) (by positivity)) _) (by positivity)
      have h2 : (((halfSplit r (calS r d h) m : ℝ)) + 1) * ((((halfSplit r (calT r d σ) m : ℝ)) + 1)^(m+1)) / ((m+1).factorial:ℝ)
          ≤ ((halfSplit r (calS r d h) m : ℝ) + 1) * ((halfSplit r (calT r d σ) m + m + 1).choose (m+1) : ℝ) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hfac]
        exact hch
      linarith
    linarith [hLHS, hcore', hRHS]

end Work.BW

