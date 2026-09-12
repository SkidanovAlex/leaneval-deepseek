import Mathlib
import Submission.Cwnorm
import Submission.RemezComplex

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.SqfRemez

open Submission.Cwnorm

/-- Iterating `complex_remez` over the linear factors of a divisor `H` bounds
the `cwnorm n` of the cofactor `A`. -/
theorem remez_chain (C : ℝ) (hCpos : 0 < C)
    (hCR : ∀ (N m : ℕ), 1 ≤ m →
      ∀ (P : Polynomial ℂ), P.natDegree = m → ∀ α : ℂ, P.eval α = 0 →
        ∃ Q : Polynomial ℂ, P = (Polynomial.X - Polynomial.C α) * Q ∧
          cwnorm N Q ≤ ((2 * max N m : ℕ) : ℝ) ^ C * cwnorm N P)
    {n : ℕ} (hn2 : 2 ≤ n) (H A : Polynomial ℂ) (hH : H ≠ 0) (hA : A ≠ 0)
    (hdeg : (H * A).natDegree ≤ n) (hlc : 1 ≤ ‖H.leadingCoeff‖) :
    cwnorm n A ≤ ((2 * n : ℕ) : ℝ) ^ (C * (H.natDegree : ℝ)) * cwnorm n (H * A) := by
  classical
  have h2npos : 0 < ((2 * n : ℕ) : ℝ) := by
    have hn0 : 0 < 2 * n := by omega
    exact_mod_cast hn0
  let Ppol : ℕ → Prop := fun d =>
    ∀ (H A : Polynomial ℂ), H ≠ 0 → A ≠ 0 → H.natDegree = d →
      (H * A).natDegree ≤ n → 1 ≤ ‖H.leadingCoeff‖ →
        cwnorm n A ≤ ((2 * n : ℕ) : ℝ) ^ (C * (d : ℝ)) * cwnorm n (H * A)
  have hPol : ∀ d : ℕ, Ppol d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro H A hH hA hd hdeg hlc
        by_cases hd0 : d = 0
        · -- d = 0 : H is a nonzero constant
          have hdeg0 : H.natDegree = 0 := by omega
          have hcoeff : H.coeff 0 = H.leadingCoeff := by
            simp [Polynomial.leadingCoeff, hdeg0]
          have hC : H = Polynomial.C H.leadingCoeff := by
            rw [← hcoeff]
            exact Polynomial.eq_C_of_natDegree_eq_zero hdeg0
          have hHA : H * A = H.leadingCoeff • A := by
            conv_lhs => rw [hC]
            rw [Polynomial.smul_eq_C_mul]
          have hlcA : cwnorm n A ≤ cwnorm n (H * A) := by
            calc
              cwnorm n A = 1 * cwnorm n A := by ring
              _ ≤ ‖H.leadingCoeff‖ * cwnorm n A := by
                  exact mul_le_mul_of_nonneg_right hlc (cwnorm_nonneg n A)
              _ = cwnorm n (H.leadingCoeff • A) := by rw [cwnorm_smul]
              _ = cwnorm n (H * A) := by rw [hHA]
          have hexp : C * (d : ℝ) = 0 := by rw [hd0]; norm_num
          calc
            cwnorm n A ≤ cwnorm n (H * A) := hlcA
            _ = ((2 * n : ℕ) : ℝ) ^ (C * (d : ℝ)) * cwnorm n (H * A) := by
                rw [hexp]
                rw [Real.rpow_zero]
                ring
        · -- d ≥ 1 : H has a root; remove one linear factor
          have hdpos : 0 < d := by omega
          have hdgt : 0 < H.natDegree := by omega
          have hdegpos : 0 < H.degree := (Polynomial.natDegree_pos_iff_degree_pos).mp hdgt
          rcases Complex.exists_root hdegpos with ⟨α, hα⟩
          have hα0 : H.eval α = 0 := by simpa using hα
          have hdvd : (Polynomial.X - Polynomial.C α) ∣ H :=
            (Polynomial.dvd_iff_isRoot).mpr (by simpa using hα)
          rcases hdvd with ⟨H₁, hfacH⟩
          have hXne : (Polynomial.X - Polynomial.C α : Polynomial ℂ) ≠ 0 := by
            intro hX0
            have : (Polynomial.X - Polynomial.C α : Polynomial ℂ).natDegree = 0 := by
              rw [hX0]
              simp
            rw [Polynomial.natDegree_X_sub_C] at this
            norm_num at this
          have hH1ne : H₁ ≠ 0 := by
            intro hH10
            apply hH
            rw [hfacH, hH10, mul_zero]
          have hdegProd : H.natDegree = (Polynomial.X - Polynomial.C α).natDegree + H₁.natDegree := by
            rw [hfacH]
            exact Polynomial.natDegree_mul hXne hH1ne
          have hdeg1 : H₁.natDegree = d - 1 := by
            have hdegProd' : H.natDegree = 1 + H₁.natDegree := by
              rw [hfacH, Polynomial.natDegree_mul hXne hH1ne, Polynomial.natDegree_X_sub_C]
            omega
          have hAne' : A ≠ 0 := hA
          have hH1Ane : H₁ * A ≠ 0 := mul_ne_zero hH1ne hAne'
          have hHAeq : H * A = (Polynomial.X - Polynomial.C α) * (H₁ * A) := by
            calc
              H * A = ((Polynomial.X - Polynomial.C α) * H₁) * A := by rw [hfacH]
              _ = (Polynomial.X - Polynomial.C α) * (H₁ * A) := by rw [mul_assoc]
          have hdegHA : (H * A).natDegree = 1 + (H₁ * A).natDegree := by
            rw [hHAeq, Polynomial.natDegree_mul hXne hH1Ane, Polynomial.natDegree_X_sub_C]
          have hm : 1 ≤ (H * A).natDegree := by omega
          have hdeg' : (H₁ * A).natDegree ≤ n := by omega
          have hlc' : 1 ≤ ‖H₁.leadingCoeff‖ := by
            have hlcEq : H₁.leadingCoeff = H.leadingCoeff := by
              rw [hfacH]
              rw [Polynomial.leadingCoeff_monic_mul (Polynomial.monic_X_sub_C α)]
            simpa [hlcEq]
          have hPα : (H * A).eval α = 0 := by
            rw [Polynomial.eval_mul, hα0]
            ring
          rcases hCR n (H * A).natDegree hm (H * A) rfl α hPα with ⟨Q, hfacP, hQbound⟩
          have hmax : max n (H * A).natDegree = n := by omega
          have hQbound' : cwnorm n Q ≤ ((2 * n : ℕ) : ℝ) ^ C * cwnorm n (H * A) := by
            simpa [hmax] using hQbound
          have hQA : H₁ * A = Q := by
            apply mul_left_cancel₀ hXne
            calc
              (Polynomial.X - Polynomial.C α) * (H₁ * A) = H * A := by rw [← hHAeq]
              _ = (Polynomial.X - Polynomial.C α) * Q := hfacP
          have hlt : d - 1 < d := by omega
          have ih_res : cwnorm n A ≤
              ((2 * n : ℕ) : ℝ) ^ (C * ((d - 1 : ℕ) : ℝ)) * cwnorm n (H₁ * A) := by
            exact ih (d - 1) hlt H₁ A hH1ne hAne' hdeg1 hdeg' hlc'
          have hpd : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := Nat.cast_pred (R := ℝ) hdpos
          have hcd : C * ((d - 1 : ℕ) : ℝ) + C = C * (d : ℝ) := by
            rw [hpd]
            ring
          calc
            cwnorm n A ≤ ((2 * n : ℕ) : ℝ) ^ (C * ((d - 1 : ℕ) : ℝ)) * cwnorm n (H₁ * A) := ih_res
            _ = ((2 * n : ℕ) : ℝ) ^ (C * ((d - 1 : ℕ) : ℝ)) * cwnorm n Q := by rw [hQA]
            _ ≤ ((2 * n : ℕ) : ℝ) ^ (C * ((d - 1 : ℕ) : ℝ)) *
                  (((2 * n : ℕ) : ℝ) ^ C * cwnorm n (H * A)) := by
                exact mul_le_mul_of_nonneg_left hQbound'
                  (Real.rpow_nonneg (le_of_lt h2npos) (C * ((d - 1 : ℕ) : ℝ)))
            _ = ((2 * n : ℕ) : ℝ) ^ (C * ((d - 1 : ℕ) : ℝ) + C) * cwnorm n (H * A) := by
                rw [← mul_assoc]
                rw [← Real.rpow_add h2npos (C * ((d - 1 : ℕ) : ℝ)) C]
            _ = ((2 * n : ℕ) : ℝ) ^ (C * (d : ℝ)) * cwnorm n (H * A) := by
                rw [hcd]
  exact hPol (H.natDegree) H A hH hA rfl hdeg hlc

end Submission.SqfRemez
