import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq_coeff1
import Submission.Work.KMTPlan.A6.KernComp_khalf_eq

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral Polynomial
open scoped BigOperators ENNReal

noncomputable section

/-- `symSeq κ` is continuous when `κ` is summable: uniform convergence of the defining series. -/
lemma symConc_continuous_symSeq {κ : ℤ → ℂ} (hκ : Summable κ) : Continuous (symSeq κ) := by
  unfold symSeq
  exact continuous_tsum (u := fun p : ℤ => ‖κ p‖)
    (fun p => continuous_const.mul (by unfold eeC; fun_prop)) hκ.norm
    (fun p x => by simp [norm_eeC])

/-- Orthogonality of the sequence symbol against a character:
`∫₀¹ symSeq κ x * e(m x) dx = κ (-m)`. -/
lemma symConc_integral_symSeq_mul_char {κ : ℤ → ℂ} (hκ : Summable κ) (m : ℤ) :
    ∫ x in (0 : ℝ)..1, symSeq κ x * eeC ((m : ℝ) * x) = κ (-m) := by
  have h := SymSeq_coeff1 hκ (-m)
  rw [coeff1] at h
  have key : ∀ x : ℝ, eeC ((m : ℝ) * x) = eeC (-(((↑(-m) : ℤ) : ℝ)) * x) := by
    intro x; congr 1; push_cast; ring
  simp only [key]
  exact h

/-- The double integral over `[0,1]²` of a finite separable sum factorises. -/
lemma symConc_sep_integral_finset {ι : Type*} (s : Finset ι) (A B : ι → ℝ → ℂ)
    (hA : ∀ n, Continuous (A n)) (hB : ∀ n, Continuous (B n)) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∑ n ∈ s, A n x * B n y)
      = ∑ n ∈ s, (∫ x in (0 : ℝ)..1, A n x) * (∫ y in (0 : ℝ)..1, B n y) := by
  have hinner : ∀ x : ℝ, (∫ y in (0 : ℝ)..1, ∑ n ∈ s, A n x * B n y)
      = ∑ n ∈ s, A n x * (∫ y in (0 : ℝ)..1, B n y) := by
    intro x
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun n _ => intervalIntegral.integral_const_mul (A n x) (B n)
    · intro n _
      exact (continuous_const.mul (hB n)).intervalIntegrable 0 1
  simp_rw [hinner]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun n _ => intervalIntegral.integral_mul_const _ (A n)
  · intro n _
    exact ((hA n).mul_const _).intervalIntegrable 0 1

/-- The Fourier coefficient `coeff2` of `symSeq κ x * symSeq κ' y * halfSym N P x y` is the
finite convolution over the support of the halved average. -/
theorem symConc_coeff2 (κ κ' : ℤ → ℂ) (hκ : Summable κ) (hκ' : Summable κ')
    (N : ℕ) (P : Polynomial ℤ) (i j : ℤ) :
    coeff2 (fun x y => symSeq κ x * symSeq κ' y * halfSym N P x y) i j
      = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          κ (i - (n : ℤ)) * κ' (j - P.eval (n : ℤ)) := by
  have hchar : ∀ (n : ℕ) (x y : ℝ),
      eeC ((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y)
        * eeC (-(i : ℝ) * x - (j : ℝ) * y)
        = eeC (((n : ℝ) - (i : ℝ)) * x)
          * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y) := by
    intro n x y
    calc eeC ((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y)
          * eeC (-(i : ℝ) * x - (j : ℝ) * y)
        = eeC (((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y)
            + (-(i : ℝ) * x - (j : ℝ) * y)) := (eeC_add _ _).symm
      _ = eeC (((n : ℝ) - (i : ℝ)) * x
            + ((((P.eval (n : ℤ) : ℤ) : ℝ)) - (j : ℝ)) * y) := by
          congr 1
          ring
      _ = eeC (((n : ℝ) - (i : ℝ)) * x)
          * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y) := eeC_add _ _
  have hpt : ∀ x y : ℝ,
      symSeq κ x * symSeq κ' y * halfSym N P x y * eeC (-(i : ℝ) * x - (j : ℝ) * y)
        = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
              * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y)) := by
    intro x y
    calc symSeq κ x * symSeq κ' y * halfSym N P x y * eeC (-(i : ℝ) * x - (j : ℝ) * y)
        = ((N : ℂ))⁻¹ * ((symSeq κ x * symSeq κ' y)
            * (∑ n ∈ Finset.Ioc (N / 2) N,
                eeC ((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y))
            * eeC (-(i : ℝ) * x - (j : ℝ) * y)) := by
          simp only [halfSym]; ring
      _ = ((N : ℂ))⁻¹ * (∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * symSeq κ' y)
              * eeC ((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y)
              * eeC (-(i : ℝ) * x - (j : ℝ) * y)) := by
          congr 1
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
              * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          calc (symSeq κ x * symSeq κ' y)
                * eeC ((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y)
                * eeC (-(i : ℝ) * x - (j : ℝ) * y)
              = (symSeq κ x * symSeq κ' y)
                * (eeC ((n : ℝ) * x + (((P.eval (n : ℤ) : ℤ) : ℝ)) * y)
                  * eeC (-(i : ℝ) * x - (j : ℝ) * y)) := by ring
            _ = (symSeq κ x * symSeq κ' y)
                * (eeC (((n : ℝ) - (i : ℝ)) * x)
                  * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y)) := by
                  rw [hchar n x y]
            _ = (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
                * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y)) := by ring
  have h1 : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
        = κ (i - (n : ℤ)) := by
    intro n
    have key : ∀ x : ℝ, eeC (((n : ℝ) - (i : ℝ)) * x)
        = eeC ((((n : ℤ) - i : ℤ) : ℝ) * x) := by
      intro x; congr 1; push_cast; ring
    simp only [key]
    rw [symConc_integral_symSeq_mul_char hκ ((n : ℤ) - i)]
    congr 1
    ring
  have h2 : ∀ n : ℕ,
      (∫ y in (0 : ℝ)..1, symSeq κ' y
          * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y))
        = κ' (j - P.eval (n : ℤ)) := by
    intro n
    have key : ∀ y : ℝ, eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y)
        = eeC ((((P.eval (n : ℤ) - j : ℤ)) : ℝ) * y) := by
      intro y; congr 1; push_cast; ring
    simp only [key]
    rw [symConc_integral_symSeq_mul_char hκ' (P.eval (n : ℤ) - j)]
    congr 1
    ring
  simp only [coeff2]
  simp_rw [hpt]
  have hc1 : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ((N : ℂ))⁻¹
        * (∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
              * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y))))
      = ∫ x in (0 : ℝ)..1, ((N : ℂ))⁻¹ * (∫ y in (0 : ℝ)..1,
          ∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
              * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y))) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact intervalIntegral.integral_const_mul ((N : ℂ))⁻¹ _
  have hc2 : (∫ x in (0 : ℝ)..1, ((N : ℂ))⁻¹ * (∫ y in (0 : ℝ)..1,
          ∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
              * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y))))
      = ((N : ℂ))⁻¹ * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          ∑ n ∈ Finset.Ioc (N / 2) N,
            (symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
              * (symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y))) := by
    exact intervalIntegral.integral_const_mul ((N : ℂ))⁻¹ _
  rw [hc1, hc2]
  rw [symConc_sep_integral_finset (s := Finset.Ioc (N / 2) N)
      (A := fun n x => symSeq κ x * eeC (((n : ℝ) - (i : ℝ)) * x))
      (B := fun n y => symSeq κ' y * eeC ((((P.eval (n : ℤ) : ℤ) : ℝ) - (j : ℝ)) * y))
      (hA := fun n => (symConc_continuous_symSeq hκ).mul (by unfold eeC; fun_prop))
      (hB := fun n => (symConc_continuous_symSeq hκ').mul (by unfold eeC; fun_prop))]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [h1 n, h2 n]

/-- **The concrete halved kernel in the symbol dictionary of §6.**  For summable `κ`, `κ'`, the
kernel of the composition of the halved average `khalf N P` with the two linear convolutions is the
`(i,j)`-Fourier coefficient of the product of the three symbols
`symSeq κ x * symSeq κ' y * halfSym N P x y`. -/
theorem SymConc_coeff (κ κ' : ℤ → ℂ) (hκ : Summable κ) (hκ' : Summable κ') (N : ℕ) (P : Polynomial ℤ) (i j : ℤ) :
    Work.KMTAreas.A7.kernComp (Work.KMTAreas.A7.khalf N P) κ κ' i j
      = Work.KMTPlan.A6.coeff2 (fun x y => Work.KMTPlan.A6.symSeq κ x
          * Work.KMTPlan.A6.symSeq κ' y * Work.KMTPlan.A6.halfSym N P x y) i j := by
  rw [KernComp_khalf_eq, symConc_coeff2 κ κ' hκ hκ' N P i j]

end

end Work.KMTPlan.A6
