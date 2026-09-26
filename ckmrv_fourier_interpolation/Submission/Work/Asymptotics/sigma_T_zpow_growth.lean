/-
# Polynomial growth of the powers of `σ(T)`

The spectrum of `σ(T) = Work.Modular.sigmaT` is `{1 (multiplicity 5), -1 (multiplicity 1)}`,
so its powers grow at most quadratically.  `Submission.Work.Asymptotics.SigmaTPow` supplies
the explicit integer matrices `P₀, P₁, P₂, Q` with

  `4 · Tmatⁿ = P₀ + n P₁ + (n choose 2) P₂ + (-1)ⁿ Q`

(and the analogous formula for `Tmat⁻¹ = Timat`), all of whose entries are bounded by `10`
in absolute value.  Reading the identity entrywise and using the triangle inequality gives

  `‖σ(T)ⁿ i j‖ ≤ 10 · (1 + n)²`

and the same bound for `σ(T)⁻¹`.  Negative exponents are handled with the formula for
`Timat = Tmat⁻¹` and `Work.Modular.sigmaTinv`, together with the cancellation identity
`σ(T)^n * σ(T)⁻¹^n = 1`.
-/
import Mathlib
import Submission.Work.Asymptotics.SigmaTPow

set_option maxHeartbeats 800000

noncomputable section

open scoped MatrixGroups

namespace Work.Asymptotics

/-! ## Casting integer matrices to `ℂ` -/

lemma toC_intCast_apply (M : Matrix (Fin 6) (Fin 6) ℤ) (i j : Fin 6) :
    toC M i j = ((M i j : ℤ) : ℂ) := rfl

lemma toC_one : toC (1 : Matrix (Fin 6) (Fin 6) ℤ) = 1 := by
  ext i j
  simp [toC, Matrix.one_apply]

lemma toC_pow (M : Matrix (Fin 6) (Fin 6) ℤ) (n : ℕ) : toC (M ^ n) = toC M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toC_one]
  | succ n ih => rw [pow_succ, pow_succ, toC_mul, ih]

/-! ## The entrywise power formulas -/

lemma Tmat_pow_entry (n : ℕ) (i j : Fin 6) :
    4 * ((Tmat ^ n) i j)
      = P0 i j + (n : ℤ) * P1 i j + ((n.choose 2 : ℕ) : ℤ) * P2 i j
        + (-1 : ℤ) ^ n * Q i j := by
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M i j) (Tmat_pow_formula n)
  simp only [Matrix.add_apply, Matrix.smul_apply] at h
  simpa using h

lemma Timat_pow_entry (n : ℕ) (i j : Fin 6) :
    4 * ((Timat ^ n) i j)
      = P0 i j + (n : ℤ) * P1' i j + ((n.choose 2 : ℕ) : ℤ) * P2 i j
        + (-1 : ℤ) ^ n * Q i j := by
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M i j) (Timat_pow_formula n)
  simp only [Matrix.add_apply, Matrix.smul_apply] at h
  simpa using h

/-! ## The entries of the auxiliary matrices are bounded by `10` -/

lemma P0_entry (i j : Fin 6) : |(P0 i j : ℝ)| ≤ 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [P0]

lemma P1_entry (i j : Fin 6) : |(P1 i j : ℝ)| ≤ 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [P1]

lemma P1'_entry (i j : Fin 6) : |(P1' i j : ℝ)| ≤ 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [P1']

lemma P2_entry (i j : Fin 6) : |(P2 i j : ℝ)| ≤ 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [P2]

lemma Q_entry (i j : Fin 6) : |(Q i j : ℝ)| ≤ 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [Q]

/-! ## From the entrywise formula to a polynomial bound -/

/-- If `4 * x = A + n B + (n choose 2) C + (-1)^n D` and the four coefficients are bounded
by `10`, then `|x| ≤ 10 (1 + n)^2`. -/
lemma entry_bound_of_formula (x : ℤ) (n : ℕ) (A B C D : ℤ)
    (hA : |(A : ℝ)| ≤ 10) (hB : |(B : ℝ)| ≤ 10) (hC : |(C : ℝ)| ≤ 10)
    (hD : |(D : ℝ)| ≤ 10)
    (h : 4 * x = A + (n : ℤ) * B + ((n.choose 2 : ℕ) : ℤ) * C + (-1 : ℤ) ^ n * D) :
    |(x : ℝ)| ≤ 10 * (1 + (n : ℝ)) ^ 2 := by
  have hR : (4 : ℝ) * (x : ℝ)
      = (A : ℝ) + (n : ℝ) * (B : ℝ) + ((n.choose 2 : ℕ) : ℝ) * (C : ℝ)
        + ((-1 : ℝ) ^ n) * (D : ℝ) := by
    have hh := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at hh
    linarith [hh]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hneg1 : |(-1 : ℝ)| = 1 := by norm_num
  have h1 : |(A : ℝ) + (n : ℝ) * (B : ℝ) + ((n.choose 2 : ℕ) : ℝ) * (C : ℝ)
        + ((-1 : ℝ) ^ n) * (D : ℝ)| ≤
      10 + (n : ℝ) * 10 + ((n.choose 2 : ℕ) : ℝ) * 10 + 10 := by
    have h2 : |(n : ℝ) * (B : ℝ)| = (n : ℝ) * |(B : ℝ)| := by rw [abs_mul, abs_of_nonneg hn]
    have h3 : |((n.choose 2 : ℕ) : ℝ) * (C : ℝ)|
        = ((n.choose 2 : ℕ) : ℝ) * |(C : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have h4 : |((-1 : ℝ) ^ n) * (D : ℝ)| = |(D : ℝ)| := by
      rw [abs_mul, abs_pow, hneg1, one_pow, one_mul]
    have h5 := abs_add_le ((A : ℝ) + (n : ℝ) * (B : ℝ) + ((n.choose 2 : ℕ) : ℝ) * (C : ℝ))
      (((-1 : ℝ) ^ n) * (D : ℝ))
    have h6 := abs_add_le ((A : ℝ) + (n : ℝ) * (B : ℝ)) (((n.choose 2 : ℕ) : ℝ) * (C : ℝ))
    have h7 := abs_add_le (A : ℝ) ((n : ℝ) * (B : ℝ))
    rw [h4] at h5
    rw [h3] at h6
    rw [h2] at h7
    nlinarith [abs_nonneg (A : ℝ), abs_nonneg (C : ℝ), abs_nonneg (D : ℝ),
      abs_nonneg (B : ℝ)]
  have hx4 : |(x : ℝ)| = |(4 : ℝ) * (x : ℝ)| / 4 := by
    rw [abs_mul]; norm_num
  rw [hx4, hR]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  nlinarith [h1, hc, hn]

lemma Tmat_pow_entry_bound (n : ℕ) (i j : Fin 6) :
    |((Tmat ^ n) i j : ℝ)| ≤ 10 * (1 + (n : ℝ)) ^ 2 :=
  entry_bound_of_formula _ n _ _ _ _ (P0_entry i j) (P1_entry i j) (P2_entry i j)
    (Q_entry i j) (Tmat_pow_entry n i j)

lemma Timat_pow_entry_bound (n : ℕ) (i j : Fin 6) :
    |((Timat ^ n) i j : ℝ)| ≤ 10 * (1 + (n : ℝ)) ^ 2 :=
  entry_bound_of_formula _ n _ _ _ _ (P0_entry i j) (P1'_entry i j) (P2_entry i j)
    (Q_entry i j) (Timat_pow_entry n i j)

/-! ## The bounds for `σ(T)ⁿ` and `σ(T)⁻¹ⁿ` -/

lemma sigmaT_eq_toC_pow (n : ℕ) : Work.Modular.sigmaT ^ n = toC (Tmat ^ n) := by
  rw [toC_pow, ← toC_Tmat]

lemma sigmaTinv_eq_toC_pow (n : ℕ) : Work.Modular.sigmaTinv ^ n = toC (Timat ^ n) := by
  rw [toC_pow, ← toC_Timat]

lemma sigmaT_pow_entry_norm (n : ℕ) (i j : Fin 6) :
    ‖(Work.Modular.sigmaT ^ n) i j‖ ≤ 10 * (1 + (n : ℝ)) ^ 2 := by
  have h : (Work.Modular.sigmaT ^ n) i j = (((Tmat ^ n) i j : ℤ) : ℂ) := by
    rw [sigmaT_eq_toC_pow]; rfl
  rw [h, Complex.norm_intCast]
  exact Tmat_pow_entry_bound n i j

lemma sigmaTinv_pow_entry_norm (n : ℕ) (i j : Fin 6) :
    ‖(Work.Modular.sigmaTinv ^ n) i j‖ ≤ 10 * (1 + (n : ℝ)) ^ 2 := by
  have h : (Work.Modular.sigmaTinv ^ n) i j = (((Timat ^ n) i j : ℤ) : ℂ) := by
    rw [sigmaTinv_eq_toC_pow]; rfl
  rw [h, Complex.norm_intCast]
  exact Timat_pow_entry_bound n i j

/-! ## Power identities for `σ(T)` and `σ(T)⁻¹` -/

lemma sigmaT_commute_sigmaTinv : Commute Work.Modular.sigmaT Work.Modular.sigmaTinv := by
  rw [Commute, SemiconjBy, Work.Modular.sigmaT_mul_sigmaTinv,
    Work.Modular.sigmaTinv_mul_sigmaT]

lemma sigmaTinv_commute_sigmaT : Commute Work.Modular.sigmaTinv Work.Modular.sigmaT := by
  rw [Commute, SemiconjBy, Work.Modular.sigmaTinv_mul_sigmaT,
    Work.Modular.sigmaT_mul_sigmaTinv]

lemma sigmaT_pow_mul_sigmaTinv_pow (n : ℕ) :
    Work.Modular.sigmaT ^ n * Work.Modular.sigmaTinv ^ n = 1 := by
  rw [← sigmaT_commute_sigmaTinv.mul_pow, Work.Modular.sigmaT_mul_sigmaTinv, one_pow]

lemma sigmaTinv_pow_mul_sigmaT_pow (n : ℕ) :
    Work.Modular.sigmaTinv ^ n * Work.Modular.sigmaT ^ n = 1 := by
  rw [← sigmaTinv_commute_sigmaT.mul_pow, Work.Modular.sigmaTinv_mul_sigmaT, one_pow]

lemma isUnit_sigmaT_pow (n : ℕ) : IsUnit (Work.Modular.sigmaT ^ n) := by
  have h : IsUnit Work.Modular.sigmaT := Work.Modular.sigmaUnitT.isUnit
  exact h.pow n

/-! ## Powers of `σ(T^k)` in the group algebra -/

lemma of_T_pow (n : ℕ) :
    MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
        ((ModularGroup.T : SL(2, ℤ)) ^ n) = Work.Kernels.R_T ^ n := by
  rw [map_pow, MonoidAlgebra.of_apply]

lemma sigmaR_of_T_pow (n : ℕ) :
    Work.Residues.sigmaR
        (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
          ((ModularGroup.T : SL(2, ℤ)) ^ n)) = Work.Modular.sigmaT ^ n := by
  rw [of_T_pow, map_pow, Work.Residues.sigmaR_R_T]

lemma of_T_neg_nat_mul_pow (n : ℕ) :
    MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
        ((ModularGroup.T : SL(2, ℤ)) ^ (-(n : ℤ)))
      * MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
        ((ModularGroup.T : SL(2, ℤ)) ^ n) = 1 := by
  rw [← map_mul]
  have hT : (ModularGroup.T : SL(2, ℤ)) ^ (-(n : ℤ)) * ModularGroup.T ^ n = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel]
  rw [hT, map_one]

lemma sigmaR_of_T_neg (n : ℕ) :
    Work.Residues.sigmaR
        (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
          ((ModularGroup.T : SL(2, ℤ)) ^ (-(n : ℤ))))
      = Work.Modular.sigmaTinv ^ n := by
  have hL : Work.Residues.sigmaR
        (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
          ((ModularGroup.T : SL(2, ℤ)) ^ (-(n : ℤ)))) * Work.Modular.sigmaT ^ n = 1 := by
    rw [← sigmaR_of_T_pow n, ← map_mul]
    rw [of_T_neg_nat_mul_pow n, map_one]
  have hR : Work.Modular.sigmaTinv ^ n * Work.Modular.sigmaT ^ n = 1 :=
    sigmaTinv_pow_mul_sigmaT_pow n
  exact IsUnit.mul_right_cancel (isUnit_sigmaT_pow n) (hL.trans hR.symm)

/-! ## The growth bound -/

/-- **The entries of `σ(T^k)` grow at most polynomially in `k`.**
The spectrum of `σ(T)` is `{1 (multiplicity 5), -1}`, so the powers of `σ(T)` grow at most
quadratically in the exponent.  `Submission.Work.Asymptotics.SigmaTPow` supplies the explicit
integer matrices `P₀, P₁, P₂, Q` with `4 · Tmat^n = P₀ + n P₁ + (n choose 2) P₂ + (-1)^n Q` (and
the analogous formula for `Tmat⁻¹`), whose entries are bounded by `10`; from that identity the
bound follows by a Cauchy–Schwarz estimate.  Negative exponents are handled with the formula for
`Timat = Tmat⁻¹` and `Work.Modular.sigmaTinv`. -/
theorem sigma_T_zpow_growth :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ k : ℤ, ∀ i j : Fin 6,
      ‖(Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k))) i j‖
        ≤ C * (1 + |(k : ℝ)|) ^ N := by
  refine ⟨10, 2, by norm_num, by norm_num, ?_⟩
  intro k i j
  have hmain : ‖(Work.Residues.sigmaR
        (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
          (ModularGroup.T ^ k))) i j‖ ≤ 10 * (1 + |(k : ℝ)|) ^ 2 := by
    rcases Int.eq_nat_or_neg k with ⟨n, hk | hk⟩
    · subst hk
      rw [zpow_natCast, sigmaR_of_T_pow n, Int.cast_natCast,
        abs_of_nonneg (Nat.cast_nonneg n)]
      exact sigmaT_pow_entry_norm n i j
    · subst hk
      rw [sigmaR_of_T_neg n, Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n)]
      exact sigmaTinv_pow_entry_norm n i j
  have hpow : (1 + |(k : ℝ)|) ^ (2 : ℝ) = (1 + |(k : ℝ)|) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [hpow]
  exact hmain

end Work.Asymptotics
