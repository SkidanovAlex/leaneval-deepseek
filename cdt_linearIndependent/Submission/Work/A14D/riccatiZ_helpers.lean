import Mathlib
import Submission.Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff
import Submission.Commons.Algebra.Polynomial.ne_zero_of_eval_eq_zero_of_isCoprime

/-!
# A14D: polynomial facts for the Riccati equation of `L_Z`

The Riccati equation attached to `L_Z y = (P y')' + R y` (`P = z(1−z)(1−9z)`, `R = 9z − 3`) reads

  `P·(u' + u²) + P'·u + R = 0`,   `P = X − 10X² + 9X³`, `P' = 1 − 20X + 27X²`, `R = −3 + 9X`.

This file collects the elementary polynomial facts about `P`, `P'`, `R` used by the proof that
this Riccati equation has no rational solution (`Work.A14D.riccatiZ_no_rational`): the degrees and
leading coefficients, the identity `P' = P.derivative`, the factorisation `P = X(1−X)(1−9X)`, the
simple-root property of `P`, and the two "coefficient at a root" identities
`local_residue_eval` / `local_residue_deriv`.
-/

namespace Work.A14D

open Polynomial

noncomputable section

/-- `P = X − 10X² + 9X³ = X(1−X)(1−9X)`. -/
abbrev Q2Z : Polynomial ℂ := X - 10 * X ^ 2 + 9 * X ^ 3

/-- `P' = 1 − 20X + 27X²`. -/
abbrev Q1Z : Polynomial ℂ := 1 - 20 * X + 27 * X ^ 2

/-- `R = −3 + 9X`. -/
abbrev Q0Z : Polynomial ℂ := -3 + 9 * X

/-! ## `P = X − 10X² + 9X³` -/

lemma Q2Z_natDegree : Q2Z.natDegree = 3 := by
  change (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).natDegree = 3
  compute_degree!

lemma Q2Z_coeff_three : Q2Z.coeff 3 = 9 := by
  change (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).coeff 3 = 9
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X,
    ← C_eq_natCast 10, ← C_eq_natCast 9]

lemma Q2Z_leadingCoeff : Q2Z.leadingCoeff = 9 := by
  rw [← Polynomial.coeff_natDegree, Q2Z_natDegree, Q2Z_coeff_three]

lemma Q2Z_ne_zero : Q2Z ≠ 0 := by
  intro h
  have := Q2Z_natDegree
  rw [h] at this
  simp at this

/-! ## `P' = 1 − 20X + 27X²` -/

lemma Q1Z_natDegree : Q1Z.natDegree = 2 := by
  change (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ).natDegree = 2
  compute_degree!

lemma Q1Z_coeff_two : Q1Z.coeff 2 = 27 := by
  change (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ).coeff 2 = 27
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X,
    Polynomial.coeff_one, ← C_eq_natCast 20, ← C_eq_natCast 27]

lemma Q1Z_leadingCoeff : Q1Z.leadingCoeff = 27 := by
  rw [← Polynomial.coeff_natDegree, Q1Z_natDegree, Q1Z_coeff_two]

lemma Q1Z_ne_zero : Q1Z ≠ 0 := by
  intro h
  have := Q1Z_natDegree
  rw [h] at this
  simp at this

/-! ## `R = −3 + 9X` -/

lemma Q0Z_natDegree : Q0Z.natDegree = 1 := by
  change (-3 + 9 * X : Polynomial ℂ).natDegree = 1
  compute_degree!

lemma Q0Z_coeff_one : Q0Z.coeff 1 = 9 := by
  change (-3 + 9 * X : Polynomial ℂ).coeff 1 = 9
  simp [Polynomial.coeff_add, Polynomial.coeff_X, ← C_eq_natCast 9]

lemma Q0Z_leadingCoeff : Q0Z.leadingCoeff = 9 := by
  rw [← Polynomial.coeff_natDegree, Q0Z_natDegree, Q0Z_coeff_one]

lemma Q0Z_ne_zero : Q0Z ≠ 0 := by
  intro h
  have := Q0Z_natDegree
  rw [h] at this
  simp at this

/-! ## The identity `P' = P.derivative` -/

lemma Q2Z_derivative : Q2Z.derivative = Q1Z := by
  change (Polynomial.derivative (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ))
      = (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ)
  rw [show (10 : Polynomial ℂ) = (C 10 : Polynomial ℂ) from (C_eq_natCast 10).symm,
      show (9 : Polynomial ℂ) = (C 9 : Polynomial ℂ) from (C_eq_natCast 9).symm,
      show (20 : Polynomial ℂ) = (C 20 : Polynomial ℂ) from (C_eq_natCast 20).symm,
      show (27 : Polynomial ℂ) = (C 27 : Polynomial ℂ) from (C_eq_natCast 27).symm]
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_X_pow, Polynomial.derivative_C]
  rw [← mul_assoc, ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul]
  norm_num

/-! ## Evaluation -/

lemma Q2Z_eval (β : ℂ) : Q2Z.eval β = β * (1 - β) * (1 - 9 * β) := by
  change (Polynomial.eval β (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ))
      = β * (1 - β) * (1 - 9 * β)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat]
  ring

lemma Q1Z_eval (β : ℂ) : Q1Z.eval β = 1 - 20 * β + 27 * β ^ 2 := by
  change (Polynomial.eval β (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ)) = 1 - 20 * β + 27 * β ^ 2
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat] <;> ring

lemma Q0Z_eval (β : ℂ) : Q0Z.eval β = -3 + 9 * β := by
  change (Polynomial.eval β (-3 + 9 * X : Polynomial ℂ)) = -3 + 9 * β
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat,
    Polynomial.eval_neg] <;> ring

lemma Q2Z_eval_eq_zero_iff {β : ℂ} : Q2Z.eval β = 0 ↔ β = 0 ∨ β = 1 ∨ β = 1 / 9 := by
  rw [Q2Z_eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2).symm)
    · refine Or.inr (Or.inr ?_)
      have h9 : (9 : ℂ) * β = 1 := (sub_eq_zero.mp h1).symm
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h9
  · rintro (rfl | rfl | rfl) <;> norm_num

lemma Q2Z_deriv_eval_ne_zero_of_root {β : ℂ} (h : Q2Z.eval β = 0) :
    Q2Z.derivative.eval β ≠ 0 := by
  rw [Q2Z_derivative, Q1Z_eval]
  intro h0
  rw [Q2Z_eval] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [h2] at h0; norm_num at h0
    · rw [← (sub_eq_zero.mp h2)] at h0; norm_num at h0
  · have h9 : (9 : ℂ) * β = 1 := (sub_eq_zero.mp h1).symm
    have hβ : β = 1 / 9 := by
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h9
    rw [hβ] at h0
    norm_num at h0

lemma Q2Z_rootMultiplicity_le_one (β : ℂ) : Q2Z.rootMultiplicity β ≤ 1 := by
  rw [Polynomial.rootMultiplicity_le_iff Q2Z_ne_zero β 1]
  intro h
  have h2 : (X - C β) ^ 2 ∣ Q2Z := by simpa using h
  rw [Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff] at h2
  exact Q2Z_deriv_eval_ne_zero_of_root h2.1 h2.2

/-! ## The two coefficient identities at a root of `B` -/

/-- Evaluating the cleared Riccati identity at a root `β` of `B`. -/
lemma local_residue_eval {K : Type*} [Field K] (P2 P1 P0 A B : Polynomial K) (β : K)
    (hB : B.eval β = 0)
    (h : P2 * (A.derivative * B - A * B.derivative) + P2 * A ^ 2 + P1 * A * B + P0 * B ^ 2 = 0) :
    P2.eval β * A.eval β * (A.eval β - B.derivative.eval β) = 0 := by
  have h2 := congrArg (Polynomial.eval β) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    hB, Polynomial.eval_zero, mul_zero, add_zero] at h2
  ring_nf at h2 ⊢
  linear_combination h2

/-- Differentiating the cleared Riccati identity and evaluating at a root `β` of `B`. -/
lemma local_residue_deriv {K : Type*} [Field K] (P2 P1 P0 A B : Polynomial K) (β : K)
    (hP2 : P2.eval β = 0) (hB : B.eval β = 0)
    (h : P2 * (A.derivative * B - A * B.derivative) + P2 * A ^ 2 + P1 * A * B + P0 * B ^ 2 = 0) :
    P2.derivative.eval β * (A.eval β) ^ 2 - P2.derivative.eval β * A.eval β * B.derivative.eval β
      + P1.eval β * A.eval β * B.derivative.eval β = 0 := by
  have h' := congrArg (fun p => Polynomial.eval β (Polynomial.derivative p)) h
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_one,
    Polynomial.derivative_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero,
    hP2, hB, mul_zero, add_zero, zero_mul, sub_zero, zero_sub] at h'
  ring_nf at h' ⊢
  linear_combination h'

end

end Work.A14D
