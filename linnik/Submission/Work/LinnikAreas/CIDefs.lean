import Mathlib
import Submission.Work.LinnikAreas.CIDeps

/-!
# `CIDefs` — notation for the class identity

Definitions and elementary analytic bounds used in the proof of
`Work.LinnikAreas.ClassIdentityHyp` (Heath-Brown's Lemma 13.1 in the form needed for Area 2):
the tent-weighted von Mangoldt (twisted) sums, the class-prime and prime-power parts, and the
logarithmic bounds that absorb powers of `log q` into the error terms.
-/

open DirichletCharacter Complex
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace Work.LinnikAreas
open Work.LinnikContract

/-- `Σ_{n ≤ X} Λ(n) · χ(n) / n · h(log n / log q)` with `h = tentWeight (11/2) (3/10)` and
`χ` a Dirichlet character of any level `N` (the scale `log q` is that of the *outer* modulus). -/
abbrev chiSum {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (q X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod N) : ℂ) / (n : ℂ) *
    ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)

/-- The class von Mangoldt sum `Σ_{n ≤ X, n ≡ a (q)} Λ(n)/n · h(log n / log q)`. -/
abbrev classSum {q : ℕ} [NeZero q] (a X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 X, ((ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n : ℝ) : ℂ) *
    (((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) / (n : ℂ))

/-- The prime part of the class sum — the object whose positivity is the goal of Area 2. -/
abbrev primePS {q : ℕ} (a X : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]),
    ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
      ((tentW (Real.log (p : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)

/-- The non-prime (prime power) part of the class sum. -/
abbrev classPP {q : ℕ} (a X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
    ArithmeticFunction.vonMangoldt n / (n : ℝ) * tentW (Real.log (n : ℝ) / Real.log (q : ℝ))

/-- The von Mangoldt sum over all `n ≤ X` (real form). -/
abbrev allSumR (q X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    ArithmeticFunction.vonMangoldt n / (n : ℝ) * tentW (Real.log (n : ℝ) / Real.log (q : ℝ))

/-- The von Mangoldt sum over all `n ≤ X` (complex form). -/
abbrev allSum (q X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
    ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)

/-- The von Mangoldt sum over the `n ≤ X` not coprime to `q` (real form). -/
abbrev ncsSum (q X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
    ArithmeticFunction.vonMangoldt n / (n : ℝ) * tentW (Real.log (n : ℝ) / Real.log (q : ℝ))

/-- The von Mangoldt sum over the `n ≤ X` not coprime to `q` (complex form). -/
abbrev ncsSumC (q X : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
    (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
      ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)

/-- Total mass of the far zeros over all non-principal characters mod `q`. -/
abbrev farTotal (q : ℕ) [NeZero q] (R : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ

/-- `log q ≤ 8 q^{1/8}`. -/
lemma log_natCast_le_eight_rpow (q : ℕ) :
    Real.log (q : ℝ) ≤ 8 * (q : ℝ) ^ ((1 : ℝ) / 8) := by
  have h := Real.log_natCast_le_rpow_div q (ε := ((1 : ℝ) / 8)) (by norm_num)
  calc Real.log (q : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 8) / ((1 : ℝ) / 8) := h
    _ = 8 * (q : ℝ) ^ ((1 : ℝ) / 8) := by ring

/-- `log q ≤ 16 q^{49/20}` for `q ≥ 1`. -/
lemma log_natCast_le_rpow (q : ℕ) (hq : 1 ≤ q) :
    Real.log (q : ℝ) ≤ 16 * (q : ℝ) ^ ((49 : ℝ) / 20) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : Real.log (q : ℝ) ≤ 8 * (q : ℝ) ^ ((1 : ℝ) / 8) := log_natCast_le_eight_rpow q
  have h2 : (q : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ^ ((49 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have h3 : 8 * (q : ℝ) ^ ((1 : ℝ) / 8) ≤ 8 * (q : ℝ) ^ ((49 : ℝ) / 20) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : 8 * (q : ℝ) ^ ((49 : ℝ) / 20) ≤ 16 * (q : ℝ) ^ ((49 : ℝ) / 20) :=
    mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 16) (Real.rpow_nonneg (by positivity) _)
  linarith

/-- `(log q)^2 · q^{-49/20} ≤ 256` for `q ≥ 1`. -/
lemma log_sq_mul_rpow_neg_le (q : ℕ) (hq : 1 ≤ q) :
    (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20)) ≤ 256 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have h1 : Real.log (q : ℝ) ≤ 8 * (q : ℝ) ^ ((1 : ℝ) / 8) := log_natCast_le_eight_rpow q
  have h2 : (Real.log (q : ℝ)) ^ 2 ≤ (8 * (q : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 :=
    pow_le_pow_left₀ hlog0 h1 2
  have h3 : (8 * (q : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = 64 * (q : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ ((1 : ℝ) / 8)) 2,
      ← Real.rpow_mul (le_of_lt hqpos)]
    norm_num
  have h4 : 64 * (q : ℝ) ^ ((1 : ℝ) / 4) * (q : ℝ) ^ (-((49 : ℝ) / 20))
      = 64 * (q : ℝ) ^ (((1 : ℝ) / 4) + -((49 : ℝ) / 20)) := by
    rw [mul_assoc, ← Real.rpow_add hqpos]
  have h5 : (q : ℝ) ^ (((1 : ℝ) / 4) + -((49 : ℝ) / 20)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have h6 : (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20))
      ≤ 64 * (q : ℝ) ^ ((1 : ℝ) / 4) * (q : ℝ) ^ (-((49 : ℝ) / 20)) :=
    mul_le_mul_of_nonneg_right (le_trans h2 (le_of_eq h3)) (Real.rpow_nonneg hqpos.le _)
  calc (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20))
      ≤ 64 * (q : ℝ) ^ ((1 : ℝ) / 4) * (q : ℝ) ^ (-((49 : ℝ) / 20)) := h6
    _ = 64 * (q : ℝ) ^ (((1 : ℝ) / 4) + -((49 : ℝ) / 20)) := h4
    _ ≤ 64 * 1 := by
        refine mul_le_mul_of_nonneg_left h5 (by norm_num)
    _ ≤ 256 := by norm_num

end Work.LinnikAreas
