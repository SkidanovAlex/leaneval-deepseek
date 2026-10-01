/-
# ZeroFreeTables/P10/Defs14

Free-scale machinery for the "three quadratic characters" case of HB §9:
the 14-term pointwise combination

  `(1 + Re z₁)(1 + Re z₂)(1 + Re z₃)`,  `z_j = χ_j(n) n^{-iγ_j}`,

expanded into the terms

  `1 + Σ_j Re z_j + (1/2) Σ_{j<k} [Re(z_j z_k) + Re(z_j z_k⁻¹)]
      + (1/4) Σ_{sgn} Re(z₁^{sgn} z₂^{sgn} z₃^{sgn})`.

Because `χ₁χ₂χ₃ = 1` and `χ_j² = 1`, the characters occurring are
`1, χ₁, χ₂, χ₃, χ₁χ₂, χ₁χ₂⁻¹, χ₁χ₃, χ₁χ₃⁻¹, χ₂χ₃, χ₂χ₃⁻¹` and the four triple
products are all principal — exactly the fourteen `SigmaP3L` terms of
`case3_weighted_combination`.

This file contains only the definitions, the trivial unfolding/bridge lemmas and
elementary algebraic/conjugacy facts, so that the analytic (`hbTermG`
summability) and algebraic (`comb14Raw` non-negativity) parts can be proved
independently on top of it.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.WLBase

open DirichletCharacter Complex
open scoped Classical BigOperators ComplexConjugate
noncomputable section

namespace Work.ZeroFreeTables.P10

open Work.ZeroFreeTables.P3 (hbE ReDivCpow)

/-! ## The two normal forms of the summand of `SigmaP3L` -/

/-- The `n`-th summand of `SigmaP3L N L χ s a λ₁`, with the complex power kept whole. -/
def hbRawG (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (L : ℝ) (s : ℂ) (a lam₁ : ℝ) :
    ℕ → ℝ :=
  fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ (n : ZMod N) / (n : ℂ) ^ s).re)
    * hbWL L a lam₁ n

/-- `SigmaP3L` is `L⁻¹` times the `tsum` of `hbRawG`. -/
theorem SigmaP3L_eq_hbRawG (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (L : ℝ) (s : ℂ)
    (a lam₁ : ℝ) :
    SigmaP3L N L χ s a lam₁ = L⁻¹ * ∑' n, hbRawG N χ L s a lam₁ n := rfl

/-- The `n`-th summand of `SigmaP3L N L χ (σ + iΔ) a λ₁` with the power split as `n^{-σ} n^{-iΔ}`. -/
def hbTermG (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (L : ℝ) (σ Δ a lam₁ : ℝ)
    (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N) * hbE Δ n).re
    * (n : ℝ) ^ (-σ) * hbWL L a lam₁ n

/-- The bridge between the two normal forms. -/
theorem hbRawG_eq_hbTermG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (L σ Δ a lam₁ : ℝ)
    (n : ℕ) :
    hbRawG N χ L ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n = hbTermG N χ L σ Δ a lam₁ n := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    simp [hbRawG, hbTermG]
  · simp only [hbRawG, hbTermG, hbE]
    rw [ReDivCpow hn σ Δ (χ (n : ZMod N))]
    ring

/-! ## The fourteen characters, arguments and coefficients -/

/-- The fourteen characters of the three-character combination. -/
def chi14 (N : ℕ) [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N) :
    Fin 14 → DirichletCharacter ℂ N :=
  ![1, chi1, chi2, chi3, chi1 * chi2, chi1 * chi2⁻¹, chi1 * chi3, chi1 * chi3⁻¹,
    chi2 * chi3, chi2 * chi3⁻¹, 1, 1, 1, 1]

/-- The fourteen imaginary parts `Δ` of the argument points. -/
def dl14 (γ1 γ2 γ3 : ℝ) : Fin 14 → ℝ :=
  ![0, γ1, γ2, γ3, γ1 + γ2, γ1 - γ2, γ1 + γ3, γ1 - γ3, γ2 + γ3, γ2 - γ3,
    γ1 + γ2 + γ3, γ1 + γ2 - γ3, γ1 - γ2 + γ3, -γ1 + γ2 + γ3]

/-- The fourteen coefficients. -/
def coef14 : Fin 14 → ℝ :=
  ![1, 1, 1, 1, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/4, 1/4, 1/4, 1/4]

/-! ## The combination -/

/-- The `n`-th summand of the fourteen-term combination of `SigmaP3L` terms, in the `hbRawG`
normal form (i.e. literally the summands of the fourteen `SigmaP3L` terms below). -/
def comb14Raw (N : ℕ) [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 14, coef14 i * hbRawG N (chi14 N chi1 chi2 chi3 i) L
    ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁ n

/-- The fourteen-term combination of `SigmaP3L` values. -/
def S14 (N : ℕ) [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) : ℝ :=
  ∑ i : Fin 14, coef14 i * SigmaP3L N L (chi14 N chi1 chi2 chi3 i)
    ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁

/-- `S14` written out as the sum of the fourteen `SigmaP3L` terms. -/
theorem S14_unfold (N : ℕ) [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) :
    S14 N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁
      = SigmaP3L N L 1 ((σ : ℂ) + (0 : ℝ) * Complex.I) a lam₁
        + SigmaP3L N L chi1 ((σ : ℂ) + (γ1 : ℂ) * Complex.I) a lam₁
        + SigmaP3L N L chi2 ((σ : ℂ) + (γ2 : ℂ) * Complex.I) a lam₁
        + SigmaP3L N L chi3 ((σ : ℂ) + (γ3 : ℂ) * Complex.I) a lam₁
        + (1/2) * (SigmaP3L N L (chi1 * chi2) ((σ : ℂ) + (γ1 + γ2 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L (chi1 * chi2⁻¹) ((σ : ℂ) + (γ1 - γ2 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L (chi1 * chi3) ((σ : ℂ) + (γ1 + γ3 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L (chi1 * chi3⁻¹) ((σ : ℂ) + (γ1 - γ3 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L (chi2 * chi3) ((σ : ℂ) + (γ2 + γ3 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L (chi2 * chi3⁻¹) ((σ : ℂ) + (γ2 - γ3 : ℝ) * Complex.I) a lam₁)
        + (1/4) * (SigmaP3L N L 1 ((σ : ℂ) + (γ1 + γ2 + γ3 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L 1 ((σ : ℂ) + (γ1 + γ2 - γ3 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L 1 ((σ : ℂ) + (γ1 - γ2 + γ3 : ℝ) * Complex.I) a lam₁
          + SigmaP3L N L 1 ((σ : ℂ) + (-γ1 + γ2 + γ3 : ℝ) * Complex.I) a lam₁) := by
  simp only [S14, chi14, dl14, coef14, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring

/-- The `n`-th summand of the fourteen-term combination, written out. -/
theorem comb14Raw_unfold (N : ℕ) [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) (n : ℕ) :
    comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n
      = hbTermG N 1 L σ 0 a lam₁ n
        + hbTermG N chi1 L σ γ1 a lam₁ n
        + hbTermG N chi2 L σ γ2 a lam₁ n
        + hbTermG N chi3 L σ γ3 a lam₁ n
        + (1/2) * (hbTermG N (chi1 * chi2) L σ (γ1 + γ2) a lam₁ n
          + hbTermG N (chi1 * chi2⁻¹) L σ (γ1 - γ2) a lam₁ n
          + hbTermG N (chi1 * chi3) L σ (γ1 + γ3) a lam₁ n
          + hbTermG N (chi1 * chi3⁻¹) L σ (γ1 - γ3) a lam₁ n
          + hbTermG N (chi2 * chi3) L σ (γ2 + γ3) a lam₁ n
          + hbTermG N (chi2 * chi3⁻¹) L σ (γ2 - γ3) a lam₁ n)
        + (1/4) * (hbTermG N 1 L σ (γ1 + γ2 + γ3) a lam₁ n
          + hbTermG N 1 L σ (γ1 + γ2 - γ3) a lam₁ n
          + hbTermG N 1 L σ (γ1 - γ2 + γ3) a lam₁ n
          + hbTermG N 1 L σ (-γ1 + γ2 + γ3) a lam₁ n) := by
  simp only [comb14Raw, chi14, dl14, coef14, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rw [hbRawG_eq_hbTermG, hbRawG_eq_hbTermG, hbRawG_eq_hbTermG, hbRawG_eq_hbTermG,
    hbRawG_eq_hbTermG, hbRawG_eq_hbTermG, hbRawG_eq_hbTermG, hbRawG_eq_hbTermG,
    hbRawG_eq_hbTermG, hbRawG_eq_hbTermG, hbRawG_eq_hbTermG, hbRawG_eq_hbTermG,
    hbRawG_eq_hbTermG, hbRawG_eq_hbTermG]
  ring

/-! ## Elementary conjugacy facts -/

/-- Conjugation of the exponential factor. -/
theorem hbE_conj (Δ : ℝ) (n : ℕ) : conj (hbE Δ n) = hbE (-Δ) n := by
  rw [hbE, hbE, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The inverse of the exponential factor. -/
theorem hbE_inv (Δ : ℝ) (n : ℕ) : (hbE Δ n)⁻¹ = hbE (-Δ) n := by
  rw [Complex.inv_eq_conj (Work.ZeroFreeTables.P3.hbE_norm Δ n), hbE_conj]

/-- Conjugation of a character value: `conj (χ a) = χ⁻¹ a` (also at non-units). -/
theorem conj_char {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    conj (χ (n : ZMod N)) = χ⁻¹ (n : ZMod N) :=
  MulChar.star_apply' χ (n : ZMod N)

/-- The algebraic expansion of `(1 + Re z₁)(1 + Re z₂)(1 + Re z₃)`. -/
theorem prod_three_re_expand (z1 z2 z3 : ℂ) :
    (1 + z1.re) * (1 + z2.re) * (1 + z3.re)
      = 1 + z1.re + z2.re + z3.re
        + (1/2) * ((z1*z2).re + (z1*conj z2).re + (z1*z3).re
            + (z1*conj z3).re + (z2*z3).re + (z2*conj z3).re)
        + (1/4) * ((z1*z2*z3).re + (z1*z2*conj z3).re
            + (z1*conj z2*z3).re + (conj z1*z2*z3).re) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ## The character relations forced by `χ₁χ₂χ₃ = 1`, `χ_j² = 1` -/

/-- `χ₁χ₂ = χ₃⁻¹`. -/
theorem chi12_eq_inv {N : ℕ} [NeZero N] {chi1 chi2 chi3 : DirichletCharacter ℂ N}
    (hprod : chi1 * chi2 * chi3 = 1) : chi1 * chi2 = chi3⁻¹ :=
  eq_inv_of_mul_eq_one_left hprod

/-- `χ₁χ₃ = χ₂⁻¹`. -/
theorem chi13_eq_inv {N : ℕ} [NeZero N] {chi1 chi2 chi3 : DirichletCharacter ℂ N}
    (hprod : chi1 * chi2 * chi3 = 1) : chi1 * chi3 = chi2⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hprod]; ac_rfl

/-- `χ₂χ₃ = χ₁⁻¹`. -/
theorem chi23_eq_inv {N : ℕ} [NeZero N] {chi1 chi2 chi3 : DirichletCharacter ℂ N}
    (hprod : chi1 * chi2 * chi3 = 1) : chi2 * chi3 = chi1⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hprod]; ac_rfl

/-- `χ₁χ₂χ₃⁻¹ = 1`. -/
theorem chi123_inv_eq_one {N : ℕ} [NeZero N] {chi1 chi2 chi3 : DirichletCharacter ℂ N}
    (hsq3 : chi3 ^ 2 = 1) (hprod : chi1 * chi2 * chi3 = 1) : chi1 * chi2 * chi3⁻¹ = 1 := by
  have h3raw : chi3 * chi3 = 1 := by simpa only [pow_two] using hsq3
  have h3 : chi3⁻¹ = chi3 := inv_eq_of_mul_eq_one_left h3raw
  rw [chi12_eq_inv hprod, h3, h3raw]

/-- `χ₁χ₃χ₂⁻¹ = 1`. -/
theorem chi13_inv2_eq_one {N : ℕ} [NeZero N] {chi1 chi2 chi3 : DirichletCharacter ℂ N}
    (hsq2 : chi2 ^ 2 = 1) (hprod : chi1 * chi2 * chi3 = 1) : chi1 * chi3 * chi2⁻¹ = 1 := by
  have h2raw : chi2 * chi2 = 1 := by simpa only [pow_two] using hsq2
  have h2 : chi2⁻¹ = chi2 := inv_eq_of_mul_eq_one_left h2raw
  rw [chi13_eq_inv hprod, h2, h2raw]

/-- `χ₂χ₃χ₁⁻¹ = 1`. -/
theorem chi23_inv1_eq_one {N : ℕ} [NeZero N] {chi1 chi2 chi3 : DirichletCharacter ℂ N}
    (hsq1 : chi1 ^ 2 = 1) (hprod : chi1 * chi2 * chi3 = 1) : chi2 * chi3 * chi1⁻¹ = 1 := by
  have h1raw : chi1 * chi1 = 1 := by simpa only [pow_two] using hsq1
  have h1 : chi1⁻¹ = chi1 := inv_eq_of_mul_eq_one_left h1raw
  rw [chi23_eq_inv hprod, h1, h1raw]

end Work.ZeroFreeTables.P10
