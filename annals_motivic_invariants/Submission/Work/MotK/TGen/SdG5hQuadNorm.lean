import Mathlib
import Submission.Work.MotK.TGen.CruxAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.SdG5hQuadNorm` — normalisation of a homogeneous quadratic

A homogeneous quadratic form in three variables whose `x₀²`-coefficient is non-zero is a
non-zero scalar multiple of the *monic* `quadF p q r s t = x₀² + (p x₁ + q x₂) x₀ + (r x₁² + s x₁x₂ + t x₂²)`.

This is the bookkeeping step that lets the monic-quadratic factor of `Gg` (produced by
`SdG5hHomogFac`) be fed into `SdG5hQuadEquations` / `SdG5hQuadAlg`.

The proof is a direct coefficient computation: a homogeneous degree-two polynomial in three
variables only involves the six monomials `x₀², x₀x₁, x₀x₂, x₁², x₁x₂, x₂²`, and the
`x₀²`-coefficient is non-zero, so the form is the scalar `F.coeff x₀²` times the monic normal
form.  The finite combinatorics is the classification of the finsupps of degree two
(`classify`), and the coefficient extraction is `coeff_six`.
-/

set_option linter.unusedSimpArgs false

namespace Work.MotK.TGen

open MvPolynomial

/-- The finsupp of a product of two (possibly equal) variables, `xᵢxⱼ`. -/
private noncomputable def pair (i j : Fin 3) : Fin 3 →₀ ℕ := Finsupp.single i 1 + Finsupp.single j 1

variable {K : Type} [Field K]

/-- A finsupp over `Fin 3` is determined by its three values. -/
private lemma pair_eq_iff_vals {u : Fin 3 →₀ ℕ} {i j : Fin 3} :
    pair i j = u ↔ u 0 = (pair i j) 0 ∧ u 1 = (pair i j) 1 ∧ u 2 = (pair i j) 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    ext k
    fin_cases k <;> simp_all

/-- `xᵢxⱼ` is the monomial with exponent vector `pair i j`. -/
private lemma X_mul_X_eq_monomial (i j : Fin 3) :
    (X i * X j : MvPolynomial (Fin 3) K) = monomial (pair i j) 1 := by
  rw [pair, ← pow_one (X i), ← pow_one (X j), X_pow_eq_monomial, X_pow_eq_monomial,
    monomial_mul_monomial, mul_one]

/-- The coefficient of `xᵢxⱼ`. -/
private lemma coeff_X_mul_X (i j : Fin 3) (m : Fin 3 →₀ ℕ) :
    (X i * X j : MvPolynomial (Fin 3) K).coeff m = if pair i j = m then 1 else 0 := by
  rw [X_mul_X_eq_monomial, coeff_monomial]

/-- The exponent vector of `xᵢxⱼ` has total degree two. -/
private lemma degree_pair (i j : Fin 3) : (pair i j : Fin 3 →₀ ℕ).degree = 2 := by
  rw [pair, map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- Coefficients of the six-term expansion of a homogeneous quadratic form. -/
private lemma coeff_six (a b c d e f : K) (m : Fin 3 →₀ ℕ) :
    (C a * (X 0 * X 0) + C b * (X 0 * X 1) + C c * (X 0 * X 2) + C d * (X 1 * X 1)
      + C e * (X 1 * X 2) + C f * (X 2 * X 2) : MvPolynomial (Fin 3) K).coeff m
    = a * (if pair 0 0 = m then 1 else 0) + b * (if pair 0 1 = m then 1 else 0)
      + c * (if pair 0 2 = m then 1 else 0) + d * (if pair 1 1 = m then 1 else 0)
      + e * (if pair 1 2 = m then 1 else 0) + f * (if pair 2 2 = m then 1 else 0) := by
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    coeff_X_mul_X]

/-- The only exponent vectors of total degree two over `Fin 3` are the six products `xᵢxⱼ`. -/
private lemma classify (m : Fin 3 →₀ ℕ) (hm : m.degree = 2) :
    m = pair 0 0 ∨ m = pair 0 1 ∨ m = pair 0 2 ∨ m = pair 1 1 ∨ m = pair 1 2 ∨ m = pair 2 2 := by
  have h : m 0 + m 1 + m 2 = m.degree := by rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
  have key : (m 0 = 2 ∧ m 1 = 0 ∧ m 2 = 0) ∨ (m 0 = 1 ∧ m 1 = 1 ∧ m 2 = 0)
      ∨ (m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 1) ∨ (m 0 = 0 ∧ m 1 = 2 ∧ m 2 = 0)
      ∨ (m 0 = 0 ∧ m 1 = 1 ∧ m 2 = 1) ∨ (m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 2) := by omega
  rcases key with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
  · left; ext k; fin_cases k <;> simp_all [pair, Finsupp.add_apply]
  · right; left; ext k; fin_cases k <;> simp_all [pair, Finsupp.add_apply]
  · right; right; left; ext k; fin_cases k <;> simp_all [pair, Finsupp.add_apply]
  · right; right; right; left; ext k; fin_cases k <;> simp_all [pair, Finsupp.add_apply]
  · right; right; right; right; left; ext k; fin_cases k <;> simp_all [pair, Finsupp.add_apply]
  · right; right; right; right; right; ext k; fin_cases k <;> simp_all [pair, Finsupp.add_apply]

/-- The expansion of `C a * quadF p q r s t` into the six monomials, with the scalar pulled in. -/
private lemma C_mul_quadF (a p q r s t : K) :
    C a * quadF p q r s t
      = C a * (X 0 * X 0) + C (a * p) * (X 0 * X 1) + C (a * q) * (X 0 * X 2)
        + C (a * r) * (X 1 * X 1) + C (a * s) * (X 1 * X 2) + C (a * t) * (X 2 * X 2) := by
  rw [quadF, BB, CC]
  simp only [map_mul]
  first | refl_ring1 | ring

theorem SdG5hQuadNorm {K : Type} [Field K] (F : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous 2) (hc : F.coeff (Finsupp.single (0 : Fin 3) 2) ≠ 0) :
    ∃ c p q r s t : K, c ≠ 0 ∧ F = MvPolynomial.C c * Work.MotK.TGen.quadF p q r s t := by
  have hpair00 : pair (0 : Fin 3) 0 = Finsupp.single 0 2 := by
    rw [pair, ← Finsupp.single_add]
  have ha : F.coeff (pair (0 : Fin 3) 0) ≠ 0 := by rw [hpair00]; exact hc
  -- the six-term expansion of `F`
  have hF_eq : F = C (F.coeff (pair 0 0)) * (X 0 * X 0) + C (F.coeff (pair 0 1)) * (X 0 * X 1)
      + C (F.coeff (pair 0 2)) * (X 0 * X 2) + C (F.coeff (pair 1 1)) * (X 1 * X 1)
      + C (F.coeff (pair 1 2)) * (X 1 * X 2) + C (F.coeff (pair 2 2)) * (X 2 * X 2) := by
    ext m
    rw [coeff_six]
    by_cases hm : m.degree = 2
    · rcases classify m hm with h | h | h | h | h | h
      · rw [h]; simp only [pair_eq_iff_vals]; simp [pair, Finsupp.add_apply]
      · rw [h]; simp only [pair_eq_iff_vals]; simp [pair, Finsupp.add_apply]
      · rw [h]; simp only [pair_eq_iff_vals]; simp [pair, Finsupp.add_apply]
      · rw [h]; simp only [pair_eq_iff_vals]; simp [pair, Finsupp.add_apply]
      · rw [h]; simp only [pair_eq_iff_vals]; simp [pair, Finsupp.add_apply]
      · rw [h]; simp only [pair_eq_iff_vals]; simp [pair, Finsupp.add_apply]
    · have hne : ∀ i j : Fin 3, pair i j ≠ m := by
        intro i j heq
        exact hm (by rw [← heq]; exact degree_pair i j)
      rw [hF.coeff_eq_zero hm]
      simp only [ite_eq_right (hne 0 0), ite_eq_right (hne 0 1), ite_eq_right (hne 0 2),
        ite_eq_right (hne 1 1), ite_eq_right (hne 1 2), ite_eq_right (hne 2 2),
        mul_zero, add_zero, zero_add]
  refine ⟨F.coeff (pair 0 0), F.coeff (pair 0 1) / F.coeff (pair 0 0),
    F.coeff (pair 0 2) / F.coeff (pair 0 0), F.coeff (pair 1 1) / F.coeff (pair 0 0),
    F.coeff (pair 1 2) / F.coeff (pair 0 0), F.coeff (pair 2 2) / F.coeff (pair 0 0),
    ha, ?_⟩
  have h01 : F.coeff (pair 0 0) * (F.coeff (pair 0 1) / F.coeff (pair 0 0))
      = F.coeff (pair 0 1) := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  have h02 : F.coeff (pair 0 0) * (F.coeff (pair 0 2) / F.coeff (pair 0 0))
      = F.coeff (pair 0 2) := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  have h11 : F.coeff (pair 0 0) * (F.coeff (pair 1 1) / F.coeff (pair 0 0))
      = F.coeff (pair 1 1) := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  have h12 : F.coeff (pair 0 0) * (F.coeff (pair 1 2) / F.coeff (pair 0 0))
      = F.coeff (pair 1 2) := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  have h22 : F.coeff (pair 0 0) * (F.coeff (pair 2 2) / F.coeff (pair 0 0))
      = F.coeff (pair 2 2) := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  rw [C_mul_quadF, h01, h02, h11, h12, h22]
  exact hF_eq

end Work.MotK.TGen
