import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.RealExtract

namespace Work.WilC4aP

open Polynomial

/-- The `i`-th coefficient of `polyOf F`, written in terms of the coefficients of the two
summands. -/
lemma polyOf_coeff {d : ℕ} (F : Fin d → ℂ → ℂ) (i : ℕ) :
    (polyOf F).coeff i =
      (if i = d then 1 else 0) + ∑ j : Fin d, F j * (if i = (j : ℕ) then 1 else 0) := by
  simp only [polyOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul]

/-- The `i`-th coefficient of `polyOf F` is a sum of `F j`'s and constants: only the term
`j = i` of the sum can survive. -/
lemma polyOf_coeff' {d : ℕ} (F : Fin d → ℂ → ℂ) (i : ℕ) :
    (polyOf F).coeff i =
      (if i = d then 1 else 0) + ∑ j : Fin d, (if i = (j : ℕ) then F j else 0) := by
  rw [polyOf_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = (j : ℕ) <;> simp [h]

/-- A function that is either one of the coefficients or `0` is holomorphic. -/
lemma analyticAt_ite_const {P : Prop} [Decidable P] {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (if P then f else 0) 0 := by
  split_ifs with h
  · exact hf
  · exact analyticAt_const

/-- `polyOf F` is monic: it is `X ^ d` plus a polynomial of degree `< d`. -/
lemma polyOf_monic {d : ℕ} (F : Fin d → ℂ → ℂ) : (polyOf F).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt F)

/-- `polyOf F` has degree `d`. -/
lemma polyOf_degree {d : ℕ} (F : Fin d → ℂ → ℂ) :
    (polyOf F).degree = (d : WithBot ℕ) := by
  have hS : (∑ j : Fin d, C (F j) * X ^ (j:ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt F
  have hX : (X ^ d : Polynomial (ℂ → ℂ)).degree = (d : WithBot ℕ) := Polynomial.degree_X_pow d
  show (X ^ d + ∑ j : Fin d, C (F j) * X ^ (j:ℕ)).degree = _
  rw [Polynomial.degree_add_eq_left_of_degree_lt (by rw [hX]; exact hS), hX]

/-- `polyOf F` has natDegree `d`. -/
lemma polyOf_natDegree {d : ℕ} (F : Fin d → ℂ → ℂ) : (polyOf F).natDegree = d :=
  Polynomial.natDegree_eq_of_degree_eq_some (polyOf_degree F)

/-- Every coefficient of `polyOf F` is holomorphic at `0` as soon as the `F j` are: each of
them is a constant or one of the `F j`. -/
lemma polyOf_holCoeffs {d : ℕ} (F : Fin d → ℂ → ℂ) (hF : ∀ j, AnalyticAt ℂ (F j) 0) :
    HolCoeffs (polyOf F) 0 := by
  intro i
  rw [polyOf_coeff']
  apply AnalyticAt.add
  · exact analyticAt_ite_const (f := fun _ : ℂ => (1 : ℂ)) analyticAt_const
  · apply Finset.analyticAt_sum Finset.univ
    intro j _
    exact analyticAt_ite_const (f := F j) (hF j)

/-- Basic facts about `polyOf F = Y ^ d + ∑ j, C (F j) * Y ^ j`, needed to feed it to the
Puiseux machinery: it is monic, of degree `d`, and its coefficients are holomorphic wherever
the `F j` are.

PROOF HINT: `Polynomial.degree_sum_fin_lt` bounds the degree of the sum by `d`, so
`Polynomial.monic_X_pow_add` gives monicity; then `natDegree_eq_of_degree_eq_some` after a
degree computation, or directly `natDegree_eq_of_le_of_coeff_ne_zero` with the coefficient
computation `(polyOf F).coeff i = (if i = d then 1 else 0) + ∑ j, F j * (if i = j then 1 else 0)`
(`Polynomial.coeff_add`, `Polynomial.finsetSum_coeff`, `Polynomial.coeff_C_mul`,
`Polynomial.coeff_X_pow`, `Finset.sum_ite_eq'`).  Analyticity: each coefficient is `1`, some
`F j`, or `0`. -/
theorem polyOf_basic {d : ℕ} (F : Fin d → ℂ → ℂ) (hF : ∀ j, AnalyticAt ℂ (F j) 0) :
    (Work.WilC4aP.polyOf F).Monic ∧ (Work.WilC4aP.polyOf F).natDegree = d ∧
      Work.WilC4aP.HolCoeffs (Work.WilC4aP.polyOf F) 0 :=
  ⟨polyOf_monic F, polyOf_natDegree F, polyOf_holCoeffs F hF⟩

end Work.WilC4aP
