/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Submission.Helpers
import Submission.Models
import Submission.Models2
import Submission.Commons.NumberTheory.NumberField.small_algebraic_model
import Submission.Commons.Analysis.SpecialFunctions.exists_model_count_bound
import Submission.Commons.Algebra.MvPolynomial.card_bounded_polys_le
import Submission.Commons.RingTheory.Ideal.card_minimalPrimes_quotient_le
import ChallengeDeps
/-!
# Main Statements from Enumerating number fields

We formalise the statements of the main results from J.-M. Couveignes,
`Enumerating number fields`, Annals of Math, 192 (2) 2020.
-/


namespace Submission

open _root_.EnumeratingNumberFields
open _root_.EnumeratingNumberFields.NumberFieldOfBoundedDiscriminant
open _root_.EnumeratingNumberFields.NumberFieldOfDegree
set_option autoImplicit false

namespace EnumeratingNumberFields

open AlgebraicGeometry Module NumberField Real Scheme

section theorem_1









noncomputable section

variable {r : ℕ} (E : Fin r → MvPolynomial (Fin r) ℚ)









end

/--
Statement of Theorem 1 (Number fields have small models):

There exists a positive constant `Q` such that the following is true. Let `K` be a number field
of degree `n ≥ Q` and root discriminant `δ` over `ℚ`. Then there exist integers `r ≤ Q log n` and
`d ≤ Q log n` such that `(d + r) choose r ≤ Q n log n`, and there exist `r` polynomials
`E₁, ..., Eᵣ` of degree `≤ d` in `ℤ[x₁, ..., xᵣ]` all having coefficients bounded in absolute value
by `(n δ) ^ (Q log n)` such that the (smooth and zero-dimensional affine) scheme with equations
`E₁ = ... = Eᵣ = 0` and `det (∂Eᵢ/∂xⱼ) ≠ 0` contains `Spec K` as one of its irreducible components.
-/
theorem theorem_1 : ∃ Q > 0, ∀ n ≥ Q, ∀ K : NumberFieldOfDegree n, ∃ (r d : ℕ),
    r ≤ Q * log n ∧ d ≤ Q * log n ∧ (d + r).choose r ≤ Q * n * log n ∧
      ∃ E : Fin r → MvPolynomial (Fin r) ℤ, (∀ i, (E i).totalDegree ≤ d) ∧
        (∀ i j, |(E i).coeff j| ≤ (n * rootDiscr K) ^ (Q * log n)) ∧
          letI X := nonsingularOpen fun i ↦ (E i).map (algebraMap ℤ ℚ)
          ∃ Z, ∃ hZ : Z ∈ irreducibleComponents X,
            Nonempty (X.irreducibleComponent Z hZ ≅ Spec (.of K)) :=
  Submission.Models.theorem_1_of_algebraic_model
    Commons.NumberTheory.NumberField.small_algebraic_model

end theorem_1

section theorem_2











/--
Statement of Theorem 2 (Number fields with bounded discriminant):

There exists a positive constant `Q` such that the following is true. Let `n ≥ Q` be an integer.
Let `H ≥ 1` be an integer. The number of isomorphism classes of number fields
with degree `n` and discriminant `≤ H` is `≤ n^(Q n log^3 n) H^(Q log^3 n)`.
-/
theorem theorem_2 : ∃ Q > 0, ∀ n ≥ Q, ∀ H ≥ 1,
    (Nat.card (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) : ℝ) ≤
      n ^ (Q * n * log n ^ 3) * H ^ (Q * log n ^ 3) :=
  Submission.Models2.theorem_2_of_model
    Commons.NumberTheory.NumberField.small_algebraic_model
    (fun Q₁ hQ₁ => by
      obtain ⟨Q, hQpos, hQb⟩ := Commons.Analysis.SpecialFunctions.exists_model_count_bound Q₁ hQ₁
      exact ⟨Q, hQpos, fun n hn H hH => hQb (n : ℝ) hn (H : ℝ) (by exact_mod_cast hH)⟩)
    (fun r d K₀ => Commons.Algebra.MvPolynomial.card_bounded_polys_le r d K₀)
    (fun {k} _ {r} f => Commons.RingTheory.Ideal.card_minimalPrimes_quotient_le f)

end theorem_2

end EnumeratingNumberFields

end Submission
