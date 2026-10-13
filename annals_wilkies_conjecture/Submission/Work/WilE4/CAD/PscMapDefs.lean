/-
  WilE4 / CAD — the linear map whose matrix is the principal subresultant matrix.

  `Work.WilE4.CAD.pscMat f g m n i` is the submatrix of the Sylvester matrix on the rows
  `pscRow m n i` (the powers `X ^ (2 * i), …, X ^ (m + n - 1)`) and the columns `pscCol m n i`
  (the multiples `X ^ k * f` for `i ≤ k ≤ n - 1`, then `X ^ k * g` for `i ≤ k ≤ m - 1`); its
  determinant is the principal subresultant coefficient `psc f g m n i`.

  This file introduces the linear map `pscMap f g m n i` of which that matrix is the matrix, in the
  standard monomial bases:

  `pscMap f g m n i : ℝ[X]_{< n - i} × ℝ[X]_{< m - i} → (Fin (m + n - 2 * i) → ℝ)`,
  `(A, B) ↦ (r ↦ (A * f + B * g).coeff (i + r))`.

  Its kernel is `{(A, B) : A * f + B * g ∈ ℝ[X]_{< i}}`; in particular, at `i = deg (gcd f g)` it is
  trivial (`psc_gcd_natDegree_ne_zero`), and below that degree it is not
  (`psc_eq_zero_of_lt_gcd`).  The identification of `pscMat f g m n i` with the matrix of
  `pscMap f g m n i` rests on the entry formula `pscMat_apply` of
  `Submission.Work.WilE4.CAD.psc_entry`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Proj

set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE4.CAD

open Polynomial Matrix

/-- The linear map `(A, B) ↦ (r ↦ (A * f + B * g).coeff (i + r))` from
`ℝ[X]_{< n - i} × ℝ[X]_{< m - i}` to `Fin (m + n - 2 * i) → ℝ`.

(The two spaces have the same dimension `(n - i) + (m - i)` as soon as `i ≤ min m n`, and then the
matrix of this map in the standard bases is `pscMat f g m n i`; see
`Submission.Work.WilE4.CAD.pscMat_apply_pscMap`.) -/
def pscMap (f g : Polynomial ℝ) (m n i : ℕ) :
    (Polynomial.degreeLT ℝ (n - i) × Polynomial.degreeLT ℝ (m - i)) →ₗ[ℝ]
      (Fin (m + n - 2 * i) → ℝ) :=
  LinearMap.pi fun r : Fin (m + n - 2 * i) =>
    (Polynomial.lcoeff ℝ (i + (r : ℕ))).comp
      (((LinearMap.mulLeft ℝ f).comp
          ((Polynomial.degreeLT ℝ (n - i)).subtype.comp (LinearMap.fst ℝ _ _))) +
       ((LinearMap.mulLeft ℝ g).comp
          ((Polynomial.degreeLT ℝ (m - i)).subtype.comp (LinearMap.snd ℝ _ _))))

/-- The value of `pscMap` at `(A, B)` is the vector of coefficients of `A * f + B * g` at the
powers `X ^ i, …, X ^ (m + n - i - 1)`. -/
@[simp]
theorem pscMap_apply (f g : Polynomial ℝ) (m n i : ℕ)
    (P : Polynomial.degreeLT ℝ (n - i) × Polynomial.degreeLT ℝ (m - i))
    (r : Fin (m + n - 2 * i)) :
    pscMap f g m n i P r
      = (f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).coeff (i + (r : ℕ)) := by
  rw [pscMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply, Submodule.subtype_apply,
    LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, Polynomial.lcoeff_apply]

/-- `pscMap` vanishes at `(A, B)` exactly when `A * f + B * g` has all its coefficients at the
powers `X ^ i, …, X ^ (m + n - i - 1)` equal to zero. -/
theorem pscMap_eq_zero_iff (f g : Polynomial ℝ) (m n i : ℕ)
    (P : Polynomial.degreeLT ℝ (n - i) × Polynomial.degreeLT ℝ (m - i)) :
    pscMap f g m n i P = 0 ↔
      ∀ r : Fin (m + n - 2 * i),
        (f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).coeff (i + (r : ℕ)) = 0 := by
  rw [funext_iff]
  simp only [pscMap_apply, Pi.zero_apply]

end Work.WilE4.CAD
