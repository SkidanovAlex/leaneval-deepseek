import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.Q44Child.witness_class_count

/-!
# The `ℚ`-model of the witness class (`Work.HP.MDEstimates.WClassDefs`)

`Work.HP.linForm v i = ∑_j C(v_{j,i}) X_j` is a linear form over `ℤ`; `Work.HP.verPoly v m`
is a product of its powers over `ℤ`, and `Work.HP.wCoeff v e m` is its `e`-coefficient.  To
be able to *evaluate* these polynomials (at rational points) and to compare with
`Work.HP.formEval`, we need the same objects over `ℚ`, which is what this file provides.

The identity that matters is

`Work.HP.MDEstimates.verPolyQ v m = (Work.HP.verPoly v m).map (Int.castRingHom ℚ)`,

from which the coefficients agree, together with the evaluation formula
`eval s (verPolyQ v m) = ∏_i (∑_j s_j v_{j,i})^{m_i}`.
-/

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDEstimates

/-- `Work.HP.linForm` with `ℚ`-coefficients. -/
def linFormQ (v : Fin 3 → (Fin 5 → ℤ)) (i : Fin 5) : MvPolynomial (Fin 3) ℚ :=
  ∑ j : Fin 3, MvPolynomial.C ((v j i : ℤ) : ℚ) * MvPolynomial.X j

/-- `Work.HP.verPoly` with `ℚ`-coefficients. -/
def verPolyQ (v : Fin 3 → (Fin 5 → ℤ)) (m : Work.HP.Mon 4 4) : MvPolynomial (Fin 3) ℚ :=
  ∏ i : Fin 5, (linFormQ v i) ^ (m.1 i : ℕ)

lemma linFormQ_isHomogeneous (v : Fin 3 → (Fin 5 → ℤ)) (i : Fin 5) :
    (linFormQ v i).IsHomogeneous 1 := by
  rw [linFormQ]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun j _ => ?_)
  have h := (MvPolynomial.isHomogeneous_C (Fin 3) (((v j i : ℤ) : ℚ))).mul
    (MvPolynomial.isHomogeneous_X ℚ j)
  simpa using h

lemma verPolyQ_isHomogeneous (v : Fin 3 → (Fin 5 → ℤ)) (m : Work.HP.Mon 4 4) :
    (verPolyQ v m).IsHomogeneous 4 := by
  rw [verPolyQ]
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin 5))
    (fun i : Fin 5 => (linFormQ v i) ^ (m.1 i : ℕ)) (fun i => (m.1 i : ℕ))
    (fun i _ => by simpa using (linFormQ_isHomogeneous v i).pow (m.1 i : ℕ))
  simpa [m.2] using h

lemma eval_linFormQ (v : Fin 3 → (Fin 5 → ℤ)) (s : Fin 3 → ℚ) (i : Fin 5) :
    MvPolynomial.eval s (linFormQ v i) = ∑ j : Fin 3, s j * (v j i : ℚ) := by
  rw [linFormQ]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  ring

lemma eval_verPolyQ_lin (v : Fin 3 → (Fin 5 → ℤ)) (s : Fin 3 → ℚ) (m : Work.HP.Mon 4 4) :
    MvPolynomial.eval s (verPolyQ v m)
      = ∏ i : Fin 5, (∑ j : Fin 3, s j * (v j i : ℚ)) ^ (m.1 i : ℕ) := by
  rw [verPolyQ]
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_pow, eval_linFormQ]

lemma verPolyQ_eq_map (v : Fin 3 → (Fin 5 → ℤ)) (m : Work.HP.Mon 4 4) :
    verPolyQ v m = (Work.HP.verPoly v m).map (Int.castRingHom ℚ) := by
  rw [verPolyQ, Work.HP.verPoly]
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_pow]
  congr 1
  rw [linFormQ, Work.HP.linForm]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rfl

lemma verPolyQ_coeff (v : Fin 3 → (Fin 5 → ℤ)) (m : Work.HP.Mon 4 4) (d : Fin 3 →₀ ℕ) :
    (verPolyQ v m).coeff d = ((Work.HP.verPoly v m).coeff d : ℚ) := by
  rw [verPolyQ_eq_map, MvPolynomial.coeff_map]
  rfl

end Work.HP.MDEstimates
