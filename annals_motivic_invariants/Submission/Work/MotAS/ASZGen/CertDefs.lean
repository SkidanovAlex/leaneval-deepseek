import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZGen.CertDefs` -- certificate data for the AS eliminant irreducibility

`cf a b g` is the quartic `f = c4 X^4 + (g (a+2b)^5) X^3 + w2 X^2 + (g c3) X + w0` whose fifth
power appears in the annihilator of the element `W = cf(θ)` of `AdjoinRoot (X^5 - X - C g)` used in
`Work.MotAS.ASZElimIrredGen`.  It is an `abbrev` so that `ring` sees the explicit polynomial.

The degree/coefficient facts are proved through the auxiliary lemmas `natDegree_C_mul_X_le`,
`natDegree_sum5_le` and `coeff_four_shape`, which keep the (large) coefficient expressions out of
the goals handed to the arithmetic tactics.
-/

set_option maxHeartbeats 4000000

namespace Work.MotAS.ASZGen

open Polynomial

variable {K : Type*} [Field K]

/-- The quartic `f = c4 X^4 + (g (a+2b)^5) X^3 + w2 X^2 + (g c3) X + w0`. -/
noncomputable abbrev cf (a b g : K) : Polynomial K :=
  C (2*a^4*b+2*a^3*b^2-a^2*b^3+a*b^4) * X^4
  + C (g * (a+2*b)^5) * X^3
  + C (a*b*(3*a+b)*(a^2+b^2)) * X^2
  + C (g * (-a^5-a^4*b+2*a^3*b^2+a^2*b^3-2*a*b^4+2*b^5)) * X
  + C (-(a+2*b)*a^2*b^2)

/-- `natDegree (C c * X) ≤ 1`. -/
lemma natDegree_C_mul_X_le (c : K) : (C c * X : Polynomial K).natDegree ≤ 1 := by
  simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le c 1

/-- Degree bound for a sum of five monomial shaped polynomials. -/
lemma natDegree_sum5_le {R : Type*} [Semiring R] (p q r s t : Polynomial R)
    (hp : p.natDegree ≤ 4) (hq : q.natDegree ≤ 3) (hr : r.natDegree ≤ 2)
    (hs : s.natDegree ≤ 1) (ht : t.natDegree ≤ 0) :
    (p + q + r + s + t).natDegree ≤ 4 := by
  have hq4 : q.natDegree ≤ 4 := hq.trans (by decide)
  have hr4 : r.natDegree ≤ 4 := hr.trans (by decide)
  have hs4 : s.natDegree ≤ 4 := hs.trans (by decide)
  have ht4 : t.natDegree ≤ 4 := ht.trans (by decide)
  have h1 : (p + q).natDegree ≤ 4 :=
    (Polynomial.natDegree_add_le p q).trans (max_le hp hq4)
  have h2 : (p + q + r).natDegree ≤ 4 :=
    (Polynomial.natDegree_add_le (p + q) r).trans (max_le h1 hr4)
  have h3 : (p + q + r + s).natDegree ≤ 4 :=
    (Polynomial.natDegree_add_le (p + q + r) s).trans (max_le h2 hs4)
  exact (Polynomial.natDegree_add_le (p + q + r + s) t).trans (max_le h3 ht4)

/-- `cf a b g` has degree at most `4`. -/
lemma cf_natDegree_le (a b g : K) : (cf a b g).natDegree ≤ 4 := by
  simp only [cf]
  exact natDegree_sum5_le _ _ _ _ _
    (Polynomial.natDegree_C_mul_X_pow_le _ 4)
    (Polynomial.natDegree_C_mul_X_pow_le _ 3)
    (Polynomial.natDegree_C_mul_X_pow_le _ 2)
    (natDegree_C_mul_X_le _)
    (le_of_eq (Polynomial.natDegree_C _))

/-- The `X^4`-coefficient of a sum of five monomial shaped polynomials. -/
lemma coeff_four_shape {R : Type*} [Semiring R] (A B Dd E Ff : R) :
    (C A * X ^ 4 + C B * X ^ 3 + C Dd * X ^ 2 + C E * X + C Ff : Polynomial R).coeff 4
      = A := by
  have h4 : (C A * X ^ 4 : Polynomial R).coeff 4 = A := by
    rw [Polynomial.coeff_C_mul_X_pow]
    norm_num
  have h3 : (C B * X ^ 3 : Polynomial R).coeff 4 = 0 := by
    rw [Polynomial.coeff_C_mul_X_pow]
    norm_num
  have h2 : (C Dd * X ^ 2 : Polynomial R).coeff 4 = 0 := by
    rw [Polynomial.coeff_C_mul_X_pow]
    norm_num
  have h1 : (C E * X : Polynomial R).coeff 4 = 0 := by
    rw [Polynomial.coeff_C_mul_X]
    norm_num
  have h0 : (C Ff : Polynomial R).coeff 4 = 0 := by
    rw [Polynomial.coeff_C]
    norm_num
  simp only [Polynomial.coeff_add, h4, h3, h2, h1, h0, add_zero]

/-- The `X^4`-coefficient of `cf a b g`. -/
lemma cf_coeff_four (a b g : K) :
    (cf a b g).coeff 4 = 2*a^4*b+2*a^3*b^2-a^2*b^3+a*b^4 := by
  simp only [cf]
  exact coeff_four_shape _ _ _ _ _

end Work.MotAS.ASZGen
