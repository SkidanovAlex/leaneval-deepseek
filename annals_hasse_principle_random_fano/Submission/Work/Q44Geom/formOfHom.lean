import Mathlib
import Submission.Work.HP.Defs

/-!
# `Work.Q44Geom.formOfHom`

`Work.HP.formOf d n c` is the rational polynomial `∑_m c_m · X^{m}`, whose monomials all have
exponent vector of total degree `d`.  Hence it is homogeneous of degree `d`; here `d = n = 4`.

The only content is that the exponent vector of a monomial, transported to a `Finsupp` by
`Work.HP.Mon.toFinsupp`, has `Finsupp.degree = d` — which is exactly the defining property of an
element of `Work.HP.Mon d n`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.Q44Geom

/-- The exponent vector of a monomial, as a `Finsupp`, has total degree `d`. -/
lemma finsupp_degree_toFinsupp (m : Work.HP.Mon 4 4) :
    Finsupp.degree (Work.HP.Mon.toFinsupp m) = 4 := by
  rw [Finsupp.degree_eq_sum]
  simp only [Work.HP.Mon.toFinsupp, Finsupp.equivFunOnFinite_symm_apply_apply]
  exact m.2

theorem formOfHom (c : Work.HP.Mon 4 4 → ℤ) :
    (Work.HP.formOf 4 4 c).IsHomogeneous 4 := by
  rw [Work.HP.formOf]
  refine MvPolynomial.IsHomogeneous.sum Finset.univ (fun m : Work.HP.Mon 4 4 =>
    monomial (Work.HP.Mon.toFinsupp m) (c m : ℚ)) 4 ?_
  intro m _
  exact MvPolynomial.isHomogeneous_monomial _ (finsupp_degree_toFinsupp m)

end Work.Q44Geom
