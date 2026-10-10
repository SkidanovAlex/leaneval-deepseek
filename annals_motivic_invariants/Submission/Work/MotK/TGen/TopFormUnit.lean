import Mathlib
import Submission.Work.MotK.TGen.FwTopDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top form of a nonzero polynomial

`Work.MotK.TGen.topForm p` is the homogeneous component of `p` of degree `p.totalDegree`, i.e.
the leading form of `p`.  This file proves that it is nonzero for `p ≠ 0`, and that if it is a
unit then so is `p` (indeed, `p` is then a nonzero constant).

The key ingredient is `MvPolynomial.coeff_homogeneousComponent` together with the fact that the
`totalDegree`, being the supremum of the degrees of the monomials in the support of a nonzero
polynomial, is attained.
-/

set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-- **The top form of a nonzero polynomial is nonzero.**  `topForm p = homogeneousComponent
p.totalDegree p` contains the coefficient of any monomial of degree `p.totalDegree`, and such a
monomial exists in the support of `p` because the sup defining `totalDegree` is attained. -/
lemma topForm_ne_zero (p : MvPolynomial (Fin 3) K) (hp : p ≠ 0) : topForm p ≠ 0 := by
  intro h
  -- the support is nonempty, so the sup of the degrees is attained
  have hsupp : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  obtain ⟨d, hdmem, hdsup⟩ :=
    Finset.exists_mem_eq_sup p.support hsupp (fun m => (Finsupp.toMultiset m).card)
  have hd : Finsupp.degree d = p.totalDegree := by
    rw [MvPolynomial.totalDegree_eq, hdsup, Finsupp.card_toMultiset, Finsupp.degree_apply]
    rfl
  -- `d` is then a monomial of degree `totalDegree`, so its coefficient survives in `topForm p`
  have hcoeff : (topForm p).coeff d = p.coeff d := by
    rw [topForm, MvPolynomial.coeff_homogeneousComponent, ite_eq_left hd]
  rw [h] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hdmem) hcoeff.symm

/-- If the top form of `p` is a unit then `p` itself is a unit: a unit of a polynomial ring over
a field is a nonzero constant, so `IsUnit (topForm p)` forces `p.totalDegree = 0`, and then `p` is
a constant (with the same constant term as its top form). -/
theorem TopFormUnit (K : Type) [Field K] (c : MvPolynomial (Fin 3) K) (hc : c ≠ 0) :
    Work.MotK.TGen.topForm c ≠ 0 ∧ (IsUnit (Work.MotK.TGen.topForm c) → IsUnit c) := by
  refine ⟨topForm_ne_zero c hc, fun h => ?_⟩
  have hne : topForm c ≠ 0 := topForm_ne_zero c hc
  -- `topForm c` is homogeneous of degree `c.totalDegree`, hence has that total degree
  have hdeg : (topForm c).totalDegree = c.totalDegree :=
    (MvPolynomial.homogeneousComponent_isHomogeneous c.totalDegree c).totalDegree hne
  -- a unit of `K[X₀,X₁,X₂]` has total degree `0`
  rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced] at h
  obtain ⟨h1, h2⟩ := h
  have hc0 : c.totalDegree = 0 := by rw [← hdeg]; exact h2
  have hcC : c = MvPolynomial.C (c.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hc0
  -- and then `c` is that constant, whose constant term is a unit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨c.coeff 0, ?_, hcC⟩
  have htop : topForm c = MvPolynomial.C (c.coeff 0) := by
    rw [topForm, hc0, MvPolynomial.homogeneousComponent_zero]
  rw [htop, MvPolynomial.coeff_C] at h1
  simpa using h1

end Work.MotK.TGen
