import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The multihomogeneous piece `homPiece N d ⊆ MvPolynomial (Fin (N+1) × Fin 2) ℂ` consisting of the
polynomials all of whose monomials have multidegree `d` is finite-dimensional over `ℂ`: by
`MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported` it is the span of the monomials
`monomial m 1` with `Finsupp.weight (mdeg N) m = d`, and the set of such `m` is finite because
`Finsupp.weight (mdeg N) m = d` forces `m v ≤ d v.1` for every `v`. This fact is needed to apply
the `finrank` lemmas (`Submodule.finrank_quotient_add_finrank`,
`Submodule.finrank_sup_add_finrank_inf_eq`) to the quotients that define `rayHilb`. -/
theorem rayHilb_finite (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    Module.Finite ℂ ↥(homPiece N d) := by
  rw [Module.Finite.iff_fg]
  refine Submodule.FG.of_le
    (MvPolynomial.homogeneousSubmodule_fg (Fin (N + 1) × Fin 2) ℂ (∑ i, d i)) ?_
  intro p hp
  rw [MvPolynomial.mem_homogeneousSubmodule, MvPolynomial.IsHomogeneous]
  intro a ha
  -- For `a` an exponent vector appearing in `p`, `Finsupp.weight (mdeg N) a = d`; we show that the
  -- total degree of `a` is `∑ i, d i`.
  have hkey : (Finsupp.degree a : ℕ) = ∑ i, Finsupp.weight (mdeg N) a i := by
    have h : (Finsupp.degree (Finsupp.weight (mdeg N) a) : ℕ) = ∑ v, a v := by
      rw [Finsupp.weight_eq_sum, map_sum]
      simp [mdeg, Finsupp.degree_single]
    rw [Finsupp.degree_eq_sum (f := a),
      (Finsupp.degree_eq_sum (f := Finsupp.weight (mdeg N) a)).symm, h]
  have hwa : Finsupp.weight (mdeg N) a = d := hp ha
  have h1 : Finsupp.weight (1 : Fin (N + 1) × Fin 2 → ℕ) a = Finsupp.degree a := by
    simp only [Finsupp.weight, Finsupp.degree_eq_weight_one]; rfl
  rw [h1, hkey, hwa]

end Work.BW
