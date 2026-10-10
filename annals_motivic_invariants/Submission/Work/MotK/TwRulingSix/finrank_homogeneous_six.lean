import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRulingSix

/-- The space of homogeneous degree-6 polynomials in 5 variables over a field `R` has dimension 210
(= the number of degree-6 monomials in 5 variables = `C(10,4)` = `5.multichoose 6`).

Route (the degree-6 analogue of `Submission/Work/MotK/TwRuling/GUIDE_finrank_homogeneous_five.md`):
`MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 5) R 6` rewrites the submodule as
`AddMonoidAlgebra.supported R R {d : Fin 5 →₀ ℕ | d.degree = 6}`;
`MvPolynomial.basisMonomials (Fin 5) R` (underlying family `fun s => monomial s 1`, see
`MvPolynomial.coe_basisMonomials`) restricts to a basis indexed by the subtype
`{d : Fin 5 →₀ ℕ // d.degree = 6}`, so `finrank_span_eq_card` gives
`Module.finrank R ↥(MvPolynomial.homogeneousSubmodule (Fin 5) R 6) = Fintype.card {d : Fin 5 →₀ ℕ // d.degree = 6}`.
For the cardinality either use `Finset.finsuppAntidiagEquivSubtype` /
`Finset.card_finsuppAntidiag_nat_eq_multichoose` (`#s = 5`, `n = 6`, giving `5.multichoose 6 = 210`)
or the equivalence with `Sym (Fin 5) 6` (`Sym.card_sym_eq_multichoose`, `card_sym_fin_eq_multichoose`)
together with `Nat.multichoose_eq` and `decide`/`norm_num`.  A `Fintype` instance on the subtype may
have to be built by hand (e.g. `Set.Finite.fintype` via `Finsupp.finite_of_nat_weight_eq` with the
constant weight `1`, or transport along an explicit equivalence).  If the exact equality proves
awkward, `Module.finrank R ↥(MvPolynomial.homogeneousSubmodule (Fin 5) R 6) ≤ 210` is also acceptable
as a fallback, but please deliver the equality if you can. -/
theorem finrank_homogeneous_six (R : Type) [Field R] :
    Module.finrank R ↥(MvPolynomial.homogeneousSubmodule (Fin 5) R 6) = 210 := by
  classical
  -- The index set of degree-6 monomials in 5 variables.
  let s : Set (Fin 5 →₀ ℕ) := {d | d.degree = 6}
  -- It is in bijection with `Sym (Fin 5) 6` (multisets of size 6 over `Fin 5`).
  let e : Sym (Fin 5) 6 ≃ ↥s := Sym.equivNatSum (Fin 5) 6
  haveI inst : Fintype ↥s := Fintype.ofEquiv _ e
  -- Cardinality: `#s = multichoose 5 6 = choose 10 6 = 210`.
  have hcard : Fintype.card ↥s = 210 := by
    rw [← Fintype.card_congr e, Sym.card_sym_fin_eq_multichoose, Nat.multichoose_eq]
    decide
  -- The homogeneous submodule is the supported submodule, whose finrank equals `#s`.
  have hfr : Module.finrank R ↥(MvPolynomial.homogeneousSubmodule (Fin 5) R 6)
      = Fintype.card ↥s := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact (LinearEquiv.finrank_eq
        (AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) (s := s))).trans
      (by rw [Module.finrank_finsupp_self])
  rw [hfr, hcard]

end Work.MotK.TwRulingSix
