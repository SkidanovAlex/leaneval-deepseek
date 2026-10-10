import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotK.TwRuling

/-! The space of homogeneous degree-5 polynomials in 5 variables over a field `R` has dimension 126
(= the number of degree-5 monomials in 5 variables = `C(9,5)`).

Route in `Submission/Work/MotK/TwRuling/GUIDE_finrank_homogeneous_five.md`.

The monomials of `MvPolynomial (Fin 5) R` form the basis `MvPolynomial.basisMonomials`, indexed by
exponent vectors `Fin 5 →₀ ℕ`.  The homogeneous component of degree `5` is spanned by those basis
vectors whose exponent vector has total degree `5`, so its dimension is the number of such exponent
vectors.  Counting them: `Finsupp.toMultiset` (with inverse `Multiset.toFinsupp`) identifies
`{d : Fin 5 →₀ ℕ // d.degree = 5}` with the multisets of size `5` over `Fin 5`, i.e. with
`Sym (Fin 5) 5`, whose cardinality is `5.multichoose 5 = C(9,4) = 126`. -/

/-- The degree-`5` exponent vectors of `MvPolynomial (Fin 5) R` correspond to the multisets of
size `5` over `Fin 5`: `Finsupp.toMultiset` sends an exponent vector `d` to the multiset with `d i`
copies of `i`, and its cardinality is the total degree `d.degree`. -/
noncomputable def finsuppDegreeFiveEquivSym :
    {d : Fin 5 →₀ ℕ // d.degree = 5} ≃ Sym (Fin 5) 5 where
  toFun d := ⟨Finsupp.toMultiset d.1, by
    rw [Finsupp.card_toMultiset,
      show Finsupp.sum d.1 (fun _ => id) = d.1.degree from rfl, d.2]⟩
  invFun s := ⟨Multiset.toFinsupp s.1, by
    rw [show (Multiset.toFinsupp s.1).degree = s.1.toFinsupp.sum (fun _ => id) from rfl,
      Multiset.toFinsupp_sum_eq, s.2]⟩
  left_inv d := by
    apply Subtype.ext
    exact Finsupp.toMultiset_toFinsupp d.1
  right_inv s := by
    apply Sym.ext
    exact Multiset.toFinsupp_toMultiset s.1

theorem finrank_homogeneous_five (R : Type) [Field R] :
    Module.finrank R ↥(MvPolynomial.homogeneousSubmodule (Fin 5) R 5) = 126 := by
  -- `Fintype` instance for the (finite) set of degree-`5` exponent vectors, transported from
  -- `Sym (Fin 5) 5`.
  letI : Fintype {d : Fin 5 →₀ ℕ // d.degree = 5} :=
    Fintype.ofEquiv (Sym (Fin 5) 5) finsuppDegreeFiveEquivSym.symm
  -- There are `5.multichoose 5 = 126` degree-`5` monomials in `5` variables.
  have hcard : Fintype.card {d : Fin 5 →₀ ℕ // d.degree = 5} = 126 := by
    rw [Fintype.card_congr finsuppDegreeFiveEquivSym, Sym.card_sym_eq_multichoose,
      Fintype.card_fin]
    norm_num [Nat.multichoose]
  -- The degree-`5` monomials are linearly independent (they are a subfamily of a basis).
  have hli : LinearIndependent R (fun d : {d : Fin 5 →₀ ℕ // d.degree = 5} =>
      (AddMonoidAlgebra.single d.1 1 : MvPolynomial (Fin 5) R)) := by
    have h := ((MvPolynomial.basisMonomials (Fin 5) R).linearIndependent).comp
      (Subtype.val : {d : Fin 5 →₀ ℕ // d.degree = 5} → (Fin 5 →₀ ℕ)) Subtype.val_injective
    rw [MvPolynomial.coe_basisMonomials] at h
    exact h
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.supported_eq_span_single, Set.image_eq_range]
  rw [show (Set.range (fun x : {x // x ∈ {d : Fin 5 →₀ ℕ | d.degree = 5}} =>
          (AddMonoidAlgebra.single (x : Fin 5 →₀ ℕ) 1 : MvPolynomial (Fin 5) R)))
        = Set.range (fun d : {d : Fin 5 →₀ ℕ // d.degree = 5} =>
          (AddMonoidAlgebra.single (d : Fin 5 →₀ ℕ) 1 : MvPolynomial (Fin 5) R)) from rfl]
  rw [finrank_span_eq_card hli, hcard]

end Work.MotK.TwRuling
