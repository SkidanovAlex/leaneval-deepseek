import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

/-- **Every non-constant rational function has a pole somewhere.**  If `f : F(t)` is not a
constant (`¬ ∃ c, f = algebraMap F (RatFunc F) c`), then either `f` has a pole at the place of some
irreducible `π`, or `f` has a pole at infinity.

Route: `f = num / denom` in reduced form with `denom` monic.  If `denom ≠ 1` then `denom` is
non-constant, hence has an irreducible factor `π` (`WfDvdMonoid.exists_irreducible_factor`), and
`ord π f = - multiplicity π denom < 0` (`RatFunc.isCoprime_num_denom` gives `π ∤ num`).  If
`denom = 1`, then `f = num` is a non-constant polynomial (otherwise `f` would be a constant,
contradicting the hypothesis) and `ordInf f = - num.natDegree < 0` (`ordInf_polynomial`). -/
theorem exists_ord_neg_or_ordInf_neg {F : Type*} [Field F] {f : RatFunc F}
    (h : ¬ ∃ c : F, f = algebraMap F (RatFunc F) c) :
    (∃ π : Polynomial F, Irreducible π ∧ Work.Genus.ord π f < 0) ∨ Work.Genus.ordInf f < 0 := by
  by_cases hπ : ∃ π : Polynomial F, Irreducible π ∧ Work.Genus.ord π f < 0
  · exact Or.inl hπ
  · -- No finite pole: `f` is a polynomial, and being non-constant it must have a pole at infinity.
    right
    obtain ⟨p, hp⟩ := Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg
      (fun π hπi => by
        by_contra hlt
        exact hπ ⟨π, hπi, lt_of_not_ge hlt⟩)
    rw [hp, Work.Genus.OrderInf.ordInf_polynomial]
    by_contra hle
    rw [not_lt] at hle
    -- `0 ≤ -deg p` forces `deg p = 0`, i.e. `f` is the constant `p.coeff 0`, contradicting `h`.
    have hdeg : p.natDegree = 0 := by omega
    refine h ⟨p.coeff 0, ?_⟩
    rw [hp]
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    exact (IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F) (p.coeff 0)).symm

end Work.Genus.Main
