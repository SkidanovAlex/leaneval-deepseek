import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Points of coheight zero are generic points

For an irreducible scheme `X`, a point `x` whose coheight (with respect to the specialisation
preorder on `X`) is `0` is the generic point of `X`.

Concretely: a scheme is given the *specialisation preorder*, in which `a ≤ b` iff `a` lies in the
closure of `b` (`AlgebraicGeometry.Scheme.le_iff_specializes`), so that the generic point of an
irreducible component is a *maximal* element.  Thus `Order.coheight x = 0` says that `x` is
maximal (`Order.coheight_eq_zero`), i.e. that `x` is the generic point of an irreducible component
of `X`.  If in addition `X` is irreducible, its only irreducible component is `X` itself, so
`closure {x} = univ`: every point specializes to `x`, and as `X` is a `T₀` space (indeed every
scheme is `T₀` and quasi-sober), `x` is the unique generic point of `X`, namely `genericPoint X`.

The argument only uses that `X` is a quasi-sober `T₀` irreducible topological space, so it is
proved below in that generality (`eq_genericPoint_of_coheight_eq_zero_of_quasiSober`) and then
specialised to schemes.
-/

namespace Work.K3

attribute [local instance] specializationPreorder in
/-- **A point of coheight zero in a quasi-sober `T₀` irreducible space is its generic point.**
Here the space carries its specialisation preorder (`a ≤ b` iff `a ∈ closure {b}`). -/
theorem eq_genericPoint_of_coheight_eq_zero_of_quasiSober {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] [IrreducibleSpace α] (x : α) (h : Order.coheight x = 0) :
    x = genericPoint α := by
  -- `coheight x = 0` means that `x` is maximal in the specialisation order.
  have hmax : IsMax x := Order.coheight_eq_zero.mp h
  -- Every point lies below the generic point, which therefore is the top element of the order;
  -- maximality of `x` then forces `x` itself to be the top: every point lies below `x`.
  have htop : ∀ y : α, y ≤ x := by
    intro y
    have h1 : y ≤ genericPoint α := by
      rw [← Set.mem_Iic, ← closure_singleton_eq_Iic]
      exact specializes_iff_mem_closure.mp (genericPoint_specializes y)
    have h2 : x ≤ genericPoint α := by
      rw [← Set.mem_Iic, ← closure_singleton_eq_Iic, genericPoint_closure]
      trivial
    exact le_trans h1 (hmax h2)
  -- Hence the closure of `x` is everything, i.e. `x` is a generic point of `α`; generic points of
  -- a `T₀` space are unique.
  have hgen : IsGenericPoint x Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    rw [specializes_iff_mem_closure, closure_singleton_eq_Iic, Set.mem_Iic]
    exact htop y
  exact hgen.eq (genericPoint_spec α)

/-- **A point of coheight zero in an irreducible scheme is the generic point.**  A scheme carries
the specialisation preorder by default (`AlgebraicGeometry.Scheme.le_iff_specializes`), is `T₀` and
quasi-sober, so the previous lemma applies verbatim. -/
theorem eq_genericPoint_of_coheight_eq_zero {X : AlgebraicGeometry.Scheme.{0}}
    [IrreducibleSpace X] (x : X) (h : Order.coheight x = 0) : x = genericPoint X :=
  eq_genericPoint_of_coheight_eq_zero_of_quasiSober x h

end Work.K3
