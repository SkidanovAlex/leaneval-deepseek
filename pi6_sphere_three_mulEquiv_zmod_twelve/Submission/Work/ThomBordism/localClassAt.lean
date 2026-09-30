import Mathlib
import Submission.Work.Cohomology.pd_good

/-!
# The local class of a homology class at a point

For a topological space `X`, a homology class `c ∈ H_n(X;ℤ)` and a point `x : X`, the **local class**
of `c` at `x` is the image of `c` in the relative homology `H_n(X, X ∖ {x};ℤ)` — the quotient of
`C_*(X)` by the chains supported away from `x`.  The class `c` is a *local generator* at `x` when
this image generates `H_n(X, X∖{x})`.

This is exactly the hypothesis under which the Poincaré–Lefschetz duality machinery of
`Submission/Work/Cohomology/` runs (`Work.Cohomology.Good`, `Work.Cohomology.pd_good_univ`), and it
is the form in which the fundamental classes of this workspace are recorded (`Man8.c_fund`,
`NullBordismFamily.w_fund`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

/-- **The local class at a point**: the image of `c ∈ H_n(X;ℤ)` in `H_n(X, X ∖ {x};ℤ)`. -/
def localClassAt (X : TopCat.{0}) (n : ℕ)
    (c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) (x : X) :
    (Work.Cohomology.relChains X {y : X | y ≠ x}).homology n :=
  (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X {y : X | y ≠ x})) n) c

/-- **`c` is a local generator at `x`**: its local class at `x` generates `H_n(X, X∖{x};ℤ)`. -/
def IsLocalGeneratorAt (X : TopCat.{0}) (n : ℕ)
    (c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) (x : X) : Prop :=
  Submodule.span ℤ {localClassAt X n c x} = ⊤

/-- **`c` is a local generator**: at every point of `X`.  This is the hypothesis `hc` of
`Work.Cohomology.pd_good_univ`, i.e. that `c` is a fundamental class. -/
def IsLocalGenerator (X : TopCat.{0}) (n : ℕ)
    (c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) : Prop :=
  ∀ x : X, IsLocalGeneratorAt X n c x

end

end Work.ThomBordism
