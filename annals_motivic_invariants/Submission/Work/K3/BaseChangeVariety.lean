import Mathlib
import Submission.Work.K3.BaseChange
import Submission.Work.K3.baseChange_comp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.BaseChangeVariety` — varieties base change along a field extension

The descent step of `thm:K3` produces the `𝕜`-model of the link from its `ℚ`-model by base change.
For that, the *constituents* of the model (`S`, `S'`, the fourfold `P`) must be `𝕜`-varieties: this
file shows that the base change of a `ℚ`-variety is a `𝕜`-variety, provided its structure morphism
is geometrically integral (the geometric content of "`S`, `S'` are K3 surfaces over `ℚ`, `P` is a
model of `ℙ⁴`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Base change of a variety is a variety** (along a field extension), for a geometrically
integral structure morphism.  The three remaining components of the `Variety` structure are the
base-change instances for `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. -/
def variety_baseChange (K L : Type) [Field K] [Field L] [Algebra K L] (X : Scheme.{0})
    [hvar : Variety K X] [GeometricallyIntegral (X ↘ Spec (.of K))] :
    Variety L (baseChange K L X) :=
  { «over» := baseChangeOver K L X
    isIntegral := isIntegral_baseChange K L X
    isSeparated := by
      haveI : IsSeparated (X ↘ Spec (.of K)) := hvar.isSeparated
      show IsSeparated (pullback.fst (specMap K L) (X ↘ Spec (.of K)))
      infer_instance
    locallyOfFiniteType := by
      haveI : LocallyOfFiniteType (X ↘ Spec (.of K)) := hvar.locallyOfFiniteType
      show LocallyOfFiniteType (pullback.fst (specMap K L) (X ↘ Spec (.of K)))
      infer_instance
    quasicompact := by
      haveI : QuasiCompact (X ↘ Spec (.of K)) := hvar.quasicompact
      show QuasiCompact (pullback.fst (specMap K L) (X ↘ Spec (.of K)))
      infer_instance }

/-- The base change of a geometrically integral variety is integral. -/
theorem isIntegral_baseChange' (K L : Type) [Field K] [Field L] [Algebra K L] (X : Scheme.{0})
    [Variety K X] [GeometricallyIntegral (X ↘ Spec (.of K))] : IsIntegral (baseChange K L X) :=
  isIntegral_baseChange K L X

/-- The base change of a geometrically integral variety is irreducible. -/
theorem irreducibleSpace_baseChange (K L : Type) [Field K] [Field L] [Algebra K L]
    (X : Scheme.{0}) [Variety K X] [GeometricallyIntegral (X ↘ Spec (.of K))] :
    IrreducibleSpace (baseChange K L X) := by
  haveI := isIntegral_baseChange K L X
  infer_instance

/- The three facts above are deliberately *not* registered as global instances: instance search for
`Variety L (baseChange K L X)` would then have to unify the goal with the head `baseChange K L X` of
the instance, which requires unfolding the definition of `baseChange` and, with it, synthesizing an
`Over (Spec K)` instance for an unsolved metavariable -- a loop.  They are used explicitly (or as
*local* instances, whose type is syntactically the goal). -/

end

end Work.K3
