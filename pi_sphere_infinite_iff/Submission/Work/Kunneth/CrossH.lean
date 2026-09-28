import Mathlib
import Submission.Work.Kunneth.CrossCup
import Submission.Work.Kunneth.crossCochain_isCocycle
import Submission.Work.Cohomology.DualComplexMap

/-!
# The cross product on cohomology

`Work.Kunneth.pullbackH` is the pullback of cohomology classes along a simplicial map, and
`Work.Kunneth.crossH` is the **cross product** of cohomology classes,
`a × b = π₁^* a ⌣ π₂^* b`.

**Note.**  This file re-registers the generic `ℤ`-module structure
(`attribute [instance 5000] AddCommGroup.toIntModule`), which the other files of the chapter
remove (see `README.md` §3): the pullback of cohomology is a statement about `ModuleCat`
homology modules alone, with no tensor product in sight, and the generic structure is what makes
the `ℤ`-linear structure on `M →ₗ[ℤ] N` synthesise here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [local instance 5000] AddCommGroup.toIntModule

/-- **Pullback of cohomology classes** `H^n(Y;ℤ) → H^n(X;ℤ)` along `f : X ⟶ Y`. -/
noncomputable def pullbackH (X Y : SSet) (f : X ⟶ Y) (n : ℕ) :=
  (HomologicalComplex.homologyMap
    (Work.Cohomology.dualComplexMap ℤ (sChain X) (sChain Y) (SSet.chainComplexMap f zz)) n).hom

/-- **The cross product on cohomology**, `a × b = π₁^* a ⌣ π₂^* b`. -/
noncomputable def crossH (X Y : SSet) (p q : ℕ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    ↑((Work.Cohomology.cochainC ℤ (sProd X Y)).homology (p + q)) :=
  Work.Cohomology.cupH' ℤ (sProd X Y) p q
    (pullbackH (sProd X Y) X (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p a)
    (pullbackH (sProd X Y) Y (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q b)

/-- **The defining identity of the cross product on cohomology**:
`a × b = π₁^* a ⌣ π₂^* b`. -/
theorem crossH_apply (X Y : SSet) (p q : ℕ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossH X Y p q a b
      = Work.Cohomology.cupH' ℤ (sProd X Y) p q
          (pullbackH (sProd X Y) X (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p a)
          (pullbackH (sProd X Y) Y (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q b) :=
  rfl

end

end Work.Kunneth
