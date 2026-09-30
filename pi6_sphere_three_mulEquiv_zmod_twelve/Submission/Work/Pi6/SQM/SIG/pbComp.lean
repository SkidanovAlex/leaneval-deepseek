import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `pbComp` — contravariant functoriality of the cochain pullback

`Work.Pi6.SQM.SIG.pb f u` is the pullback of the cochain `u` along a map of simplicial sets `f`
(equivalently, the pullback along the geometric realisation, by `pb_continuous`).  This file shows
that it is contravariantly functorial: `pb (f ≫ g) = pb g ∘ pb f` on cochains, which is
`LinearMap.dualMap_comp_dualMap` applied to `chainComplexMap_comp_f`.

The degreewise functoriality of `SSet.chainComplexMap` is not in Mathlib (it is
`Work.Cohomology.chainComplexMap_comp_f`, reproduced here for the coefficient object `𝔽₂`), so we
prove the needed instance locally with the standard cofan argument.
-/

open CategoryTheory
open scoped CategoryTheory Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- **Functoriality of the simplicial chain complex, degreewise (coefficients `𝔽₂`).** -/
theorem chainComplexMap_comp_f_F2 {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (SSet.chainComplexMap (f ≫ g) (ModuleCat.of F2 F2)).f n =
      (SSet.chainComplexMap f (ModuleCat.of F2 F2)).f n ≫
        (SSet.chainComplexMap g (ModuleCat.of F2 F2)).f n := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [SSet.ι_chainComplexMap_f, ← Category.assoc, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f]
  rfl

/-- Contravariant functoriality of `pb`.  The composition of the underlying chain maps is
`MVcapSquares.chainComplexMap_comp_f`, and `LinearMap.dualMap_comp_dualMap` reverses it. -/
theorem pbComp {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (u : Work.Cohomology.Cochain Work.Pi6.SQ.F2 Z n) :
    Work.Pi6.SQM.SIG.pb (CategoryTheory.CategoryStruct.comp f g) u =
      Work.Pi6.SQM.SIG.pb f (Work.Pi6.SQM.SIG.pb g u) := by
  unfold Work.Pi6.SQM.SIG.pb
  rw [chainComplexMap_comp_f_F2 f g n]
  simp only [ModuleCat.hom_comp]
  rw [← LinearMap.dualMap_comp_dualMap]
  rfl

end

end Work.Pi6.SQM.SIG
