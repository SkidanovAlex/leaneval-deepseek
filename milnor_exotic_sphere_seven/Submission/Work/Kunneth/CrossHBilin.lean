import Mathlib
import Submission.Work.Kunneth.CrossH
import Submission.Work.Kunneth.crossH_bilinear

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cross product on cohomology as a bilinear map

`Work.Kunneth.crossHLin X Y p q : Hᵖ(X;ℤ) →ₗ[ℤ] H^q(Y;ℤ) →ₗ[ℤ] H^{p+q}(X ⊗ Y;ℤ)` is the
cross product of `Submission/Work/Kunneth/CrossH.lean` packaged as a (curried) bilinear map; the
companion lemma `Work.Kunneth.crossH_bilinear` supplies the linearity.  By
`Work.Kunneth.crossH_apply` it is `a × b = π₁^* a ⌣ π₂^* b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [local instance 5000] AddCommGroup.toIntModule

/-- **The cross product on cohomology, as a bilinear map**:
`Hᵖ(X;ℤ) →ₗ H^q(Y;ℤ) →ₗ H^{p+q}(X ⊗ Y;ℤ)`. -/
noncomputable def crossHLin (X Y : SSet) (p q : ℕ) :
    ↑((Work.Cohomology.cochainC ℤ X).homology p) →ₗ[ℤ]
      ↑((Work.Cohomology.cochainC ℤ Y).homology q) →ₗ[ℤ]
        ↑((Work.Cohomology.cochainC ℤ (sProd X Y)).homology (p + q)) :=
  Classical.choose (crossH_bilinear X Y p q)

/-- The computation rule for `crossHLin`: it agrees with `crossH`, hence is `π₁^* a ⌣ π₂^* b`. -/
theorem crossHLin_apply (X Y : SSet) (p q : ℕ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossHLin X Y p q a b = crossH X Y p q a b :=
  Classical.choose_spec (crossH_bilinear X Y p q) a b

/-- **The cross product is the cup product of the pulled-back classes**:
`a × b = π₁^* a ⌣ π₂^* b`. -/
theorem crossHLin_apply_eq_cup (X Y : SSet) (p q : ℕ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossHLin X Y p q a b
      = Work.Cohomology.cupH' ℤ (sProd X Y) p q
          (pullbackH (sProd X Y) X (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p a)
          (pullbackH (sProd X Y) Y (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q b) := by
  rw [crossHLin_apply, crossH_apply]

end

end Work.Kunneth
