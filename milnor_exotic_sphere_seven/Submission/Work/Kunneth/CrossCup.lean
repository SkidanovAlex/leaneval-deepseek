import Mathlib
import Submission.Work.Kunneth.Cross
import Submission.Work.Kunneth.crossCochain_apply
import Submission.Work.Kunneth.AWAux
import Submission.Work.Cohomology.Kunneth.ezEval
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cross product is the cup product of the pulled-back classes

For cochains `α` of `X` and `β` of `Y` of degrees `p` and `q`, the cross product
`Work.Kunneth.crossCochain X Y p q α β` of `Submission/Work/Kunneth/Cross.lean` is exactly the
cup product of the pullbacks of `α` and `β` along the two projections of `X ⊗ Y`:

  `α × β = π₁^* α ⌣ π₂^* β`.

This is the cochain-level form of the requested identity `a × b = π₁^* a ⌣ π₂^* b` for the cross
product on cohomology.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The cross product of cochains is the cup product of the pulled-back classes**:
`α × β = π₁^* α ⌣ π₂^* β`. -/
theorem crossCochain_eq_cup (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q) :
    crossCochain X Y p q α β
      = Work.Cohomology.cup ℤ (sProd X Y)
          (Work.Cohomology.Kunneth.ssetPullback (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p α)
          (Work.Cohomology.Kunneth.ssetPullback (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q β) := by
  have hop : backInclLE q (p + q) (by omega) = Work.Cohomology.backIncl p q := by
    refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    simp only [Work.Kunneth.hom_backInclLE_val, Work.Cohomology.hom_backIncl_val]
    omega
  apply Work.Cohomology.genEval_ext
  intro z
  rw [crossCochain_apply, Work.Cohomology.cup_apply]
  obtain ⟨a, b⟩ := z
  rw [Work.Cohomology.Kunneth.ssetPullback_genEval, Work.Cohomology.Kunneth.ssetPullback_genEval,
    Work.Cohomology.Kunneth.frontFace_prod_mk, Work.Cohomology.Kunneth.backFace_prod_mk,
    Work.Cohomology.Kunneth.fst_apply_prod, Work.Cohomology.Kunneth.snd_apply_prod]
  have hb : Work.Cohomology.backFace Y p q b =
      backFaceLE Y q (p + q) (by omega) b := by
    show Y.map (Work.Cohomology.backIncl p q).op b = Y.map (backInclLE q (p + q) (by omega)).op b
    rw [hop]
  rw [hb]

end

end Work.Kunneth
