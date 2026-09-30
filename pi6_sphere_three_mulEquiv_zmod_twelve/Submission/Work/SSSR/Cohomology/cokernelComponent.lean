import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.relCohMVDefs
import Submission.Work.SSSR.Cohomology.relCapH
import Submission.Work.Cohomology.MVcapSquares
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace Work.SSSR.Cohomology

noncomputable section

/-- **The `n`-th component of the cokernel of a morphism of chain complexes is the cokernel of the
`n`-th component.** -/
def cokernelComponentIso {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (n : ℕ) :
    (cokernel f).X n ≅ cokernel (f.f n) := by
  let F : WalkingParallelPair ⥤ ModuleCat R := (parallelPair f 0) ⋙
    HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n
  let G : WalkingParallelPair ⥤ ModuleCat R := parallelPair (f.f n) 0
  have hFG : F = G := by
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · cases j <;> rfl
    · rintro X' Y' g
      match g with
      | .left => cat_disch
      | .right => cat_disch
      | .id Z => cat_disch
  exact IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)
        (colimit.isColimit (parallelPair f 0)))
      (colimit.isColimit F) ≪≫ HasColimit.isoOfNatIso (eqToIso hFG)

/-- **`cokernelComponentIso` is the canonical comparison**: composed with the projection
`cokernel.π f` it is the degreewise cokernel projection. -/
theorem cokernelComponentIso_canon {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (n : ℕ) :
    (cokernel.π f).f n ≫ (cokernelComponentIso f n).hom = cokernel.π (f.f n) := by
  simp only [cokernelComponentIso]
  have hs : ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair f 0))).ι.app WalkingParallelPair.one
      = (cokernel.π f).f n := rfl
  rw [← hs]
  rw [coconePointUniqueUpToIso_comp_isoOfNatIso_ι
    ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair f 0)))
    _ (eqToIso _) WalkingParallelPair.one]
  simp

variable {X : TopCat}

end

end Work.SSSR.Cohomology
