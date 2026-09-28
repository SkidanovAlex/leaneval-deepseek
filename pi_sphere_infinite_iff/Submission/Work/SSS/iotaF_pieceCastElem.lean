import Mathlib
import Submission.Work.SSS.serreE1CruxD1

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **Naturality of `Work.SSS.iotaF` under an equality of simplices of the base.**  Transporting the
value of `iotaF` at `σ` along the object equality induced by `hσ : σ = σ'` (through
`Work.SSS.pieceCastElem`, which is `eqToHom`) gives the value of `iotaF` at `σ'`.

Route: `subst hσ` (`cases hσ`) makes `σ' := σ` and `hσ := rfl`, so `pieceCastElem _ rfl` reduces by
`eqToHom_refl`, and `h` and `h'` are two proofs of the same proposition
`sigmaVert σ = b`, identified by proof irrelevance. -/
theorem iotaF_pieceCastElem {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ) (b : B)
    (σ σ' : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (hσ : σ = σ')
    (h : Work.SSS.sigmaVert σ = b) (h' : Work.SSS.sigmaVert σ' = b)
    (z : (Work.SSS.fibreCC p b).X q) :
    Work.SSS.pieceCastElem (Work.SSS.sSingP p) hσ
        ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) n b σ h q)) z)
      = (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) n b σ' h' q)) z := by
  subst hσ
  rw [Subsingleton.elim h h']
  simp only [pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

end Work.SSS
