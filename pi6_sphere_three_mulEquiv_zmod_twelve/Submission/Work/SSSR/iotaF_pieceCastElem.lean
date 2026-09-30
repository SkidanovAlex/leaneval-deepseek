import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **Naturality of `Work.SSSR.iotaF` under an equality of simplices of the base.**  Transporting the
value of `iotaF` at `σ` along the object equality induced by `hσ : σ = σ'` (through
`Work.SSSR.pieceCastElem`, which is `eqToHom`) gives the value of `iotaF` at `σ'`.

Route: `subst hσ` (`cases hσ`) makes `σ' := σ` and `hσ := rfl`, so `pieceCastElem _ rfl` reduces by
`eqToHom_refl`, and `h` and `h'` are two proofs of the same proposition
`sigmaVert σ = b`, identified by proof irrelevance. -/
theorem iotaF_pieceCastElem {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (n q : ℕ) (b : B)
    (σ σ' : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (hσ : σ = σ')
    (h : Work.SSSR.sigmaVert σ = b) (h' : Work.SSSR.sigmaVert σ' = b)
    (z : (Work.SSSR.fibreCC (R := R) p b).X q) :
    Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hσ
        ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) n b σ h q)) z)
      = (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) n b σ' h' q)) z := by
  subst hσ
  rw [Subsingleton.elim h h']
  simp only [pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

end Work.SSSR
