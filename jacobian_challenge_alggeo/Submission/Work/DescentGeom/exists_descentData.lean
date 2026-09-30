import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.DescentSetup
import Submission.Work.DescentGeom.localSpeiser
import Submission.Work.DescentGeom.isIso_phi_of_local
import Submission.Work.Descent.All
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.QuotientHom

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.DescentGeom

open CategoryTheory

open scoped CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

theorem exists_descentData {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] [FiniteDimensional k k'] (G' : Work.DescentGeom.Sch k')
    [AlgebraicGeometry.IsSeparated G'.hom]
    (galAct : Work.Descent.Gal k k' → (G'.left ≅ G'.left))
    (galAct_one : galAct 1 = Iso.refl G'.left)
    (galAct_mul : ∀ σ τ, galAct (σ * τ) = (galAct σ).trans (galAct τ))
    (hhom : ∀ σ, (galAct σ).hom ≫ G'.hom = G'.hom ≫ Work.DescentGeom.specGal σ)
    (hcover : ∀ x : G'.left, ∃ Ω : G'.left.Opens, AlgebraicGeometry.IsAffineOpen Ω ∧
      (∀ σ, (galAct σ).hom ⁻¹ᵁ Ω = Ω) ∧ x ∈ Ω) :
    ∃ (J : Work.DescentGeom.Sch k) (e : Work.DescentGeom.bc k' J ≅ G'),
      ∀ σ : Work.Descent.Gal k k',
        Work.Descent.galAct J σ ≫ e.hom.left = e.hom.left ≫ (galAct σ).hom := by
  let D : Work.DescentGeom.GalData k k' :=
    ⟨G', ‹AlgebraicGeometry.IsSeparated G'.hom›, galAct, galAct_one, galAct_mul, hhom, hcover⟩
  exact ⟨D.J, D.eInv (Work.DescentGeom.isIso_phi_of_local D
    (fun U => Work.DescentGeom.localSpeiser D U)), fun σ => D.eInv_galAct _ σ⟩

end Work.DescentGeom
