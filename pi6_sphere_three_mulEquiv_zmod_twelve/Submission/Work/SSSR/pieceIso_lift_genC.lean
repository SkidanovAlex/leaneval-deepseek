import Mathlib
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.serreE1StepAux
import Submission.Work.SSSR.ezSimplexZero_aux
import Submission.Work.SSSR.hornCok_d_faceLift
import Submission.Work.SSSR.pieceIso_peel
import Submission.Work.SSSR.pieceIso_lift_zero
import Submission.Work.SSSR.sigmaVert_face
import Submission.Work.SSSR.sSingP_fibreIncl_comp
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Elementary transport lemmas -/

/-- `eqToHom`-naturality of the singular simplicial set of the fibres (local copy of
`Work.SSSR.eqToHom_sSingP_fibreIncl`, to avoid importing `piszTower`). -/
lemma eqToHom_sSingP_fibreIncl' (p : C(E, B)) {x y : B} (h : x = y) :
    eqToHom (congrArg (fun z : B => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) h)
        ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p y)
      = Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p x) := by
  cases h
  rw [eqToHom_refl, Category.id_comp]

/-- The differential of a chain map, elementwise. -/
lemma chainMap_d_apply' {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i j : ℕ) (x : K.X i) :
    (L.d i j) ((φ.f i) x) = (φ.f j) ((K.d i j) x) := by
  have h := congrArg (fun (g : K.X i ⟶ L.X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm φ i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **The transport of a fibre-homology class along a base-point equality**, for the map induced by
a lift composed with the transport. -/
lemma fibreConj_homologyπ_v_face {p : C(E, B)} {b : B} {t : ℕ} {x' x : B} (h : x' = x)
    (v : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) ⟶ Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x))
    (gen : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).X t)
    (h1 : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x'))).d t ((ComplexShape.down ℕ).next t)
        ((Work.SSSR.sCCMap R (v ≫ eqToHom (congrArg (fun z : B => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) h.symm))).f t gen) = 0)
    (h2 : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x))).d t ((ComplexShape.down ℕ).next t)
        ((Work.SSSR.sCCMap R v).f t gen) = 0) :
    (Work.SSSR.fibreConj p h t)
      ((HomologicalComplex.homologyπ (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x'))) t)
        (HomologicalComplex.cyclesMk (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x')))
          ((Work.SSSR.sCCMap R (v ≫ eqToHom (congrArg (fun z : B => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) h.symm))).f t gen)
          ((ComplexShape.down ℕ).next t) rfl h1))
    = (HomologicalComplex.homologyπ (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x))) t)
        (HomologicalComplex.cyclesMk (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x)))
          ((Work.SSSR.sCCMap R v).f t gen) ((ComplexShape.down ℕ).next t) rfl h2) := by
  subst h
  simp only [eqToHom_refl, Work.SSSR.fibreConj_rfl, ModuleCat.hom_id, LinearMap.id_apply]
  congr 1

end Work.SSSR
