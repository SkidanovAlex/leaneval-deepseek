import Mathlib
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.SSSR.homology_sigmaExplicit
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.serreE1CoefExplicit
import Submission.Work.SSSR.transportIsoPath_homotopic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `mapPhi R f d` as an isomorphism, with inverse `mapPsi R f d`. -/
def mapPhiIso {X Y : SSet.{0}} (f : X ⟶ Y) (d : ℕ) :
    (∐ fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) ≅ grF (serF R f) d where
  hom := mapPhi R f d
  inv := mapPsi R f d
  hom_inv_id := mapPhi_comp_mapPsi f d
  inv_hom_id := mapPsi_comp_mapPhi f d

/-- The `σ`-summand coefficient isomorphism: the homology of the σ-piece in degree `s + t` is the
homology of the fibre over the first vertex of `σ`, trivialised by `Work.SSSR.triv`. -/
noncomputable def PsiCoef (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t s : ℕ) (σ : nIndex (sSing B) s) :
    coefM p e₀ t ≅ (pieceAlong R (sSingP p) (nIndexSigma (sSing B) s σ)).homology (s + t) :=
  (triv p e₀ hfib hc t (sigmaVert (nIndexSigma (sSing B) s σ))).symm ≪≫
    (serreE1PieceIso p hfib s t (nIndexSigma (sSing B) s σ)).symm

end

end Work.SSSR
