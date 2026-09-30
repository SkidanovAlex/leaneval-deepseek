import Mathlib
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.serreE1Assembly
import Submission.Work.SSS.homology_sigmaExplicit
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.serreE1CoefExplicit
import Submission.Work.SSS.transportIsoPath_homotopic

/-!
# The comparison chain map `Ψ : N_*(B) ⊗ H_t(F) ⟶ E¹` of the Serre filtration

`Work.SSS.serreE1` asserts `Nonempty (E1Complex ξ t ≅ tensorComplex (Nn B) (coefM p e₀ t))`.
The degreewise isomorphism `thetaD` of `Submission/Work/SSS/serreE1Assembly.lean` is assembled from
`Classical.choice`d `Nonempty`-valued statements and is therefore *opaque*: no statement about its
behaviour on differentials can be derived from its type.  This file replaces it by the explicit
chain map `PsiCmp` (built from the transparent isomorphisms `serreE1CoefIsoIso`, `serreE1PieceIso`,
`triv`, `homology_sigmaIso` and `mapPhi`), whose chain-map property is proved (elsewhere) from the
Eilenberg–Zilber boundary formula and the fibre transport along the edges.

`Psi_s` is by construction an isomorphism of `ℤ`-modules for every `s` (`isIso_PsiCmp`): all its
factors are isomorphisms.  The remaining obligation for `Work.SSS.serreE1` is that `PsiCmp` commutes
with the differentials, i.e. `Psi_{s+1} ≫ d¹ = ∂ ⊗ id ≫ Psi_s`; see
`REFS/NOTES_LEAD_SSS_d1.md` §1.2–1.3.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `mapPhi f d` as an isomorphism, with inverse `mapPsi f d`. -/
def mapPhiIso {X Y : SSet.{0}} (f : X ⟶ Y) (d : ℕ) :
    (∐ fun y : nIndex Y d => pieceAlong f (nIndexSigma Y d y)) ≅ grF (serF f) d where
  hom := mapPhi f d
  inv := mapPsi f d
  hom_inv_id := mapPhi_comp_mapPsi f d
  inv_hom_id := mapPsi_comp_mapPhi f d

/-- The `σ`-summand coefficient isomorphism: the homology of the σ-piece in degree `s + t` is the
homology of the fibre over the first vertex of `σ`, trivialised by `Work.SSS.triv`. -/
noncomputable def PsiCoef (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t s : ℕ) (σ : nIndex (sSing B) s) :
    coefM p e₀ t ≅ (pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)).homology (s + t) :=
  (triv p e₀ hfib hc t (sigmaVert (nIndexSigma (sSing B) s σ))).symm ≪≫
    (serreE1PieceIso p hfib s t (nIndexSigma (sSing B) s σ)).symm

/-- **The comparison isomorphism `Ψ_s` of the first page of the Serre spectral sequence.** -/
noncomputable def PsiCmpIso (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    (tensorComplex (Nn B) (coefM p e₀ t)).X s ≅ (E1Complex ξ t).X s :=
  (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).symm ≪≫
  (Sigma.mapIso (fun σ : nIndex (sSing B) s => PsiCoef p e₀ hfib hc t s σ)) ≪≫
  (homology_sigmaIso (fun σ : nIndex (sSing B) s =>
      pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) (s + t)).symm ≪≫
  (HomologicalComplex.homologyMapIso (mapPhiIso (sSingP p) s) (s + t)) ≪≫
  (eqToIso (show (grF (serF (sSingP p)) s).homology (s + t) = (E1Complex ξ t).X s by
    show (grF (serF (sSingP p)) s).homology (s + t) = (grF ξ.F s).homology (s + t)
    rw [hξ]))

/-- The comparison isomorphism `Ψ_s`, as a morphism of `ℤ`-modules. -/
noncomputable def PsiCmp (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    (tensorComplex (Nn B) (coefM p e₀ t)).X s ⟶ (E1Complex ξ t).X s :=
  (PsiCmpIso p e₀ hfib hc t ξ hξ s).hom

/-- `Ψ_s` is an isomorphism (all its factors are). -/
theorem isIso_PsiCmp (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    IsIso (PsiCmp p e₀ hfib hc t ξ hξ s) := by
  rw [PsiCmp]
  infer_instance

end

end Work.SSS
