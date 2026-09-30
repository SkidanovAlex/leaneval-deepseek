import Mathlib
import Submission.Work.SSSR.serreE1D1
import Submission.Work.SSSR.serreE1Chain
import Submission.Work.SSSR.serreE2Defs
import Submission.Work.SSSR.serreE1Snd
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.SSSR.iotaF_iota_comp_pieceIso
import Submission.Work.SSSR.iotaTLin_boundary
import Submission.Work.SSSR.sndToSerre_compat
import Submission.Work.SSSR.sndToSerre_range
import Submission.Work.SSSR.kF_eq_of_lift
import Submission.Work.SSSR.tensorComplex_d_coef
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.IotaChain.basic
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

/-- The canonical filtration of `C_*(E)`; its `F` is definitionally `Fc p`. -/
abbrev xiCan (p : C(E, B)) :
    Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)) :=
  serreFiltrationOf p

/-- The `(s+1)`-simplex `σ` of the base, as a map `Δ[s+1] ⟶ Sing B`. -/
abbrev sigHat {s : ℕ} (σ : nIndex (sSing B) (s + 1)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B :=
  nIndexSigma (sSing B) (s + 1) σ

/-- The chain complex of the `(s+1)`-st term of the Serre filtration, i.e. `(Fc p).obj s`. -/
abbrev serreCC (p : C(E, B)) (k : ℕ) : ChainComplex (ModuleCat R) ℕ :=
  sCC R (((Work.SSSR.StemsB.serreSubcomplex (sSingP p) k : (sSing E).Subcomplex) : SSet))

/-- The Eilenberg–Zilber chain `EZ(std_s, z)` of the fundamental `s`-simplex of `Δ[s]` and a chain
`z` of the fibre `F_b`, as an element of `C(Δ[s] ⊗ Sing F_b)`. -/
def ezElem (p : C(E, B)) (s t : ℕ) (b : B) (z : (fibreCC (R := R) p b).X t) :
    (sCC R ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
      sSing (Work.SSSR.StemsB.fibre p b))).X (s + t) :=
  ezLinSnd s t (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
    (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex s) z

/-- The restriction of the coherent lift `ezSimplex_σ` to its `i`-th face. -/
def faceRestr (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s + 2)) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
        sSing (Work.SSSR.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) (SSet.stdSimplex.δ i ≫ σ) :=
  _root_.Work.SSSR.faceLift (sSingP p) σ
    (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) (s + 1) b σ h)
    (ezSimplex_fst (liftFam p hfib) (liftFam_proj p hfib) (s + 1) b σ h) i

/-- The second projection of the `i`-th face of the pullback, at level `s+1`. -/
def faceC (p : C(E, B)) (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (i : Fin (s + 2)) :
    pullAlong (sSingP p) (SSet.stdSimplex.δ i ≫ σ) ⟶
      ((Work.SSSR.StemsB.serreSubcomplex (sSingP p) (s + 1) : (sSing E).Subcomplex) : SSet) :=
  sndToSerre (sSingP p) (SSet.stdSimplex.δ i ≫ σ) (s + 1)
    ((sndToSerre_range (sSingP p)).1 (SSet.stdSimplex.δ i ≫ σ))

/-- The `i`-th face chain of the lifted Eilenberg–Zilber chain, in `C(R_{s+1})`. -/
def faceB (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (z : (fibreCC (R := R) p b).X t) (i : Fin (s + 2)) :
    (serreCC (R := R) p (s + 1)).X (s + t) :=
  (ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b σ h i ≫ faceC p s σ i)).f (s + t)))
    (ezElem p s t b z)

/-- The alternating sum of the face chains: the lift of `∂(ι_σ z)` inside `C(R_{s+1})`. -/
def faceSum (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (z : (fibreCC (R := R) p b).X t) :
    (serreCC (R := R) p (s + 1)).X (s + t) :=
  ∑ i : Fin (s + 2), (-1 : ℤ) ^ (i : ℕ) • faceB p hfib s t b σ h z i

end

end Work.SSSR
