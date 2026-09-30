import Mathlib
import Submission.Work.SSS.serreE1D1
import Submission.Work.SSS.serreE1Chain
import Submission.Work.SSS.serreE2Defs
import Submission.Work.SSS.serreE1Snd
import Submission.Work.SSS.ezSimplexZero_chain_class
import Submission.Work.SSS.iotaF_iota_comp_pieceIso
import Submission.Work.SSS.iotaTLin_boundary
import Submission.Work.SSS.sndToSerre_compat
import Submission.Work.SSS.sndToSerre_range
import Submission.Work.SSS.kF_eq_of_lift
import Submission.Work.SSS.tensorComplex_d_coef
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.IotaChain.basic

/-!
# The first differential of the Serre spectral sequence: the `d¹`-on-generators interface

Vocabulary for the computation of `d¹` on the generators `[σ] ⊗ m` of the first page
(`M = H_t(F)`), the last remaining input of `Work.SSS.serreE1`.  Fix `p : E → B` a Serre
fibration, `s t : ℕ`, a nondegenerate `(s+1)`-simplex `σ` of `Sing B` (with
`σ̂ = nIndexSigma Y (s+1) σ : Δ[s+1] ⟶ Sing B`, `b = σ̂(v₀)`), and a cycle chain `z` of `F_b`.

* `ezElem σ h z` is the Eilenberg–Zilber chain `EZ(std_s, z)` in `C(Δ[s] ⊗ Sing F_b)`;
* `faceRestr σ h i` is the restriction of the coherent lift `ezSimplex_σ` to the `i`-th face,
  a map `Δ[s] ⊗ Sing F_b ⟶ T_{δ i ≫ σ}` (Mathlib-style `faceLift` applied to `ezSimplex_σ`);
* `faceC σ h i` is the second projection `T_{δ i ≫ σ} ⟶ R_{s+1}` (`sndToSerre` at level `s+1`;
  the sharpened range bound `sndToSerre_range` shows the image of the face lands in `R_{s+1}`,
  one step *below* the `R_{s+2}` of `sndToR`);
* `faceB σ h z i` is the `i`-th face chain in `C(R_{s+1})`, the image of `ezElem` under
  `faceRestr ≫ faceC`;
* `faceSum σ h z = ∑_i (-1)^i • faceB σ h z i`.

The two main identities of the computation are `sndToR_iotaTLinFace` (the boundary of the lifted
chain `ι_σ z`, pushed to `C(R_{s+2})` by `sndToR`, is the alternating sum of the `incF`-images of
the `faceB`) and `mapPhiY_iotaF`.
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

/-- The canonical filtration of `C_*(E)`; its `F` is definitionally `Fc p`. -/
abbrev xiCan (p : C(E, B)) :
    Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)) :=
  serreFiltrationOf p

/-- The `(s+1)`-simplex `σ` of the base, as a map `Δ[s+1] ⟶ Sing B`. -/
abbrev sigHat {s : ℕ} (σ : nIndex (sSing B) (s + 1)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B :=
  nIndexSigma (sSing B) (s + 1) σ

/-- The chain complex of the `(s+1)`-st term of the Serre filtration, i.e. `(Fc p).obj s`. -/
abbrev serreCC (p : C(E, B)) (k : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  sCC (((Work.StemsB.serreSubcomplex (sSingP p) k : (sSing E).Subcomplex) : SSet))

/-- The Eilenberg–Zilber chain `EZ(std_s, z)` of the fundamental `s`-simplex of `Δ[s]` and a chain
`z` of the fibre `F_b`, as an element of `C(Δ[s] ⊗ Sing F_b)`. -/
def ezElem (p : C(E, B)) (s t : ℕ) (b : B) (z : (fibreCC p b).X t) :
    (sCC ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
      sSing (Work.StemsB.fibre p b))).X (s + t) :=
  ezLinSnd s t (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
    (sSing (Work.StemsB.fibre p b)) (stdIdSimplex s) z

/-- The restriction of the coherent lift `ezSimplex_σ` to its `i`-th face. -/
def faceRestr (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s + 2)) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
        sSing (Work.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) (SSet.stdSimplex.δ i ≫ σ) :=
  _root_.Work.SSS.faceLift (sSingP p) σ
    (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) (s + 1) b σ h)
    (ezSimplex_fst (liftFam p hfib) (liftFam_proj p hfib) (s + 1) b σ h) i

/-- The second projection of the `i`-th face of the pullback, at level `s+1`. -/
def faceC (p : C(E, B)) (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (i : Fin (s + 2)) :
    pullAlong (sSingP p) (SSet.stdSimplex.δ i ≫ σ) ⟶
      ((Work.StemsB.serreSubcomplex (sSingP p) (s + 1) : (sSing E).Subcomplex) : SSet) :=
  sndToSerre (sSingP p) (SSet.stdSimplex.δ i ≫ σ) (s + 1)
    ((sndToSerre_range (sSingP p)).1 (SSet.stdSimplex.δ i ≫ σ))

/-- The `i`-th face chain of the lifted Eilenberg–Zilber chain, in `C(R_{s+1})`. -/
def faceB (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (z : (fibreCC p b).X t) (i : Fin (s + 2)) :
    (serreCC p (s + 1)).X (s + t) :=
  (ModuleCat.Hom.hom ((sCCMap (faceRestr p hfib s b σ h i ≫ faceC p s σ i)).f (s + t)))
    (ezElem p s t b z)

/-- The alternating sum of the face chains: the lift of `∂(ι_σ z)` inside `C(R_{s+1})`. -/
def faceSum (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (z : (fibreCC p b).X t) :
    (serreCC p (s + 1)).X (s + t) :=
  ∑ i : Fin (s + 2), (-1 : ℤ) ^ (i : ℕ) • faceB p hfib s t b σ h z i

end

end Work.SSS
