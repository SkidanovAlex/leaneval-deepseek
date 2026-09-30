import Mathlib
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSSK.Defs
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.CapAux
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.Pi6.MSS.normalizedPullback
import Submission.Work.Pi6.MSS.essMapLeCardImage
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The mixed product formula at the `E_1` level** (chain-evaluation form).

For a Serre fibration `p : E → B` with simply connected base and coefficient field `𝕜`: for a
normalised `s`-cocycle `β` of the base, a `2`-cycle `y` of the zeroth column of `E_2`, a simplex
`σ : Δ[s] → Sing B` and a cycle `z` of the fibre over the first vertex of `σ`, the evaluation of the
cup product of `pbC β` with `y` on the Eilenberg–Zilber chain `iotaT` pushed to `E` is, up to a sign,
the value of `β` on `σ` times the Kronecker pairing of the restriction of `y` (to the fibre over
`p e₀`) with the transported fibre cycle.

This is the multiplicativity of the `E₁` identification of the Serre spectral sequence on the
"mixed" products of a base class with a fibre class.

Route (`REFS/NOTES_LEAD_MSSK.md` §2): `Work.Pi6.MSS.normalizedPullback` + `kronecker_cap_cup`
reduce the left hand side to `β(σ) • y(cap thetaTop c)`, `Work.Pi6.MSSK.capPieceTransport`
(capPieceTransport) rewrites `cap thetaTop c` as a cycle over the *last* vertex whose trivialised
class is the transported first-vertex class, and `Work.SSSR.iotaF_iota_comp_pieceIso` identifies the
piece class of `iotaF z` with `± [z]`.  The further input is the flatness of the restriction of a
`Z_2^0`-cochain to the fibres of `p`: evaluating on a fibre cycle is compatible with the canonical
transport `Work.SSSR.transportIsoPath` (equivalently with the trivialisation `Work.SSSR.triv`). -/
noncomputable def cruxChain (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) :
    (Work.SSSR.sCC 𝕜 (Work.SSS.sSing E)).X (s+q) :=
  ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f (s+q)).hom
    (((Work.SSSR.iotaT (R := 𝕜) p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
        s (Work.SSS.sigmaVert σ) σ rfl q).hom z))

noncomputable def cruxFibre (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (hz : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
      ((ComplexShape.down ℕ).next q) z = 0) :
    Work.SSSR.coefM (R := 𝕜) p e₀ q :=
  ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSS.sigmaVert σ) ≪≫
      (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm).hom.hom)
    ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).homologyπ q
      ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).cyclesMk z
        ((ComplexShape.down ℕ).next q) rfl hz))

variable (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

lemma genEval_thetaTop' (p : C(E, B)) (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    Work.Cohomology.genEval 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (Work.Pi6.MSSK.thetaTop 𝕜 p σ) w = Work.Pi6.MSSK.thetaVal 𝕜 p σ w :=
  Work.Pi6.MSSK.genEval_thetaTop 𝕜 p σ w

lemma genEval_pbC_SSSR (p : C(E, B)) {n : ℕ}
    (c : Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing B) n) (τ : (Work.SSSR.sSing E) _⦋n⦌) :
    Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p n c) τ
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) c ((Work.SSSR.sSingP p).app (op ⦋n⦌) τ) :=
  Work.Pi6.MSS.genEval_pbC 𝕜 p c τ

lemma sSingP_app_snd_eq (p : C(E, B)) (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    (Work.SSSR.sSingP p).app (op (SimplexCategory.mk s))
        ((pullback.snd σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) w)
      = ((pullback.fst σ (Work.SSSR.sSingP p) ≫ σ).app (op (SimplexCategory.mk s))) w :=
  (congrArg (fun (φ : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶ Work.SSSR.sSing B) =>
      (φ.app (op (SimplexCategory.mk s))) w)
    (pullback.condition (f := σ) (g := Work.SSSR.sSingP p))).symm

/-- The Eilenberg–Zilber chain `ι_σ z` in the pullback `T_σ`. -/
noncomputable def cruxIota (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) :
    (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + q) :=
  (Work.SSSR.iotaT (R := 𝕜) p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
    s (Work.SSS.sigmaVert σ) σ rfl q).hom z

/-- The cap chain `thetaTop ⌢ ι_σ z` pushed forward to `E`. -/
noncomputable def cruxCap (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) :
    (Work.SSSR.sCC 𝕜 (Work.SSSR.sSing E)).X q :=
  ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q).hom
    (Work.Cohomology.cap 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (Work.Pi6.MSSK.thetaTop 𝕜 p σ) q (cruxIota 𝕜 p hfib s q σ z))

/-- The chain over the last vertex of `σ` obtained from the cap lift `z'` by the vertex
identification `vertexIso`. -/
noncomputable def cruxU (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z' : (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).cycles q) :
    (Work.SSSR.sCC 𝕜 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
      (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))))).X q :=
  ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom).f q)
    ((ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).iCycles q)) z')

/-- The sign `(-1)^{s(s+1)/2}·(-1)^{s(s+1)/2}` of the mixed evaluation. -/
noncomputable def cruxEps (s : ℕ) : 𝕜 :=
  Work.Pi6.MSSK.capSign 𝕜 s * ((Work.SSSR.iotaSign s : ℤ) : 𝕜)

/-- The image of the Eilenberg–Zilber chain `cruxIota` in the `σ`-piece `C(T_σ)/C(∂T_σ)`. -/
noncomputable def cruxPiece (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) :
    (Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) σ).X (s + q) :=
  ((CategoryTheory.Limits.cokernel.π
      (Work.SSSR.sCCMap 𝕜 (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s + q)).hom
    (cruxIota 𝕜 p hfib s q σ z)

/-- The relative-cycle condition: the image of `cruxIota` in the `σ`-piece is a cycle. -/
def CruxRel (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) : Prop :=
  (Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) σ).d (s + q)
      ((ComplexShape.down ℕ).next (s + q)) (cruxPiece 𝕜 p hfib s q σ z) = 0

end Work.Pi6.MSS
