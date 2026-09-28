import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.StemsB.SerreFiltration
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.Chains
import Submission.Work.SSS.SSetChain
import Submission.Work.SSS.Filtration

/-!
# The pieces of the first page of the Serre spectral sequence

Vocabulary for `Work.SSS.serreE1`.  For a morphism of simplicial sets `f : X ⟶ Y` and a simplex
`σ : Δ[s] ⟶ Y` of the target, the *σ-piece* is the relative chain complex

  `pieceAlong f σ = C(T_σ)/C(∂T_σ)`,

where `T_σ = Δ[s] ×_Y X` is the pullback of `f` along `σ` and `∂T_σ ⊆ T_σ` is the preimage of
`∂Δ[s]`.

The graded piece `grF (natShift ⋙ serreChainFiltration f ℤ) d = C(F_d)/C(F_{d-1})` of the Serre
filtration is the direct sum of the σ-pieces over the nondegenerate `d`-simplices of `Y`
(`serreE1Graded`), and for `X = Sing E`, `Y = Sing B`, `f = Sing p` with `p` a Serre fibration, the
homology of the σ-piece in degree `s + k` is the homology of the fibre over `σ(v₀)` in degree `k`
(`serreE1Piece`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-- The singular simplicial set of a topological space. -/
abbrev sSing (X : Type) [TopologicalSpace X] : SSet.{0} := TopCat.toSSet.obj (TopCat.of X)

/-- The simplicial chain complex with `ℤ`-coefficients. -/
abbrev sCC (X : SSet.{0}) : ChainComplex (ModuleCat ℤ) ℕ :=
  X.chainComplex (ModuleCat.of ℤ ℤ)

/-- The chain map induced by a morphism of simplicial sets. -/
abbrev sCCMap {X Y : SSet.{0}} (f : X ⟶ Y) : sCC X ⟶ sCC Y :=
  ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f

/-- The map of singular simplicial sets induced by a continuous map. -/
def sSingP {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    sSing E ⟶ sSing B :=
  TopCat.toSSet.map (TopCat.ofHom p)

/-- The pullback `T_σ = Δ[s] ×_Y X` of a simplicial map along a simplex of its target. -/
def pullAlong {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) : SSet.{0} :=
  pullback σ f

/-- The boundary subcomplex `∂T_σ ⊆ T_σ`: the preimage of `∂Δ[s]`. -/
def bdryAlong {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    (pullAlong f σ).Subcomplex :=
  (SSet.boundary s).preimage (pullback.fst σ f)

/-- The σ-piece `C(T_σ)/C(∂T_σ)`. -/
def pieceAlong {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (sCCMap (bdryAlong f σ).ι)

/-- The nondegenerate `d`-simplices of a simplicial set, as an index type. -/
abbrev nIndex (Y : SSet.{0}) (d : ℕ) : Type := {y : Y.N // y.dim = d}

/-- The simplex `Δ[d] ⟶ Y` attached to a nondegenerate `d`-simplex. -/
def nIndexSigma (Y : SSet.{0}) (d : ℕ) (y : nIndex Y d) :
    (SSet.stdSimplex.obj (SimplexCategory.mk d) : SSet.{0}) ⟶ Y :=
  SSet.yonedaEquiv.symm (y.1.toS.cast y.2).simplex

/-- The point of `B` underlying a simplex `σ : Δ[s] ⟶ Sing B` (its `0`-th vertex). -/
def sigmaVert {B : Type} [TopologicalSpace B] {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ sSing B) : B :=
  ((TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk s)))
      (SSet.yonedaEquiv σ))
    ⟨Pi.single (0 : Fin (s+1)) 1, single_mem_stdSimplex ℝ (0 : Fin (s+1))⟩

end

end Work.SSS
