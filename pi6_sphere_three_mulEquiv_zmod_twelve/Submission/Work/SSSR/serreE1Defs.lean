import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.StemsB.SerreFiltration
import Submission.Work.SSSR.StemsB.Fibrations
import Submission.Work.SSSR.Cohomology.Chains
import Submission.Work.SSSR.SSetChain
import Submission.Work.SSSR.Filtration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- The singular simplicial set of a topological space. -/
abbrev sSing (X : Type) [TopologicalSpace X] : SSet.{0} := TopCat.toSSet.obj (TopCat.of X)

/-- The simplicial chain complex with `ℤ`-coefficients. -/
abbrev sCC (R : Type) [CommRing R] [Nontrivial R] (X : SSet.{0}) : ChainComplex (ModuleCat R) ℕ :=
  X.chainComplex (ModuleCat.of R R)

/-- The chain map induced by a morphism of simplicial sets. -/
abbrev sCCMap (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y) : sCC R X ⟶ sCC R Y :=
  ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map f

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
def pieceAlong (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    ChainComplex (ModuleCat R) ℕ :=
  cokernel (sCCMap R (bdryAlong f σ).ι)

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

end Work.SSSR
