import Mathlib
import Submission.Work.Pi6.MSSK.Defs
import Submission.Work.SSSR.vertRestrPath
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- The monotone map `⦋1⦌ ⟶ ⦋t+1⦌` sending `0 ↦ t`, `1 ↦ t+1`: the **last edge** `{t, t+1}` of
`Δ[t+1]`. -/
def lastEdgeHom (t : ℕ) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk (t+1) :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨t + i.val, by have := i.isLt; omega⟩
      monotone' := fun a b hab => by simp only [Fin.le_def] at *; omega }

/-- The last edge `{t, t+1}` of `Δ[t+1]`, as a morphism of simplicial sets. -/
def lastEdge (t : ℕ) :
    (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
      (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) :=
  SSet.stdSimplex.map (lastEdgeHom t)

/-- The singular `1`-simplex of the last edge of `σ`. -/
def lastEdgeSimplex {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (Work.SSSR.sSing B) _⦋1⦌ :=
  SSet.yonedaEquiv (lastEdge t ≫ σ)

/-- The continuous map underlying the last-edge simplex, as a map `Δ¹ ⟶ B`. -/
def lastEdgeMap {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    C(↥(stdSimplex ℝ (Fin 2)), B) :=
  TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1))
    (lastEdgeSimplex t σ)

/-- The first vertex `Δ[0] ⟶ Δ[n]`. -/
def firstV (n : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶
    SSet.stdSimplex.obj (SimplexCategory.mk n) :=
  SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) 0)

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The part of `T_σ` over the *first* vertex, included in `T_σ` (the analogue of `fibreInc`). -/
def firstIncl (p : C(E, B)) {n : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) (firstV n ≫ σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ :=
  show pullback (firstV n ≫ σ) (Work.SSSR.sSingP p) ⟶ pullback σ (Work.SSSR.sSingP p) from
  pullback.lift (pullback.fst (firstV n ≫ σ) (Work.SSSR.sSingP p) ≫ firstV n)
    (pullback.snd (firstV n ≫ σ) (Work.SSSR.sSingP p))
    (by rw [Category.assoc]; exact pullback.condition)

/-- The inclusion of the part of `T_σ` over the last edge `{t, t+1}` into `T_σ`. -/
def edgeIncl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastEdge t ≫ σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ :=
  show pullback (lastEdge t ≫ σ) (Work.SSSR.sSingP p) ⟶ pullback σ (Work.SSSR.sSingP p) from
  pullback.lift (pullback.fst (lastEdge t ≫ σ) (Work.SSSR.sSingP p) ≫ lastEdge t)
    (pullback.snd (lastEdge t ≫ σ) (Work.SSSR.sSingP p))
    (by rw [Category.assoc]; exact pullback.condition)

/-- The inclusion of the part of the edge piece over the vertex `0` of `Δ[1]` (i.e. over the vertex
`t` of `Δ[t+1]`). -/
def vtx0Incl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) (firstV 1 ≫ lastEdge t ≫ σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastEdge t ≫ σ) :=
  firstIncl p (lastEdge t ≫ σ)

/-- The inclusion of the part of the edge piece over the vertex `1` of `Δ[1]` (i.e. over the vertex
`t+1` of `Δ[t+1]`). -/
def vtx1Incl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV 1 ≫ lastEdge t ≫ σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastEdge t ≫ σ) :=
  Work.Pi6.MSSK.fibreInc p (lastEdge t ≫ σ)

/-- The identification of the vertex piece `T_{σ'}` with the singular simplicial set of the fibre,
in the `pullAlong` spelling (the `pullAlong`-normalised form of
`Work.SSSR.pullAlongVertexIsoIso`). -/
noncomputable def vertexIso (p : C(E, B)) (σ' : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶
    Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ' ≅
      Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ')) :=
  Work.SSSR.pullAlongVertexIsoIso p σ'

/-- The degree-`K` chain map induced by `vertexIso`. -/
noncomputable def vertexIsoChain (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) (K : ℕ)
    (σ' : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ')).X K ⟶
      (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ')))).X K :=
  (Work.SSSR.sCCMap R (vertexIso p σ').hom).f K

/-- The homology class of a cycle of a chain complex. -/
noncomputable def chainClass (R : Type) [CommRing R] [Nontrivial R]
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : K.X n)
    (hz : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) z = 0) : K.homology n :=
  K.homologyπ n (K.cyclesMk z ((ComplexShape.down ℕ).next n) rfl hz)

end

end Work.Pi6.MSSK
