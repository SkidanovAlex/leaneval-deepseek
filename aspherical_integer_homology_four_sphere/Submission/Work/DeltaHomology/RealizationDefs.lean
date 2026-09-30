import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Realizations of `Δ`-complexes

A *realization* of a finite `Δ`-complex `K` in a topological space `X` is the
data making `X` the quotient of the disjoint union of its simplices:

* `DeltaSimplexMap K X` carries the characteristic maps
  `χ : ∀ k, Fin (K.card k) → C(Δ^k, X)` (stored as the corresponding simplices of
  Mathlib's singular simplicial set `TopCat.toSSet.obj X`, so that the singular
  chain API applies directly), compatible with faces
  (`χ (face σ i) = χ σ ∘ δ_i`);
* `DeltaRealization K X` adds the point-set conditions: `X` is compact Hausdorff,
  every point of `X` lies in *exactly one* open simplex (the interiors of the
  `χ σ`), and `X` carries the weak (quotient) topology determined by the closed
  simplices, i.e. a set is open iff its preimage under every `χ σ` is open.

The open `k`-simplex is the set of `StdSimplex ℝ (Fin (k+1))` whose barycentric
weights are all strictly positive; `OpenSimplex K` is the type of pairs
`(k, σ, w)` with `w` an open point of `Δ^k`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity
open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

/-- The open `k`-simplex: the points of the standard simplex all of whose
barycentric weights are strictly positive. -/
def IsOpenSimplexPoint (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) : Prop :=
  ∀ i, 0 < w.weights i

/-- The boundary of the standard `k`-simplex: the points with at least one zero
barycentric weight. -/
def StdSimplexBoundary (k : ℕ) : Set (StdSimplex ℝ (Fin (k + 1))) :=
  {w | ∃ i, w.weights i = 0}

/-- An open simplex of a `Δ`-complex: a dimension `k`, a `k`-simplex `σ` of `K`,
and an interior point of the standard `k`-simplex. -/
structure OpenSimplex (K : DeltaCx) where
  /-- The dimension. -/
  dim : ℕ
  /-- The simplex. -/
  idx : Fin (K.card dim)
  /-- The interior point of the standard simplex. -/
  pt : StdSimplex ℝ (Fin (dim + 1))
  /-- The point is in the interior (all weights strictly positive). -/
  pos : IsOpenSimplexPoint dim pt

/-- The face `δ_i` of a singular simplex of `X`, as a function on the simplices
of the singular simplicial set. -/
def singFace {X : TopCat} {k : ℕ} (i : Fin (k + 2))
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (k + 1)))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k)) :=
  ConcreteCategory.hom (SimplicialObject.δ (TopCat.toSSet.obj X) i) x

/-- The image of a singular simplex of `X` under a continuous map `g : X ⟶ Y`,
as a function on the simplices of the singular simplicial sets. -/
def singMap {X Y : TopCat} (g : X ⟶ Y) {k : ℕ}
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))) :
    (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk k)) :=
  ConcreteCategory.hom ((TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk k))) x

/-- The characteristic maps of a `Δ`-complex in a topological space: for each
`k`-simplex `σ` a singular `k`-simplex `χ σ` of `X`, compatible with faces. -/
structure DeltaSimplexMap (K : DeltaCx) (X : TopCat) where
  /-- The characteristic map of each simplex, as a singular simplex of `X`. -/
  χ : ∀ k : ℕ, Fin (K.card k) → (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))
  /-- Face compatibility: `χ (face σ i) = χ σ ∘ δ_i`. -/
  face_compat : ∀ {k : ℕ} (σ : Fin (K.card (k + 1))) (i : Fin (k + 2)),
    χ k (K.face σ i) = singFace i (χ (k + 1) σ)

namespace DeltaSimplexMap

variable {K : DeltaCx} {X : TopCat}

/-- The characteristic map of the `k`-simplex `σ` as a continuous map
`Δ^k → X`. -/
def cls (χ : DeltaSimplexMap K X) (k : ℕ) (σ : Fin (K.card k)) :
    C(StdSimplex ℝ (Fin (k + 1)), X) :=
  TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk k)) (χ.χ k σ)

@[simp]
theorem cls_apply (χ : DeltaSimplexMap K X) (k : ℕ) (σ : Fin (K.card k))
    (w : StdSimplex ℝ (Fin (k + 1))) : χ.cls k σ w = χ.cls k σ w := rfl

/-- The point of `X` determined by an open simplex. -/
def real (χ : DeltaSimplexMap K X) (p : OpenSimplex K) : X :=
  χ.cls p.dim p.idx p.pt

/-- The degree-`k` component of the chain map from the `Δ`-chains of `K` to the
singular chains of `X`: the basis simplex `σ` is sent to the singular simplex
`χ σ`. -/
def deltaChainMapFun (χ : DeltaSimplexMap K X) (k : ℕ) :
    K.chainX k ⟶ (singChain Work.Homology.ZMod X).X k :=
  Sigma.desc (fun σ : Fin (K.card k) =>
    SSet.ιChainComplex (TopCat.toSSet.obj X) (χ.χ k σ))

/-- The degree-`k` component of the chain map on a basis simplex. -/
theorem deltaChainMapFun_chainι (χ : DeltaSimplexMap K X) (k : ℕ) (σ : Fin (K.card k)) :
    K.chainι k σ ≫ χ.deltaChainMapFun k
      = SSet.ιChainComplex (TopCat.toSSet.obj X) (χ.χ k σ) :=
  Limits.Sigma.ι_comp_desc _ σ

end DeltaSimplexMap

/-- A realization of the `Δ`-complex `K` in the topological space `X`: the
characteristic maps `χ` together with the point-set and topological conditions
that make `X` the quotient of the disjoint union of the simplices along the face
identifications. -/
structure DeltaRealization (K : DeltaCx) (X : TopCat) extends DeltaSimplexMap K X where
  /-- `X` is compact. -/
  [compact : CompactSpace X]
  /-- `X` is Hausdorff. -/
  [t2 : T2Space X]
  /-- Every point of `X` lies in exactly one open simplex. -/
  bij : ∀ x : X, ∃! p : OpenSimplex K, DeltaSimplexMap.real toDeltaSimplexMap p = x
  /-- `X` carries the weak (quotient) topology determined by the closed
  simplices: a set is open iff all its preimages under the characteristic maps
  are open. -/
  weak : ∀ s : Set X, IsOpen s ↔
    ∀ (k : ℕ) (σ : Fin (K.card k)), IsOpen ((DeltaSimplexMap.cls toDeltaSimplexMap k σ) ⁻¹' s)

end

end Work.DeltaHomology
