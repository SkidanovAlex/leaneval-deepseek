import Mathlib
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.Interface
import Submission.Work.ThomBordism.PontryaginThom.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The *genuine* tubular data of an embedded piece — the TUBULAR half of
`Work.PTGeometric.GenuineTubeGeometry`

The collar producer of the last mile (`Work.PTGeometric.ConcreteLastMileSource`, hence the `hcol`
hypothesis of `Work.ThomBordism.thomRational_of_collarConnWeak`) quantifies over the *genuine*
collapse data of the family: the structure `Work.PTGeometric.GenuineTubeGeometry` has a TUBULAR half
(`emb`, `ε`, `chart`, `q`, `R`, `J`, `g`, the representative `rep`, and the identification `isGeom`
that the **loop of `rep` is TUBULAR's concrete collapse** `Work.Tubular.alphaV`) and a half about the
coordinate structure of the concrete Thom space (`core`, `coord`, …), which is area PTGEOMETRIC's.

This file isolates the TUBULAR half as `Work.ThomBordism.GenuineTubeData`, so that the two halves can
be produced independently: the geometric half is TUBULAR's tubular-neighbourhood theorem plus the
Pontryagin–Thom representative (`Work.Tubular.tubeThomRep_of_nuPairing`, whose collapse *is*
`Work.Tubular.alphaV` by construction — the reason `isGeom` is provable rather than assumed), while
PTGEOMETRIC supplies the coordinate half.

The `isGeom` field is stated as an equality of `GenLoop`s with the reindexing
`finCongr (Nat.add_comm 8 k) : Fin (8 + k) ≃ Fin (k + 8)` (TUBULAR's cube is `Fin (8 + k)`, the
chapter's representative lives on `Fin (k + 8)`), which is exactly the shape in which
`Work.Tubular.tubeThomRep_of_nuPairing` builds its collapse
(`GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α`).
-/

open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

/-- **The genuine tubular data of one embedded piece**: TUBULAR's tube data of an embedding of a
closed oriented `8`-manifold into `ℝ^{8+k}` (`emb`, `ε`, `chart`, `q`, the box radius `R`), the
Gauss/classifying map `J` into the universal Thom space, the metric-free collapse `g`, a
Pontryagin–Thom representative of the piece on a prescribed normal-bundle datum `N`, and **the
identification that the loop of that representative is TUBULAR's concrete collapse**
`Work.Tubular.alphaV` (the `isGeom` field of `Work.PTGeometric.GenuineTubeGeometry`). -/
structure GenuineTubeData (V : Man8) (k : ℕ) (D : ThomTarget k) (N : NormalBundlData V) where
  /-- the embedding of the piece in `ℝ^{8+k}` -/
  emb : EmbeddingData V (8 + k)
  /-- the radius of the tube chart -/
  ε : ℝ
  hε : 0 < ε
  /-- TUBULAR's tube chart of the embedding -/
  chart : Work.Tubular.TubeChart emb ε
  /-- a point of the normal sphere bundle -/
  q : Work.Tubular.NormalSphSub emb ε
  /-- the radius of the cube containing the tube -/
  R : ℝ
  hR : 0 ≤ R
  hbox : ∀ y ∈ chart.U, ∀ j : Fin (8 + k), |y.ofLp j| < R
  /-- the Gauss/classifying map of the normal bundle, on the metric-free Thom spaces -/
  J : C(OnePoint (Work.Tubular.NormalTotal emb), D.T)
  hJ : J OnePoint.infty = D.t₀
  /-- the metric-free Pontryagin–Thom collapse of the ambient space onto the normal bundle -/
  g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal emb))
  hg : ∀ y, y ∉ chart.openTube → g (OnePoint.some y) = OnePoint.infty
  /-- the Pontryagin–Thom representative of the piece -/
  rep : Work.Tubular.TubeThomRep k D V N
  /-- **the loop of the representative is TUBULAR's concrete collapse** (the reindexing
  `finCongr (Nat.add_comm 8 k)` is TUBULAR's cube `Fin (8 + k)` read in the chapter's `Fin (k + 8)`) -/
  isGeom : rep.collapse
    = GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k))
        (Work.Tubular.alphaV chart hR hbox D.t₀ J hJ g hg)

end Work.ThomBordism
