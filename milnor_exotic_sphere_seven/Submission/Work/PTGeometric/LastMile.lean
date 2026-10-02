import Submission.Work.PTGeometric.SmoothToTautEqOn
import Submission.Work.PTGeometric.LocalLevel
import Submission.Work.PTGeometric.Orientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the last mile — the ambient form of the genuine collapse end

This file fixes the **interface of the last mile** of the Pontryagin–Thom construction, in the form
in which it is actually provable from the available analytic tools (G1, G2, G3, G4) and in which the
one genuine difficulty of the geometric half — the fact that the null-homotopy of the collapse map
takes values in the **one-point compactification** of the manifold part of the Thom space, so that it
hits `∞` and is not a map into a manifold at all — is isolated as data of a *smaller* source.

## The difficulty, and the shape of its solution

Let `T = OnePoint E` be the Thom space of the universal bundle (its manifold part `E` is the total
space of `γ_k`), and let `H : M → T` be the null-homotopy of the genuine collapse map of a multiple
of the family.  The preimage `H ⁻¹' core` is the null-bordism; it is contained in the open set
`H ⁻¹' E`, and all the perturbation theory (G2, G3) happens there.  What cannot be done is to
*globally* replace `H` by a map into the manifold `E`: the `∞`-values of `H` are unavoidable (they
realise the basepoint of the Thom space), and no continuous map `T → E` is the identity near the
core (such a map would contract the sphere bundle of `γ_k`).

The solution used here is the standard one: **take the source to be a compact regular neighbourhood
of `H ⁻¹' core` inside `H ⁻¹' E`.**  On it, `H` *is* a map into the manifold `E` (it avoids `∞`),
and the smoothing and the perturbation are legitimate.  The construction of that neighbourhood from
the null-homotopy is the remaining topological step; its *interface* is
`Work.PTGeometric.NullSourceData` and the derivation of the ambient collapse end from it is
`Work.PTGeometric.ambientCollapseEnd_of_nullHomotopy` (both in
`Submission/Work/PTGeometric/ambientCollapseEnd_of_nullHomotopy.lean`), while everything on the
*analytic* side is proved here (G1, G2 (`smoothMap_into_tautTotal_eqOn`), G3
(`localTransversalApproximation`), G4 (`localPreimageTheorem`)).

## Why the data are stated in *ambient* coordinates

The map into `E = TotalSpace γ_k` is recorded by its ambient coordinates: the pair
`(P, v)` of a matrix-valued and a vector-valued map on `M`, with `P x` the orthogonal projection
onto the plane of `E` at `x` and `v x ∈ im (P x)` the vector.  This has three advantages, and each of
them is used:

* `smoothMap_into_tautTotal_eqOn` (G2) is stated in exactly these coordinates (the blueprint's G2:
  "mollify the matrix entries of `P ∘ H` and the vector `v ∘ H` in ambient coordinates");
* the zero set of the map into the core is simply `{x | v x = 0}`, so the *ends* are read off as
  a level set of a vector-valued function, with no bundle bookkeeping;
* the interface is *independent of the model of the Grassmannian*: `P` is a rank-`k` orthogonal
  projection of the ambient `n`-space, which is the classical Grassmann model, while
  `Work.ThomBordism.Grassmann.OG k m` is the quotient model with its own (chart-based) total space.
  A consumer that wants the Grassmann model transports the pair along
  `P ↦ (range P, v)`; this is exactly the classical identification `Gr_k(ℝⁿ) = {P : P† = P,
  P² = P, tr P = k}` and is *not* needed for the analytic steps.

## What the interface asks for, and what it yields

`Work.PTGeometric.AmbientCollapseEnd n k ι Fam` is the ambient data of one null-homotopy:

* a compact `T2` smooth `(9+k)`-manifold `M` with boundary (the regular neighbourhood: the disk with
  holes, cut down to a neighbourhood of the preimage of the core),
* ambient coordinates `(P, v)` with `P` a rank-`k` orthogonal projection everywhere, `v x ∈ im (P x)`,
  continuous on `M` and `C^∞` near the **collapse end** `S` (the part of `∂M` that carries the
  pieces: the ends at which `H` is the genuine collapse map),
* `S ⊆ ∂M` closed, with `S ∩ {v = 0}` (the end preimage of the core) identified with the pieces,
* `v` nonvanishing on `∂M ∖ S` (so no other boundary component contributes to the bordism),
* transversality of `v` to `0` along `im (P x)` (the honest form of "transverse to the core": the
  derivative of `ℓ ∘ v` is onto `ℝ^k` for a linear `ℓ` injective on the plane `im (P x)`, which is the
  fibre coordinate of a chart of the Grassmannian at `x`),

and the theorem `exists_localLevelData_of_ambientCollapseEnd` turns it into

* a closed `W ⊆ M` (the transverse zero set of the smoothed and re-projected map, so `W` is *not*
  `{v = 0}` — it is the preimage of the core of the perturbation), with local level-set data
  (`Work.PTGeometric.LocalLevelData`), whose boundary part `W ∩ ∂M` is exactly `S ∩ {v = 0}`, i.e.
  the pieces; the manifold structure and the boundary identification are then supplied by
  `Work.PTGeometric.localPreimageTheorem` (G4) and the endgame of `Genuine.lean`.

## Main definitions

* `Work.PTGeometric.AmbientCollapseEnd`

## Main results (delegated, statements recorded here)

* `Work.PTGeometric.exists_localLevelData_of_ambientCollapseEnd`
* `Work.PTGeometric.NullSourceData`, `Work.PTGeometric.ambientCollapseEnd_of_nullHomotopy`
  (`ambientCollapseEnd_of_nullHomotopy.lean`)
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **The ambient data of the genuine collapse end of a family.**

This is the last-mile interface: the geometric input that the Pontryagin–Thom construction has to
supply, in ambient coordinates and on a source on which the null-homotopy of the collapse map is a
map into the *manifold* part of the Thom space (see the file header for why this is the right shape).

The pieces of the family are `Fin m × ι` in the application (`m` copies of each member), and the
identification `endHomeo` of the end preimage with `Σ i, (Fam i).pt` is the content of the tubular
neighbourhood theorem's collapse: the collapse map of a tubular neighbourhood meets the zero section
exactly in the embedded submanifold (`Work.Tubular.tubeCollapse_mem_normalThomZero`), and its normal
coordinate is a submersion along it (`Work.Tubular.normalCoord`). -/
structure AmbientCollapseEnd (n k : ℕ) (ι : Type) [Fintype ι] (Fam : ι → Man8) where
  /-- the source: a compact regular neighbourhood of the preimage of the core -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  /-- the matrix part of the ambient coordinates: the orthogonal projection onto the plane -/
  P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  /-- the vector part: the vector of the plane -/
  v : M → EuclideanSpace ℝ (Fin n)
  /-- the matrix part is continuous -/
  continuous_P : Continuous P
  /-- the vector part is continuous -/
  continuous_v : Continuous v
  /-- the vector part is globally `C^∞` — it is the *smoothed* null-homotopy (G2), which is where
  the ambient data of this interface come from -/
  contMDiff_v : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v
  /-- the matrix part is a rank-`k` orthogonal projection at every point -/
  isProj : ∀ x : M, ContinuousLinearMap.adjoint (P x) = P x ∧ P x * P x = P x ∧
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (P x) = (k : ℝ)
  /-- the vector part lies in the plane -/
  mem : ∀ x : M, P x (v x) = v x
  /-- **the collapse end**: the part of the boundary at which the map is the genuine collapse map -/
  S : Set M
  /-- the collapse end is closed -/
  isClosed_S : IsClosed S
  /-- the collapse end is a part of the boundary -/
  S_subset_bdry : S ⊆ (𝓡∂ ((8 + k) + 1)).boundary M
  /-- the ambient data are `C^∞` near the collapse end (the collapse of a tubular neighbourhood is
  smooth near the core: `Work.Tubular.normalCoord`) -/
  smooth_near_S : ∃ V : Set M, S ⊆ V ∧ IsOpen V ∧
    ContMDiffOn (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞ P V ∧
    ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v V
  /-- **the end preimage of the zero section is the disjoint union of the pieces** -/
  endHomeo : ↥(S ∩ {x : M | v x = 0}) ≃ₜ (Σ i : ι, (Fam i).pt)
  /-- off the collapse end the map avoids the zero section: no other boundary component contributes
  to the null-bordism -/
  avoid : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, x ∉ S → v x ≠ 0
  /-- **transversality to the zero section**: at a point where `v` vanishes, the fibre coordinate in
  a chart of the Grassmannian is a submersion.  The chart is presented by a linear map `ℓ` which is
  injective on the plane `im (P y)` for **every** `y` in an open neighbourhood `U` of `x` (the chart
  is a trivialisation of the bundle over an open set of the Grassmannian, and its fibre projection is
  an isomorphism of each plane in the chart), and the condition is that `ℓ ∘ v` is a submersion at
  `x`. -/
  transverse : ∀ x : M, v x = 0 →
    ∃ (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) (U : Set M),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ℓ z = 0 → z = 0) ∧
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y : M => ℓ (v y)) x
  /-- **boundary transversality**: the same condition on the boundary, asked for the *same* `ℓ` and
  the *same* neighbourhood, with both the interior and the restricted submersivity (the shape of
  `Work.PTGeometric.IsCoreTransverseOnBoundary`). -/
  bndTransverse : ∀ (x : M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M), v x = 0 →
    ∃ (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) (U : Set M),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ℓ z = 0 → z = 0) ∧
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y : M => ℓ (v y)) x ∧
      IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
        (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => ℓ (v y)) ⟨x, hx⟩

attribute [instance] AmbientCollapseEnd.topologicalSpace AmbientCollapseEnd.chartedSpace
  AmbientCollapseEnd.isManifold AmbientCollapseEnd.compactSpace AmbientCollapseEnd.t2Space

end

end Work.PTGeometric
