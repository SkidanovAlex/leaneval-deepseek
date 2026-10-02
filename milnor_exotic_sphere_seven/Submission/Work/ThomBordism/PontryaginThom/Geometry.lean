import Submission.Work.ThomBordism.PontryaginThom.Defs
import Submission.Work.ThomBordism.PontryaginThom.Embedding
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.Iso
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 1, with the objects of the construction named

`Defs.lean` records the *output* of the Pontryagin–Thom construction as `PTRep` (the collapse map,
its class `α_V`, and the two Hurewicz pairings) and the input `PTExists` as the assertion that it
exists for every manifold.  This file splits that input into its named geometric pieces, so that
what remains to be constructed can be stated (and attacked) piecewise:

* `EmbeddingData V n` — an embedding `V ↪ ℝ^n` (a closed `C^∞` embedding with injective
  derivative).  **Its existence in *some* dimension is a theorem of Mathlib**
  (`embeddingData_of_mathlib`, from `exists_embedding_man8`); the codimension is not prescribed by
  Mathlib, which is why the input below is stated relative to a *given* embedding (the prescribed
  codimension is the standard weak Whitney embedding theorem, true for `n ≥ 16` and not in the
  workspace).
* `NormalGaussData V n E k m` — **the normal bundle** `ν` of the embedding (of rank `k`, as gluing
  data over a finite cover of `V`), **the Gauss map** `V → G̃r_k(ℝ^{k+m})` of the nearby sibling
  chapter `Work.ThomBordism.Grassmann`, and the fact that the Gauss map **classifies** `ν`
  (`ν ≅ gauss^* γ`); together with the Pontryagin classes of `ν` and their Whitney relation to the
  tangent classes (`NormalBundlData`), which is what the argument consumes.
* `TubularData V n E k D ng` — the **tubular neighbourhood** of the embedding, recorded through its
  output: the collapse map `S^{k+8} → T` and the two Hurewicz pairings with `p₁²U`, `p₂U` (the Thom
  isomorphism).  (A tubular neighbourhood is exactly what turns a neighbourhood of `V` in the sphere
  into `Th(ν)` and gives the collapse; it is not in Mathlib, so it is recorded here by its output.)
* `PTRep.ofGeometry` — the data assemble into a `PTRep`.
* `PTGeometryAt k D` and `ptExists_of_geometry` — the input in its split form, and the derivation of
  `PTExists` from it.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open Function Topology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-! ## The embedding -/

/-- **An embedding of `V` into `ℝ^n`**: closed, `C^∞`, with injective derivative at every point —
the exact form of Mathlib's Whitney embedding theorem (`Work.ThomBordism.PontryaginThom.exists_embedding_man8`),
and precisely what is needed for a normal bundle to exist at all. -/
structure EmbeddingData (V : Man8) (n : ℕ) where
  /-- the embedding -/
  e : V.pt → EuclideanSpace ℝ (Fin n)
  /-- smoothness -/
  smooth : ContMDiff (𝓡 8) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e
  /-- it is a closed embedding -/
  closedEmbedding : IsClosedEmbedding e
  /-- its derivative is injective everywhere -/
  injective_mfderiv : ∀ x : V.pt, Function.Injective
    (mfderiv (𝓡 8) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)

/-- **Mathlib's Whitney embedding theorem** gives embedding data, in some dimension. -/
theorem embeddingData_of_mathlib (V : Man8) : ∃ n : ℕ, Nonempty (EmbeddingData V n) := by
  obtain ⟨n, e, hsmooth, hclosed, hinj⟩ := exists_embedding_man8 V
  exact ⟨n, ⟨e, hsmooth, hclosed, hinj⟩⟩

/-! ## The normal bundle and the Gauss map -/

/-- **The normal bundle of an embedding, with the Gauss map classifying it.**

The target of the Gauss map is kept abstract (`G` with the universal bundle `γ` over it), so that
this file does not depend on the (heavy, separately developed) Grassmann chapter: the intended
instance is `G = Grassmann.OG k m` with `γ = Grassmann.tautologicalBundle k m`, which is set up in
`GrassmannBridge.lean`.

* `ν` is the normal bundle of `E : EmbeddingData V n`, of rank `k`, as gluing data
  (`Work.TangentClasses.RealBundle`) over a finite cover of `V`;
* `G`, `γ` are the Grassmannian of oriented `k`-planes in `ℝ^{k+m}` and its tautological bundle;
* `gauss` is the Gauss map `V → G`;
* `classifies` records that the Gauss map classifies `ν`: the pullback of `γ` along `gauss` is
  isomorphic to `ν`;
* `normal` is the Pontryagin classes of `ν` with their Whitney relation to the tangent classes
  (`NormalBundlData`) — the fact the argument uses.

For an embedding into `ℝ^{k+8}` the rank of the normal bundle is `k`, so this is the universal rank
of the Thom target `Th(γ_k)`. -/
structure NormalGaussData (V : Man8) (n : ℕ) (E : EmbeddingData V n) (k m : ℕ) (κ : Type) where
  /-- the cover of `V` over which the normal bundle is given -/
  ι : Type
  [fintype : Fintype ι]
  /-- the normal bundle `ν` -/
  ν : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι
  /-- the Grassmannian of oriented `k`-planes in `ℝ^{k+m}` -/
  G : Type
  [topologicalSpace : TopologicalSpace G]
  /-- its tautological bundle `γ` -/
  γ : Work.TangentClasses.RealBundle G (Fin k → ℝ) κ
  /-- the Gauss map of the embedding -/
  gauss : C(V.pt, G)
  /-- the Gauss map classifies the normal bundle: `ν ≅ gauss^* γ` -/
  classifies : Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap γ gauss) ν)
  /-- the Pontryagin classes of `ν`, with the Whitney relation to the tangent classes -/
  normal : NormalBundlData V

attribute [instance] NormalGaussData.fintype

/-! ## The tubular neighbourhood, through its output -/

/-- **The tubular-neighbourhood data of the embedding, through its output**: the collapse map
`S^{k+8} → T` (collapse along a tubular neighbourhood of `V ⊂ ℝ^{k+8}`, composed with the map
`Th(ν) → T` induced by the classifying map of `ν`) and the two Hurewicz pairings of its class with
`p₁²U`, `p₂U`, which compute the normal Pontryagin numbers (the Thom isomorphism). -/
structure TubularData {V : Man8} {n : ℕ} {κ : Type} (E : EmbeddingData V n) (k m : ℕ)
    (D : ThomTarget k) (ng : NormalGaussData V n E k m κ) where
  /-- the collapse map -/
  collapse : GenLoop (Fin (k + 8)) D.T D.t₀
  /-- the pairing of its class with `p₁²U` is the normal `p₁²`-number -/
  hurewicz_p1sq : kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse))
    = ng.normal.normalP1Sq
  /-- the pairing of its class with `p₂U` is the normal `p₂`-number -/
  hurewicz_p2 : kronH ℤ (ssetOf D.T) (k + 8) D.p2U
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse))
    = ng.normal.normalP2

/-- **The geometric data assemble into a `PTRep`**: the normal classes, the collapse map and its two
pairings are exactly the fields of `PTRep`. -/
def PTRep.ofGeometry {V : Man8} {n : ℕ} {E : EmbeddingData V n} {k m : ℕ} {κ : Type} {D : ThomTarget k}
    (ng : NormalGaussData V n E k m κ) (td : TubularData E k m D ng) : PTRep V k D where
  normal := ng.normal
  collapse := td.collapse
  hurewicz_p1sq := td.hurewicz_p1sq
  hurewicz_p2 := td.hurewicz_p2

/-! ## The input in split form -/

/-- **The geometric input of the chapter, with the objects named**: for every closed oriented smooth
`8`-manifold `V` there are an embedding of `V` into some `ℝⁿ` (with the properties of
`EmbeddingData`), the normal bundle of that embedding with its Gauss map (and the Whitney relation),
and the tubular-neighbourhood data (the collapse map and the Thom-isomorphism pairings).

Compared with `PTExists` this isolates (i) the embedding (whose existence is Mathlib's theorem in an
*unbounded* dimension, `embeddingData_of_mathlib`; here the dimension may be chosen by the prover),
(ii) the normal bundle and the Gauss map classifying it, and (iii) the tubular neighbourhood, hence
the collapse and the Thom isomorphism pairings.  The parameter `κ` (the index type of the cover of
the Grassmannian) is quantified inside the existential: `NormalGaussData` is only satisfiable for a
*nonempty* index type, so quantifying over all `κ` outside would make the statement unsatisfiable
(see `NormalGaussData.nonempty`, which shows the opposite: the interface *is* satisfiable whenever
`κ` is inhabited). -/
def PTGeometryAt (k : ℕ) (D : ThomTarget k) : Prop :=
  ∀ V : Man8, ∃ (n : ℕ) (E : EmbeddingData V n) (m : ℕ) (κ : Type)
    (ng : NormalGaussData V n E k m κ), Nonempty (TubularData E k m D ng)

/-- **`PTExists` from the split geometric input**: the normal bundle and the tubular-neighbourhood
data of one embedding assemble into the Pontryagin–Thom data of `Defs.lean`, hence give the class
`α_V`.  (The embedding itself is needed only to *carry* the geometric input: `PTRep` does not
mention it.) -/
theorem ptExists_of_geometryAt {k : ℕ} {D : ThomTarget k} (h : PTGeometryAt k D) : PTExists k D := by
  intro V
  obtain ⟨n, E, m, κ, ng, ⟨td⟩⟩ := h V
  exact ⟨PTRep.ofGeometry ng td⟩

end

end Work.ThomBordism.PontryaginThom
