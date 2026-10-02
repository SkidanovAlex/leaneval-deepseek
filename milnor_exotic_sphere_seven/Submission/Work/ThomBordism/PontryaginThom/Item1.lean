import Submission.Work.ThomBordism.PontryaginThom.Pad
import Submission.Work.ThomBordism.PontryaginThom.Additivity
import Submission.Work.ThomBordism.PontryaginThom.Bordism
import Submission.Work.ThomBordism.PontryaginThom.Consistency
import Submission.Work.TangentClasses.Tangent
import Submission.Work.Thom.Iso
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 1 of the chapter: the objects of the Pontryagin–Thom construction, and `α_V`

The chapter's request has three items; item 2 (`Normal.lean`, `Hurewicz.lean`, `Rational.lean`) and
item 3 (`Additivity.lean`) are theorems.  This file is the *shape* of item 1: the geometric objects
of the Pontryagin–Thom construction, named, with `α_V ∈ π_{k+8}(T)` **derived** from them
(`ptExists_of_geom : PTGeom k D → PTExists k D`), so that `PTExists` is never a hypothesis of the
chapter's main theorems.

## The objects

* `WeakWhitney8 k` (`Pad.lean`) — an embedding `V ↪ ℝ^{k+8}` (closed, `C^∞`, injective derivative)
  for every `V`: the weak Whitney embedding theorem with the bound `k + 8 ≥ 2·8 + 1` (true for
  `k ≥ 9`).  Mathlib's Whitney embedding theorem (`Embedding.lean`) gives the embedding in *some*
  dimension, unboundedly, and `Pad.lean` proves that enlarging the ambient space is always possible
  (`EmbeddingData.pad`) while *shrinking* it is not available — so this is the exact form of the
  only embedding input.
* `NormalBundleGauss V k m κ` — the **normal bundle** `ν` of the embedding, of rank `k`, *tied to
  the tangent bundle* by a series of bundle isomorphisms
  `TV ⊕ ν ≅ ε^{k+8}` (the splitting of the trivial bundle along the embedding), together with the
  **Gauss map** `V → G̃r_k(ℝ^{k+m})` into the oriented Grassmannian (with its tautological bundle
  `γ`) which **classifies** `ν` (`ν ≅ gauss^* γ`).  Because of the splitting field this structure is
  *not* vacuous (a trivial `ν` would make `TV` stably trivial, which is false for e.g. `ℂP⁴`); the
  normal Pontryagin classes with their Whitney relation to the tangent ones are the fourth field.
* the **tubular neighbourhood**: recorded through its output, as in `Geometry.lean` — the collapse
  map `S^{k+8} → T` of the construction (collapse along the tubular neighbourhood, composed with
  `Th(ν) → T` from the Gauss map) together with the two Hurewicz pairings, i.e. the **Thom
  isomorphism**.  This is the one place where the two classical theorems absent from Mathlib and
  from the workspace are used: the tubular neighbourhood theorem and the Thom isomorphism.

## Why the tubular-neighbourhood field is a hypothesis and not a construction

See `README.md` §0 and §4: the workspace (like Mathlib) has no tubular neighbourhood theorem, no
Thom space functor on bundle maps, and no Sard for `m > n`; the *chapter* cannot contain the
construction, but it can (and does) name exactly the two classical theorems that supply it, derive
`α_V` from them, and prove everything that follows.  `Consistency.lean` and
`NormalGaussData.nonempty` below check that the interfaces are satisfiable.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-! ## The normal bundle and the Gauss map, tied to the tangent bundle -/

/-- **The normal bundle of an embedding, with the Gauss map classifying it and the splitting of the
trivial bundle.**

* `ν` — the normal bundle, a rank-`k` real bundle over `V` in gluing data form;
* `G`, `γ` — the oriented Grassmannian `G̃r_k(ℝ^{k+m})` and its tautological bundle (kept abstract,
  as in `Geometry.lean`, so that this file does not depend on the heavy Grassmann chapter; the
  intended instance is `Grassmann.OG k m` and `Grassmann.tautologicalBundle k m`);
* `gauss` — the Gauss map `V → G`;
* `classifies` — `ν ≅ gauss^* γ`;
* `splitting` — **`TV ⊕ ν ≅ ε^{k+8}`**: the embedding identifies `TV` with a subbundle of the
  trivial bundle whose complement is `ν`.  This is the field that makes the structure meaningful
  (it fails for a trivial `ν` unless `TV` is stably trivial);
* `normal` — the normal Pontryagin classes with the Whitney relation to the tangent ones (the two
  coefficients of `p(ν) ⌣ p(TV) = 1`). -/
structure NormalBundleGauss (V : Man8) (k m : ℕ) (κ : Type) where
  /-- the cover of `V` over which the normal bundle is given -/
  ι : Type
  [fintype : Fintype ι]
  /-- the normal bundle `ν` of the embedding, of rank `k` -/
  ν : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι
  /-- the oriented Grassmannian `G̃r_k(ℝ^{k+m})` -/
  G : Type
  [topologicalSpace : TopologicalSpace G]
  /-- its tautological bundle `γ` -/
  γ : Work.TangentClasses.RealBundle G (Fin k → ℝ) κ
  /-- the Gauss map of the embedding -/
  gauss : C(V.pt, G)
  /-- the Gauss map **classifies** the normal bundle: `ν ≅ gauss^* γ` -/
  classifies : Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap γ gauss) ν)
  /-- the splitting of the trivial bundle along the embedding: `TV ⊕ ν ≅ ε^{k+8}`.  (The ambient
  space is written `Euc (8 + k)`, i.e. `ℝ^{8+k}` — the same space as `ℝ^{k+8}` up to the canonical
  isometry `Fin (8+k) ≃ Fin (k+8)`; this is the convention in which the complement construction of
  `Complement.lean` lives.) -/
  splitting : Nonempty (Work.Thom.BundleIso
    ((Work.TangentClasses.tangentBundle (𝓡 8) V.pt).sum ν)
    (Work.TangentClasses.RealBundle.trivial V.pt (Euc (8 + k)) Unit))
  /-- the normal Pontryagin classes of `ν`, with the Whitney relation to the tangent ones -/
  normal : NormalBundlData V

attribute [instance] NormalBundleGauss.fintype NormalBundleGauss.topologicalSpace

/-- The rank of the normal bundle, and of the splitting: `rank (TV ⊕ ν) = 8 + k`.  (A numerical
check that the splitting is dimensionally consistent.) -/
theorem NormalBundleGauss.split_rank {V : Man8} {k m : ℕ} {κ : Type}
    (N : NormalBundleGauss V k m κ) :
    ((Work.TangentClasses.tangentBundle (𝓡 8) V.pt).sum N.ν).rank = k + 8 := by
  have h1 : (Work.TangentClasses.tangentBundle (𝓡 8) V.pt).rank = 8 := by
    rw [Work.TangentClasses.tangentBundle_rank, finrank_euclideanSpace_fin]
  have h2 : N.ν.rank = k := by
    simp [Work.TangentClasses.RealBundle.rank, Module.finrank_fin_fun]
  rw [Work.TangentClasses.RealBundle.sum_rank, h1, h2]
  omega

/-! ## The (vacuous) interface of `Geometry.lean` is satisfiable -/

/-- **The normal-bundle interface of `Geometry.lean` (`NormalGaussData`) is *satisfiable*** — it
constrains nothing about the embedding: its `ν`, `G`, `γ`, `gauss` are free data (here the Gauss map
into the manifold itself, so that the classification is `bundleComap_id`) and its `normal` field is
always inhabited (`NormalBundlData.nonempty`).  The mathematical content of item 1 is therefore
*not* in this interface: it is in `NormalBundleGauss` (the splitting `TV ⊕ ν ≅ ε^{k+8}`) and in the
tubular-neighbourhood field of `PTGeom`. -/
theorem NormalGaussData.nonempty (V : Man8) (n : ℕ) (E : EmbeddingData V n) (k m : ℕ) :
    Nonempty (NormalGaussData V n E k m Unit) := by
  classical
  obtain ⟨N⟩ := NormalBundlData.nonempty V
  exact ⟨{ ι := Unit
           ν := Work.TangentClasses.RealBundle.trivial V.pt (Fin k → ℝ) Unit
           G := V.pt
           γ := Work.TangentClasses.RealBundle.trivial V.pt (Fin k → ℝ) Unit
           gauss := ContinuousMap.id V.pt
           classifies := ⟨Work.Thom.BundleIso.ofEq (by rw [Work.Thom.bundleComap_id])⟩
           normal := N }⟩

/-- A `NormalBundleGauss` gives the (weaker, but simpler) interface `NormalGaussData` of
`Geometry.lean`, with the same `ν`, `G`, `γ`, `gauss` and normal classes. -/
def NormalBundleGauss.toNormalGaussData {V : Man8} {k m : ℕ} {κ : Type}
    (N : NormalBundleGauss V k m κ) {n : ℕ} (E : EmbeddingData V n) :
    NormalGaussData V n E k m κ where
  ι := N.ι
  ν := N.ν
  G := N.G
  γ := N.γ
  gauss := N.gauss
  classifies := N.classifies
  normal := N.normal

/-! ## The geometric input of item 1 -/

/-- **The geometric input of item 1**: for every closed oriented smooth `8`-manifold,

* the normal bundle `ν` of an embedding of `V` into `ℝ^{k+8}`, of rank `k`, its Gauss map into the
  oriented Grassmannian and the splitting `TV ⊕ ν ≅ ε^{k+8}` (`normalBundle`) — the existence of `ν`
  with that splitting *is* the existence of the embedding (the zero section of the disc bundle of `ν`
  is the embedded `V`), so the embedding is carried by this field and is not a separate hypothesis:
  Mathlib's embedding theorem (`Embedding.lean`) gives it per manifold, and `Pad.lean` shows that the
  only thing it does not give is the *uniform* codimension, which the splitting field consumes
  implicitly;
* the **tubular neighbourhood and the Thom isomorphism** (`tubular`): a collapse map
  `S^{k+8} → T` — collapse along a tubular neighbourhood of the embedded `V`, composed with the map
  `Th(ν) → T` induced by the classifying Gauss map — whose Hurewicz pairings with `p₁²U` and `p₂U`
  are the **normal** Pontryagin numbers of `ν` (for any presentation `N` of those classes, which by
  `NormalBundlData.normalP1Sq_eq`/`normalP2_eq` is `V.p1Sq` and `V.p1Sq - V.p2Num`).

This is the only hypothesis of the chapter that is not a construction available in the workspace:
the tubular neighbourhood theorem and the Thom isomorphism are classical theorems of the literature
(Thom), absent from Mathlib (as is Sard for `m > n`, which the weak Whitney bound would need).  See
`README.md` §0 for the exact status. -/
structure PTGeom (k : ℕ) (D : ThomTarget k) where
  /-- the normal bundle of an embedding into `ℝ^{k+8}`, its Gauss map, and the splitting
  `TV ⊕ ν ≅ ε^{k+8}` -/
  normalBundle : ∀ V : Man8, ∃ m : ℕ, ∃ κ : Type, Nonempty (NormalBundleGauss V k m κ)
  /-- **the tubular neighbourhood and the Thom isomorphism**: the collapse map of the construction
  and its two Hurewicz pairings -/
  tubular : ∀ (V : Man8) (N : NormalBundlData V),
    ∃ c : GenLoop (Fin (k + 8)) D.T D.t₀,
      kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ c))
        = N.normalP1Sq ∧
      kronH ℤ (ssetOf D.T) (k + 8) D.p2U
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ c))
        = N.normalP2

/-- **The minimal geometric input of item 1**: the tubular neighbourhood and the Thom isomorphism
alone (the normal Pontryagin classes being taken canonically, `NormalBundlData.nonempty`).  This is
what the chapter's argument actually consumes: `PTGeom` additionally names the normal bundle and the
Gauss map, which enter the construction but not the computation. -/
def PTGeomMin (k : ℕ) (D : ThomTarget k) : Prop :=
  ∀ (V : Man8) (N : NormalBundlData V),
    ∃ c : GenLoop (Fin (k + 8)) D.T D.t₀,
      kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ c))
        = N.normalP1Sq ∧
      kronH ℤ (ssetOf D.T) (k + 8) D.p2U
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ c))
        = N.normalP2

/-- The full geometric input gives the minimal one (forget the normal bundle). -/
theorem PTGeom.toPTGeomMin {k : ℕ} {D : ThomTarget k} (h : PTGeom k D) : PTGeomMin k D :=
  h.tubular

/-- **Item 1 from the minimal geometric input.** -/
theorem ptExists_of_geomMin {k : ℕ} {D : ThomTarget k} (h : PTGeomMin k D) : PTExists k D := by
  intro V
  obtain ⟨N⟩ := NormalBundlData.nonempty V
  obtain ⟨c, h1, h2⟩ := h V N
  exact ⟨{ normal := N, collapse := c, hurewicz_p1sq := h1, hurewicz_p2 := h2 }⟩

/-- **The normal-bundle half of the geometric input, as a named proposition** (the first field of
`PTGeom`): for every closed oriented smooth `8`-manifold there is a rank-`k` bundle `ν` with
`TV ⊕ ν ≅ ε^{k+8}`, a Gauss map into the oriented Grassmannian and the classification
`ν ≅ gauss^*γ`.  This is a theorem of the literature (the normal bundle of an embedded submanifold),
absent from Mathlib; see the README §4.2 for what a construction has to supply. -/
def NormalBundleExists (k : ℕ) : Prop :=
  ∀ V : Man8, ∃ m : ℕ, ∃ κ : Type, Nonempty (NormalBundleGauss V k m κ)

/-- **The tubular-neighbourhood half of the geometric input, as a named proposition** (the second
field of `PTGeom`): the collapse map of the construction and its two Hurewicz pairings (the tubular
neighbourhood theorem and the Thom isomorphism).  Classically a theorem; absent from Mathlib. -/
def TubularThomIso (k : ℕ) (D : ThomTarget k) : Prop := PTGeomMin k D

/-- The two named classical inputs assemble into the geometric input of the chapter (this is the
single place where they are consumed: filling these two `Prop`s is *all* that item 1 asks for). -/
theorem ptGeom_of_inputs {k : ℕ} {D : ThomTarget k} (h₁ : NormalBundleExists k)
    (h₂ : TubularThomIso k D) : PTGeom k D :=
  ⟨h₁, h₂⟩

/-- **Item 1, assembled: `α_V` exists.**  The geometric input `PTGeom k D` gives, for every `V`, the
Pontryagin–Thom data of `Defs.lean` — the normal classes, the collapse map and its two pairings —
hence the class `α_V ∈ π_{k+8}(T)` (`PTRep.α`).  This is the theorem that replaces the hypothesis
`exists_rep : PTExists k D` of the earlier versions of the chapter: `PTExists` is *derived*. -/
theorem ptExists_of_geom {k : ℕ} {D : ThomTarget k} (h : PTGeom k D) : PTExists k D := by
  intro V
  obtain ⟨N⟩ := NormalBundlData.nonempty V
  obtain ⟨c, h1, h2⟩ := h.tubular V N
  exact ⟨{ normal := N, collapse := c, hurewicz_p1sq := h1, hurewicz_p2 := h2 }⟩

/-- The geometric input of item 1 gives the split geometric input `PTGeometryAt` of `Geometry.lean`
— the interface in which the embedding, the normal bundle with its Gauss map, and the tubular data
are named separately — given the *uniform* Whitney embedding bound (`WeakWhitney8 k`, the weak
Whitney embedding theorem with the explicit codimension, `Pad.lean`).  Nothing in the chapter's main
theorems needs this: they go through `ptExists_of_geom` directly, and the only reason the uniform
bound appears here is that `PTGeometryAt` names the embedding as an argument. -/
theorem PTGeom.toPTGeometryAt {k : ℕ} {D : ThomTarget k} (h : PTGeom k D)
    (hemb : WeakWhitney8 k) : PTGeometryAt k D := by
  intro V
  obtain ⟨E⟩ := hemb V
  obtain ⟨m, κ, ⟨N⟩⟩ := h.normalBundle V
  refine ⟨k + 8, E, m, κ, N.toNormalGaussData E, ?_⟩
  obtain ⟨c, h1, h2⟩ := h.tubular V N.normal
  exact ⟨c, h1, h2⟩

/-- **Item 1 + item 2 in one statement**: under the geometric input `PTGeom k D` and rational
Hurewicz in the stable range, every closed oriented smooth `8`-manifold with vanishing `p₁²`- and
`p₂`-numbers has a Pontryagin–Thom class `α_V` (`PTRep.α`) a positive multiple of which is
null-homotopic — the input of the transversality chapter. -/
theorem PTGeom.exists_pow_eq_one_of_numbers_zero {k : ℕ} {D : ThomTarget k} (h : PTGeom k D)
    (hk : 10 ≤ k) (hrat : Work.Drive.RationalHurewiczStable) (V : Man8)
    (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ r : PTRep V k D, r.α ^ N = 1 := by
  obtain ⟨r⟩ := ptExists_of_geom h V
  obtain ⟨N, hN, hpow⟩ :=
    r.exists_pow_eq_one_of_numbers_zero (by omega) hrat (by omega) h1 h2
  exact ⟨N, hN, r, hpow⟩

/-- The same corollary from the minimal geometric input. -/
theorem PTGeomMin.exists_pow_eq_one_of_numbers_zero {k : ℕ} {D : ThomTarget k} (h : PTGeomMin k D)
    (hk : 10 ≤ k) (hrat : Work.Drive.RationalHurewiczStable) (V : Man8)
    (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ r : PTRep V k D, r.α ^ N = 1 := by
  obtain ⟨r⟩ := ptExists_of_geomMin h V
  obtain ⟨N, hN, hpow⟩ :=
    r.exists_pow_eq_one_of_numbers_zero (by omega) hrat (by omega) h1 h2
  exact ⟨N, hN, r, hpow⟩

/-- The same corollary from the chapter's geometric input, with the weaker contract
`Work.Drive.RationalHurewiczStable3` (the project lead's preferred hypothesis) and `k ≥ 11`. -/
theorem PTGeom.exists_pow_eq_one_of_numbers_zero_three {k : ℕ} {D : ThomTarget k} (h : PTGeom k D)
    (hk : 11 ≤ k) (hrat : Work.Drive.RationalHurewiczStable3) (V : Man8)
    (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ r : PTRep V k D, r.α ^ N = 1 := by
  obtain ⟨r⟩ := ptExists_of_geom h V
  obtain ⟨N, hN, hpow⟩ := r.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  exact ⟨N, hN, r, hpow⟩

/-- The same from the minimal geometric input, with `RationalHurewiczStable3` and `k ≥ 11`. -/
theorem PTGeomMin.exists_pow_eq_one_of_numbers_zero_three {k : ℕ} {D : ThomTarget k}
    (h : PTGeomMin k D) (hk : 11 ≤ k) (hrat : Work.Drive.RationalHurewiczStable3) (V : Man8)
    (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ r : PTRep V k D, r.α ^ N = 1 := by
  obtain ⟨r⟩ := ptExists_of_geomMin h V
  obtain ⟨N, hN, hpow⟩ := r.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  exact ⟨N, hN, r, hpow⟩

/-! ## The chapter's inputs -/

/-- **The inputs of the Pontryagin–Thom chapter**: the geometry of item 1 (`PTGeom`), and
transversality (the sibling chapter `Transversality`, in the single and family forms).  Additivity
(item 3) is *not* an input: it is the theorem `ptAdditivity`. -/
structure PTChapter (k : ℕ) (D : ThomTarget k) where
  /-- item 1: the geometric objects of the construction -/
  geom : PTGeom k D
  /-- transversality, single manifold -/
  transversality : Transversality k D
  /-- transversality, families -/
  transversalityFamily : TransversalityFamily k D

/-- The chapter's inputs give the construction-and-transversality inputs `PTInputs'` of
`Additivity.lean` (with `exists_rep` *derived*, `ptExists_of_geom`). -/
theorem PTChapter.toPTInputs' {k : ℕ} {D : ThomTarget k} (h : PTChapter k D) : PTInputs' k D :=
  { exists_rep := ptExists_of_geom h.geom
    transversality := h.transversality
    transversalityFamily := h.transversalityFamily }

/-- The chapter's inputs give the full inputs `PTInputs` of `Defs.lean`. -/
theorem PTChapter.toPTInputs {k : ℕ} {D : ThomTarget k} (h : PTChapter k D) : PTInputs k D :=
  h.toPTInputs'.toPTInputs

/-- **`TransversalityCoreFamily` from the chapter's inputs** (item 1 geometry + transversality) and
rational Hurewicz in the stable range. -/
theorem transversalityCoreFamily_of_chapter {k : ℕ} (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (h : PTChapter k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_inputs' D hk hrat h.toPTInputs'

/-- **`TransversalityCore` from the chapter's inputs.** -/
theorem transversalityCore_of_chapter {k : ℕ} (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (h : PTChapter k D) : TransversalityCore :=
  transversalityCore_of_inputs' D hk hrat h.toPTInputs'

/-- **`TransversalityCoreFamily` from the chapter's inputs and `RationalHurewiczStable3`**
(`k ≥ 11`): the project lead's preferred hypothesis. -/
theorem transversalityCoreFamily_of_chapter_three {k : ℕ} (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (h : PTChapter k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_inputs'_three D hk hrat h.toPTInputs'

/-- **`TransversalityCore` from the chapter's inputs and `RationalHurewiczStable3`** (`k ≥ 11`). -/
theorem transversalityCore_of_chapter_three {k : ℕ} (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (h : PTChapter k D) : TransversalityCore :=
  transversalityCore_of_inputs'_three D hk hrat h.toPTInputs'

/-- **The chapter's output from `PTGeom` and the family transversality, with
`RationalHurewiczStable3` and `k ≥ 11`.** -/
theorem transversalityCoreFamily_of_geom_three {k : ℕ} (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hgeom : PTGeom k D)
    (hF : TransversalityFamily k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_chapter_three D hk hrat
    { geom := hgeom
      transversality := transversalityOfTransversalityFamily hF
      transversalityFamily := hF }

/-- **The geometric input of item 1 together with transversality, plus rational Hurewicz, gives the
chapter's output** — the form in which the sibling `Transversality` chapter
(`Transversality/AssemblyCore.lean`) consumes this chapter's construction: only the *family*
transversality statement is needed. -/
theorem transversalityCoreFamily_of_geom {k : ℕ} (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hgeom : PTGeom k D)
    (hF : TransversalityFamily k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_chapter D hk hrat
    { geom := hgeom
      transversality := transversalityOfTransversalityFamily hF
      transversalityFamily := hF }

end

end Work.ThomBordism.PontryaginThom
