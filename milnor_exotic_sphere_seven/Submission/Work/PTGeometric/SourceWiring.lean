import Submission.Work.PTGeometric.SourceAssembly
import Submission.Work.ThomBordism.sourceRawAmbientData_pinned
import Submission.Work.ThomBordism.sourceRawAmbientData_tied
import Submission.Work.ThomBordism.sourceRawAmbientData_tied_collar
import Submission.Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion
import Submission.Work.PTGeometric.Assembly
import Submission.Work.ThomBordism.grassmannTargetT2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the source construction is PROVED — the last mile reduces to the orientation datum

`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion` (the **source construction**: the compact
region `M = {Φ ≤ 0}` cut out by the defining function of the core preimage, the ambient coordinates of
the null-homotopy on it, the prescribed charts at the boundary zeros) is **proved** (by a delegated
prover; module `Submission.Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`).

Hence `Work.PTGeometric.RawAmbientProducer` — the producer with the *proved* region-charting theorem
and defining function as its last arguments — is a **theorem**:

* `Work.PTGeometric.rawAmbientProducer : RawAmbientProducer`;
* `Work.PTGeometric.concreteLastMileSource_of_orientation` — `ConcreteLastMileSource k D` for every
  `k ≥ 11` from the **orientation datum** alone (no source-construction hypothesis left);
* `Work.PTGeometric.OrientationProducer`, `Work.PTGeometric.OrientationProducerConn` — the residual
  orientation input as one named `Prop`;
* `Work.PTGeometric.transversalityCoreFamily_oriented`,
  `…transversalityCoreFamilyNE_oriented` and `…transversalityCoreFamilyConn_oriented` — **the
  deliverable with `ConcreteLastMile` eliminated**: the geometric input is now only
  1. TUBULAR's tubular data of the family (`Nonempty (GenuineTubeGeometry …)`, the allowed
     hypothesis), and
  2. the orientation datum of the collapse end (`OrientationProducer`, G5: the relative fundamental
     class of the zero set with the pieces as boundary).

Everything else is proved in this directory.  `Work.ThomBordism.ptGeometricWiring` consumes
`transversalityCoreFamilyConn`; the `…_oriented` variant below is the same statement with the last
mile replaced by its two remaining inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-- **The source construction is proved**: `RawAmbientProducer` holds, by
`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion` with its two proved inputs
(`Work.PTGeometric.regionManifoldTheorem_of_isCompact_weak` and
`Work.PTGeometric.exists_sourceRegionPhiInteriorSign`) discharged. -/
theorem rawAmbientProducer : RawAmbientProducer :=
  fun k D ι _ Fam _ hk hne G m hm hpow hwk hphi =>
    nonempty_rawAmbientData_of_sourceRegion (D := D) (Fam := Fam) hk hne G m hm hpow hwk hphi

/-- **`ConcreteLastMileSource` from the orientation datum alone**: the source construction is proved,
so the only geometric input left is the orientation datum of the collapse end. -/
theorem concreteLastMileSource_of_orientation
    (horg : ∀ (n : ℕ) (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (Fam : ι → Man8)
      (hk : k ≤ n) (C : ContinuousAmbientData n k ι Fam),
      AmbientOrientationDatum (toAmbientCollapseEnd hk C)) :
    ∀ (k : ℕ) (D : ThomTarget k) [T2Space D.T], 11 ≤ k → ConcreteLastMileSource k D :=
  concreteLastMileSource_of_rawData rawAmbientProducer horg

/-- **The source construction with the prescribed charts *pinned***: the conclusion of
`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`, with the extra conjunct that every
prescribed chart `ellE j` is the frame-coordinate reading of the tube's orthonormal frame of the
normal space at some foot:
`ellE j = (Work.Tubular.readCLM (emb i) ND j' w0) ∘ Work.PTGeometric.projEuc k G.mU G.hmU`.

The pin is what fixes the *orientation* of the trivialisation of the normal bundle, hence the class
`hPairδ w` of the Pontryagin–Thom null-bordism; without it the prescribed charts are arbitrary linear
maps (only their kernel on the planes of `P` is constrained), so the sign `s_C` of the boundary
identity is a free parameter of the interface.  This statement is proved by
`Work.ThomBordism.sourceRawAmbientData_pinned` (a transcription of the source construction with the
pinned pointwise chart data `Work.ThomBordism.exists_localData_at_boundaryZero_pinned` and with the
pinning carried through the finite-cover step). -/
theorem exists_rawAmbientData_pinned {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ D0 : RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2),
      ∀ j : Fin D0.mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (ND : NormalData (Fam i) k (G.emb i).e) (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ ND.D.baseSet j'),
        D0.ellE j = (Work.Tubular.readCLM (G.emb i) ND j' w0).comp
          (Work.PTGeometric.projEuc k G.mU G.hmU) :=
  Work.ThomBordism.sourceRawAmbientData_pinned (D := D) (Fam := Fam) hk hne G m hm hpow
    (regionManifoldTheorem_of_isCompact_weak k)
    (exists_sourceRegionPhiInteriorSign G m hpow _ (isClosed_sourceBasepointSet G m hpow)
      (disjoint_sourceZeroSet_sourceBasepointSet G m hpow))

/-- **The source construction with the prescribed charts *tied* to the geometry's tie.**

This is `exists_rawAmbientData_pinned` with the normal datum of the pin *named*: the prescribed charts
are the frame-coordinate readings of `Classical.choose (G.tie i)`, i.e. of the normal datum that
`G.pulledThom i` and the oriented Gauss data `G.gauss` are stated for.  This is the form in which the
coorientation of the level set (read by the prescribed charts) is tied to the piece's given
orientation (whose local degree is `G.localDegree`), which is what the boundary sign needs. -/
theorem exists_rawAmbientData_tied {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ D0 : RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2),
      ∀ j : Fin D0.mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ (Classical.choose (G.tie i)).D.baseSet j'),
        D0.ellE j =
          (Work.Tubular.readCLM (G.emb i) (Classical.choose (G.tie i)) j' w0).comp
            (Work.PTGeometric.projEuc k G.mU G.hmU) :=
  Work.ThomBordism.sourceRawAmbientData_tied (D := D) (Fam := Fam) hk hne G m hm hpow
    (regionManifoldTheorem_of_isCompact_weak k)
    (exists_sourceRegionPhiInteriorSign G m hpow _ (isClosed_sourceBasepointSet G m hpow)
      (disjoint_sourceZeroSet_sourceBasepointSet G m hpow))

/-- **The source construction with the prescribed charts *tied* AND the collar of the level set.**

This is `exists_rawAmbientData_tied` with the extra conjunct that the level set `{v = 0}` of the
produced raw data carries a collar in the `Lvl` chart structure (`sourceRawAmbientData_tied_collar`).
The collar is what the ORIENT route to the relative fundamental class of the level set consumes
(`Work.ThomBordism.exists_relFundClass_of_collar`). -/
theorem exists_rawAmbientData_tiedCollar {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ D0 : RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2),
      (∀ j : Fin D0.mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ (Classical.choose (G.tie i)).D.baseSet j'),
        D0.ellE j =
          (Work.Tubular.readCLM (G.emb i) (Classical.choose (G.tie i)) j' w0).comp
            (Work.PTGeometric.projEuc k G.mU G.hmU)) ∧
      Work.ThomBordism.SourceBoundaryCoord D0 ∧
      (∃ (hWcl : IsClosed {x : D0.M | D0.v x = 0})
        (L : Work.PTGeometric.LocalLevelData k D0.M {x : D0.M | D0.v x = 0}),
        Work.ThomBordism.SourceOrientHyp D0 hWcl L) :=
  Work.ThomBordism.sourceRawAmbientData_tied_collar (D := D) (Fam := Fam) hk hne G m hm hpow
    (regionManifoldTheorem_of_isCompact_weak k)
    (exists_sourceRegionPhiInteriorSign G m hpow _ (isClosed_sourceBasepointSet G m hpow)
      (disjoint_sourceZeroSet_sourceBasepointSet G m hpow))

/-- **The raw ambient data chosen by the source construction** (the source construction, with the
prescribed charts pinned to the tube's frame-coordinate trivialisation and with the collar of its
level set).

This is the *named* witness of `Work.PTGeometric.exists_rawAmbientData_tiedCollar`; it is introduced
so that the two specifications (the pin and the collar) can be stated about a single named object
rather than about an anonymous `Classical.choose`.  `producedAmbientData` below is
`continuousAmbientDataOf` applied to it. -/
noncomputable def producedRawData {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T] (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2) :=
  Classical.choose (exists_rawAmbientData_tiedCollar (D := D) (Fam := Fam) hk
    (fun i => G.nonempty i) G m hm hpow)

/-- **The specification of the chosen raw data**: the tied pin *and* the collar of the level set. -/
theorem producedRawData_spec {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    (∀ j : Fin (producedRawData hk G m hm hpow).mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ (Classical.choose (G.tie i)).D.baseSet j'),
        (producedRawData hk G m hm hpow).ellE j =
          (Work.Tubular.readCLM (G.emb i) (Classical.choose (G.tie i)) j' w0).comp
            (Work.PTGeometric.projEuc k G.mU G.hmU)) ∧
      Work.ThomBordism.SourceBoundaryCoord (producedRawData hk G m hm hpow) ∧
      (∃ (hWcl : IsClosed {x : (producedRawData hk G m hm hpow).M |
          (producedRawData hk G m hm hpow).v x = 0})
        (L : LocalLevelData k (producedRawData hk G m hm hpow).M
          {x : (producedRawData hk G m hm hpow).M |
            (producedRawData hk G m hm hpow).v x = 0}),
        Work.ThomBordism.SourceOrientHyp (producedRawData hk G m hm hpow) hWcl L) :=
  Classical.choose_spec (exists_rawAmbientData_tiedCollar (D := D) (Fam := Fam) hk
    (fun i => G.nonempty i) G m hm hpow)

/-- **The tied pin of the chosen raw data.** -/
theorem producedRawData_ellE_tied {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∀ j : Fin (producedRawData hk G m hm hpow).mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ (Classical.choose (G.tie i)).D.baseSet j'),
      (producedRawData hk G m hm hpow).ellE j =
        (Work.Tubular.readCLM (G.emb i) (Classical.choose (G.tie i)) j' w0).comp
          (Work.PTGeometric.projEuc k G.mU G.hmU) :=
  (producedRawData_spec hk G m hm hpow).1

/-- **The boundary coordination of the produced raw data**: the pieces bound the level set of the raw
field with the given orientations — the conjunct added to the source construction's existence theorem
by the strengthened form (`Work.ThomBordism.sourceRawAmbientData_tied_collar`).  Equivalently (long
exact sequence of the pair) the class of the pieces is the boundary of a relative class. -/
theorem producedRawData_coord {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Work.ThomBordism.SourceBoundaryCoord (producedRawData hk G m hm hpow) :=
  (producedRawData_spec hk G m hm hpow).2.1

/-- **The collar of the level set of the chosen raw data.**

The witness `producedRawData` carries a collar of its level set `{v = 0}` in the `Lvl` chart structure
(`Work.ThomBordism.sourceRawAmbientData_tied_collar`) — the form in which the ORIENT route to a
relative fundamental class of the level set consumes it (`Work.ThomBordism.exists_relFundClass_of_collar`).

**Caveat (important for consumers).**  This collar is a collar of the level set of the *raw* field
`(producedRawData hk G m hm hpow).v`.  The field `(producedAmbientData hk G m hm hpow).v` is the
*smoothing* of it (`Work.PTGeometric.continuousAmbientData_of_rawData` replaces `v` by a `C^∞`
field `v'` agreeing with it on the collar `S0` of the boundary), so this collar does **not** transfer
to the produced level set definitionally; a consumer needs the (proved) agreement `v' = v` on `S0`,
which contains the whole boundary part of the level set. -/
theorem producedRawData_collar {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ (hWcl : IsClosed {x : (producedRawData hk G m hm hpow).M |
        (producedRawData hk G m hm hpow).v x = 0})
      (L : LocalLevelData k (producedRawData hk G m hm hpow).M
        {x : (producedRawData hk G m hm hpow).M |
          (producedRawData hk G m hm hpow).v x = 0}),
      letI : ChartedSpace (EuclideanHalfSpace 9)
        (levelModel {x : (producedRawData hk G m hm hpow).M |
          (producedRawData hk G m hm hpow).v x = 0} hWcl L) :=
        Lvl.Setup.instChartedSpace (levelSetup {x : (producedRawData hk G m hm hpow).M |
          (producedRawData hk G m hm hpow).v x = 0} hWcl L)
      Nonempty (Work.Surgery.Collar 8 (levelModel {x : (producedRawData hk G m hm hpow).M |
        (producedRawData hk G m hm hpow).v x = 0} hWcl L)) := by
  obtain ⟨hWcl, L, hc, -⟩ := (producedRawData_spec hk G m hm hpow).2.2
  exact ⟨hWcl, L, hc⟩

/-- **The orientation family of the level set of the chosen raw data**: the second component of the
`Work.ThomBordism.SourceOrientHyp` conjunct of `producedRawData_spec` — the collar of the canonical
level model `levelModel (sourceLevelSet (producedRawData …))` in its `Lvl` chart structure together
with a half-orientation family of that model.  This is the `hspec` input of
`Work.ThomBordism.orientationProducer_of_spec`. -/
theorem producedRawData_orientation {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ (hWcl : IsClosed
        (Work.ThomBordism.sourceLevelSet (producedRawData hk G m hm hpow)))
      (L : LocalLevelData k (producedRawData hk G m hm hpow).M
        (Work.ThomBordism.sourceLevelSet (producedRawData hk G m hm hpow))),
      Work.ThomBordism.SourceOrientHyp (producedRawData hk G m hm hpow) hWcl L :=
  (producedRawData_spec hk G m hm hpow).2.2

/-- **The continuous ambient data produced by the source construction** (the specific term the
orientation datum of G5 is about).  It is `continuousAmbientDataOf` applied to `producedRawData` (the
source construction, with the prescribed charts pinned to the tube's frame-coordinate trivialisation —
see `Submission/Work/ThomBordism/NOTE_OWNER_ORIENTATION2.md`).
Its *type* is unchanged, so no consumer is affected by the choice of witness. -/
noncomputable def producedAmbientData {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T] (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ContinuousAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2) :=
  continuousAmbientDataOf (Nat.le_add_right k G.mU) (by omega)
    (producedRawData hk G m hm hpow)

/-- **The prescribed charts of the produced ambient data are the frame-coordinate readings of the
*geometry's tie*.**

This is the tied form of `producedAmbientData_ellE_pinned`: the normal datum of the pin is the one
carried by `GenuineTubeGeometry.tie`, i.e. the same normal datum for which `pulledThom` is a `gtdU`
and the oriented Gauss data are the padded Gauss plane.  Read off from the choice in
`producedAmbientData` by `Classical.choose_spec`. -/
theorem producedAmbientData_ellE_tied {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∀ j : Fin (producedAmbientData hk G m hm hpow).mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ (Classical.choose (G.tie i)).D.baseSet j'),
      (producedAmbientData hk G m hm hpow).ellE j =
        (Work.Tubular.readCLM (G.emb i) (Classical.choose (G.tie i)) j' w0).comp
          (Work.PTGeometric.projEuc k G.mU G.hmU) :=
  producedRawData_ellE_tied (D := D) (Fam := Fam) hk G m hm hpow

/-- **The prescribed charts of the produced ambient data are the tube's frame-coordinate readings.**

This is the *visible* form of the pin: `Classical.choose_spec` of the strengthened existence theorem
that `producedAmbientData` uses.  A consumer of `Work.PTGeometric.producedAmbientData` may use it as a
theorem (the *value* of the chosen witness is opaque, but its specification is not). -/
theorem producedAmbientData_ellE_pinned {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    ∀ j : Fin (producedAmbientData hk G m hm hpow).mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (ND : NormalData (Fam i) k (G.emb i).e) (j' : CoverIdx (Fam i) k)
        (hb : w0 ∈ ND.D.baseSet j'),
      (producedAmbientData hk G m hm hpow).ellE j = (Work.Tubular.readCLM (G.emb i) ND j' w0).comp
        (Work.PTGeometric.projEuc k G.mU G.hmU) := by
  intro j
  obtain ⟨i, w0, j', hb, h⟩ :=
    producedAmbientData_ellE_tied (D := D) (Fam := Fam) hk G m hm hpow j
  exact ⟨i, w0, Classical.choose (G.tie i), j', hb, h⟩


/-- **The residual orientation input of the last mile, tied to the *actual* geometric data.**

For every family of nonempty closed oriented `8`-manifolds, every `k ≥ 11`, every *genuine* collapse
datum of it (`GenuineTubeGeometry k D ι Fam`) and every `m > 0` with the `m`-th power of the product of
the pieces' genuine Pontryagin–Thom classes trivial, the collapse end produced by the source
construction — i.e. `toAmbientCollapseEnd` applied to `producedAmbientData hk G m hm hpow` — carries the
**orientation datum** of the situation (G5): a relative fundamental class of the zero set of the ambient
field on the canonical model of the level set, whose boundary is the sum of the pieces' fundamental
classes.

This is the *only* geometric statement of the last mile that is not proved in this directory.  It is a
statement about the *specific* data of the construction (so the oriented Gauss data `G.gauss`, the
collapse identity `G.isGeom`, the zero-set theorem `G.zero`, the tube frames and TUBULAR's local degree
are all available to its proof). -/
def OrientationProducer : Prop :=
  ∀ (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (Fam : ι → Man8) [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt) (G : GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1),
    AmbientOrientationDataFree (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
      (producedAmbientData hk G m hm hpow))

/-- **The residual orientation input of the last mile, in the CONNECTED-FAMILY form that the
endgame actually uses.**

This is `Work.PTGeometric.OrientationProducer` with the additional hypothesis
`(hconn : ∀ i, ConnectedSpace (Fam i).pt)` on the family.  The endgame invokes the producer only on
families of *connected* manifolds (`Submission/Work/ThomBordism/orientedWiring.lean`:
`hgeo ι F hconn`, `hconn : ∀ i, ConnectedSpace (F i).pt`), and connectedness of the pieces is
*needed* by the last mile: the branch of the field
`Work.PTGeometric.GenuineTubeGeometry.pulledThom_gauss` — which is what the coorientation of the level
set inherits from `Work.PTGeometric.GenuineTubeGeometry.gauss` — is pinned only through
`Work.ThomBordism.localDegree_universalThomClass`, whose statement carries `[ConnectedSpace V.pt]`
and whose proof goes through `Work.Tubular.pathConnectedSpace_of_man8`.  See
`Submission/Work/ThomBordism/NOTE_SESSION64.md` sections 8-10.

The unrestricted `OrientationProducer` above is *stronger* and implies this one
(`Work.PTGeometric.orientationProducerConn_of_orientationProducer`), so nothing is lost by a consumer
of the strong form. -/
def OrientationProducerConn : Prop :=
  ∀ (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (Fam : ι → Man8) [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt) (hconn : ∀ i, ConnectedSpace (Fam i).pt)
    (G : GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1),
    AmbientOrientationDataFree (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
      (producedAmbientData hk G m hm hpow))

/-- The unrestricted orientation producer implies the connected-family one. -/
theorem orientationProducerConn_of_orientationProducer (h : OrientationProducer) :
    OrientationProducerConn :=
  fun k D ι _ Fam _ hk hne _hconn G m hm hpow => h k D ι Fam hk hne G m hm hpow

/-- **`ConcreteLastMileSource` from the connected-family orientation producer.** -/
theorem concreteLastMileSource_of_orientationProducerConn (hO : OrientationProducerConn) :
    ∀ (k : ℕ) (D : ThomTarget k) [T2Space D.T], 11 ≤ k →
      ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8), (∀ i, ConnectedSpace (Fam i).pt) →
        ∀ (G : GenuineTubeGeometry k D ι Fam) (m : ℕ), 0 < m →
          (∏ i, tubeAlpha (G.rep i)) ^ m = 1 →
          ∃ N' : ℕ, 0 < N' ∧
            ∃ Esrc : AmbientCollapseEnd (k + G.mU) k (Fin N' × ι) (fun x => Fam x.2),
              AmbientOrientationDataFree Esrc := by
  intro k D _ hk ι _ Fam hconn G m hm hpow
  exact ⟨m, hm, toAmbientCollapseEnd (Nat.le_add_right k G.mU)
      (producedAmbientData hk G m hm hpow),
    hO k D ι Fam hk (fun i => G.nonempty i) hconn G m hm hpow⟩

/-- **The canonical-model producer implies the free-model one.**  The hypothesis is the previous
shape of `Work.PTGeometric.OrientationProducer` (the orientation datum on the canonical `Lvl` model of
the level set).  Since `Work.PTGeometric.levelOrientationDatumFree_of_datum` turns the canonical-model
datum into the free-model one, the redefined `OrientationProducer` is **weaker**: no producer of the
old shape loses anything. -/
theorem orientationProducer_of_ambientOrientationDatum
    (h : ∀ (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (Fam : ι → Man8) [T2Space D.T]
      (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt) (G : GenuineTubeGeometry k D ι Fam)
      (m : ℕ) (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1),
      AmbientOrientationDatum (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
        (producedAmbientData hk G m hm hpow))) :
    OrientationProducer :=
  fun k D ι _ Fam _ hk hne G m hm hpow =>
    ambientOrientationDataFree_of_datum (h k D ι Fam hk hne G m hm hpow)

theorem concreteLastMileSource_of_orientationProducer (hO : OrientationProducer) :
    ∀ (k : ℕ) (D : ThomTarget k) [T2Space D.T], 11 ≤ k → ConcreteLastMileSource k D := by
  intro k D _ hk ι _ Fam G m hm hpow
  exact ⟨m, hm, toAmbientCollapseEnd (Nat.le_add_right k G.mU)
      (producedAmbientData hk G m hm hpow),
    hO k D ι Fam hk (fun i => G.nonempty i) G m hm hpow⟩

/-- **The deliverable with the last mile replaced by its two remaining inputs**, in the
nonempty-family form.

The geometric input is: for every family of nonempty closed oriented `8`-manifolds, a codimension
`k ≥ 11`, the universal Grassmannian target `Th(γ_k)`, TUBULAR's tubular data of the family
(`Nonempty (GenuineTubeGeometry k D ι F)`) and the orientation datum of the collapse end
(`OrientationProducer`).  This is strictly weaker than `hgeo` of
`Work.PTGeometric.transversalityCoreFamily`: the source construction is no longer an input. -/
theorem transversalityCoreFamilyNE_oriented
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F))
    (hO : OrientationProducer)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyNE :=
  transversalityCoreFamilyNE_of_concreteDataNE
    (fun ι _ F hne =>
      ⟨11, le_rfl, grTarget hΦ 11 (by omega), hgeo 11 le_rfl ι F hne,
        concreteLastMile_of_source
          (concreteLastMileSource_of_orientationProducer hO 11 (grTarget hΦ 11 (by omega))
            (by omega))⟩)
    hrat

/-- **The deliverable with the last mile replaced by its two remaining inputs** (unrestricted form:
the empty members of a family are dropped on the consumer's side). -/
theorem transversalityCoreFamily_oriented
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, Nonempty (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F))
    (hO : OrientationProducer)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  Work.ThomBordism.transversalityCoreFamily_of_nonempty
    (transversalityCoreFamilyNE_oriented hΦ hgeo hO hrat)

/-- **The deliverable with the last mile replaced by its two remaining inputs**, in the connected
family form consumed by the neighbouring areas
(`Work.ThomBordism.transversalityCoreFamilyConn`). -/
theorem transversalityCoreFamilyConn_oriented
    (hΦ : ∀ (k : ℕ), Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (Grassmann.sset (Grassmann.TautologicalThomSpace k 10))).homology
        (k + 8))
    (hgeo : ∀ (k : ℕ) (hk : 11 ≤ k) (ι : Type) [Fintype ι] (F : ι → Man8),
      (∀ i, ConnectedSpace (F i).pt) →
      Nonempty (GenuineTubeGeometry k (grTarget hΦ k (by omega)) ι F))
    (hO : OrientationProducer)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyConn :=
  transversalityCoreFamilyConn_of_concreteDataConn
    (fun ι _ F _ =>
      ⟨11, le_rfl, grTarget hΦ 11 (by omega), hgeo 11 le_rfl ι F (fun i => inferInstance),
        concreteLastMile_of_source
          (concreteLastMileSource_of_orientationProducer hO 11 (grTarget hΦ 11 (by omega))
            (by omega))⟩)
    hrat

end

end Work.PTGeometric
