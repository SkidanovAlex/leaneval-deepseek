import Mathlib
import Submission.Work.PTGeometric.RawAmbientData
import Submission.Work.PTGeometric.LevelOrientation
import Submission.Work.PTGeometric.exists_sourceRegionPhiInteriorSign
import Submission.Work.PTGeometric.sourceZeroSet_boundary_homeo
import Submission.Work.PTGeometric.regionManifoldTheorem_of_isCompact_weak

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the assembly of the source construction into `ConcreteLastMileSource`

Everything of the last mile is proved except
* the *raw-data producer* `Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion` (the source
  geometry: the region `M`, the ambient coordinates of the null-homotopy, the prescribed charts at
  the pieces — `DESIGN_SOURCE_CONSTRUCTION.md`), and
* the *orientation input* `Work.PTGeometric.AmbientOrientationDatum` (G5: the orientation family of
  the canonical model of the zero set, the relative fundamental class it pins down, and the boundary
  identity — the ORIENT area).

This file performs the two compositions that remain:

* `nonempty_rawAmbientData_of_geometry`: the raw-data producer, with its two other inputs
  (`RegionManifoldTheoremOfIsCompactWeak`, `SourceRegionPhiInteriorSign`) supplied by the proved
  `exists_sourceRegionPhiInteriorSign` (and `IsClosed`/`Disjoint` for the basepoint preimage);
* `concreteLastMileSource_of_rawData`: the deliverable `Work.PTGeometric.ConcreteLastMileSource`,
  from the raw-data producer and the orientation inputs, through the proved chain
  `RawAmbientData ⟹ ContinuousAmbientData ⟹ AmbientPreData ⟹ AmbientCollapseEnd`.

## Main results

* `Work.PTGeometric.nonempty_rawAmbientData_of_geometry`
* `Work.PTGeometric.concreteLastMileSource_of_rawData`
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

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The basepoint preimage of the flat source homotopy** — the set to be avoided by the source
region (the source must avoid the base point of the Thom space, where the ambient coordinates are
undefined). -/
def sourceBasepointSet {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Set (EuclideanHalfSpace ((8 + k) + 1)) :=
  {x | flatSourceHomotopy8 (k := k) (familySource G m hpow).H (familySource G m hpow).φ x.1 = D.t₀}

theorem isClosed_sourceBasepointSet [T2Space D.T] (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    IsClosed (sourceBasepointSet (D := D) (Fam := Fam) G m hpow) :=
  isClosed_eq
    ((continuous_flatSourceHomotopy8 k (familySource G m hpow).H (familySource G m hpow).φ).comp
      continuous_subtype_val)
    continuous_const

theorem disjoint_sourceZeroSet_sourceBasepointSet [T2Space D.T] (G : GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Disjoint (sourceZeroSet G m hpow) (sourceBasepointSet (D := D) (Fam := Fam) G m hpow) := by
  rw [Set.disjoint_left]
  intro x hxZ hxT
  exact G.t0_notMem_core (hxT ▸ hxZ)

/-- **The raw-data producer** — the geometric statement
`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`, as one named hypothesis.

**History.**  The first version of this producer was FALSE as then stated: `RawAmbientData` carried
`bndZero_cov : ∀ x ∈ ∂M, v x = 0 → ∃ j, ptE j = x`, a finite *enumeration* of the boundary zeros,
which together with `hend` forced every piece to be finite (machine-checked in
`rawAmbientData_refutation.lean`, diagnosed in `NOTE_RAWAMBIENTDATA_BNDZERO.md`).  The interface has
been repaired (`FIX_BNDZERO.md`, carried out this session): `bndZero_cov` is now a finite **open
cover** `∃ j, x ∈ UE j`, the transversality `bndZero_trans` is asked at **every** covered boundary zero
(pointwise, not at an enumerated base point), and the structures carry the closure margin
`ellE_inj_cl`, so that the prescribed charts enter the chart family *verbatim*.

The two other inputs of the geometric statement — the region-charting theorem and the defining
function of the region — are **proved** (`Work.PTGeometric.regionManifoldTheorem_of_isCompact_weak` and
`Work.PTGeometric.exists_sourceRegionPhiInteriorSign`, the latter via the two lemmas on the basepoint
preimage below), so they appear here as *arguments* of the producer, and the wrappers below discharge
them. -/
def RawAmbientProducer : Prop :=
  ∀ (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (Fam : ι → Man8) [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt) (G : GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hwk : RegionManifoldTheoremOfIsCompactWeak k)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow) (sourceBasepointSet G m hpow)),
    Nonempty (RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))

/-- **The raw-data producer, with its two proved inputs discharged.** -/
theorem nonempty_rawAmbientData_of_geometry [T2Space D.T]
    (hprod : RawAmbientProducer) (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Nonempty (RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2)) :=
  hprod k D ι Fam hk hne G m hm hpow (regionManifoldTheorem_of_isCompact_weak k)
    (exists_sourceRegionPhiInteriorSign G m hpow _ (isClosed_sourceBasepointSet G m hpow)
      (disjoint_sourceZeroSet_sourceBasepointSet G m hpow))

/-- **The deliverable `ConcreteLastMileSource` from the raw-data producer and the orientation
inputs.**  The only hypotheses are

* `hraw`: the raw-data producer (the source geometry; `nonempty_rawAmbientData_of_geometry` above
  reduces it to `∀ k, RegionManifoldTheoremOfIsCompactWeak k` and the defining function);
* `horg`: the orientation input of the situation (`AmbientOrientationDatum`, G5) for the collapse end
  produced by the construction.  (ORIENT's relative fundamental class in dimension `8` is no longer a
  parameter: the datum below carries the class itself.)

Everything between them is proved in this directory. -/
theorem concreteLastMileSource_of_rawData
    (hraw : RawAmbientProducer)
    (horg : ∀ (n : ℕ) (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (Fam : ι → Man8)
      (hk : k ≤ n) (C : ContinuousAmbientData n k ι Fam),
      AmbientOrientationDatum (toAmbientCollapseEnd hk C)) :
    ∀ (k : ℕ) (D : ThomTarget k) [T2Space D.T], 11 ≤ k → ConcreteLastMileSource k D := by
  intro k D _ hk ι _ Fam G m hm hpow
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  have hk0 : 0 < k := by omega
  obtain ⟨R⟩ := nonempty_rawAmbientData_of_geometry (k := k) (D := D) (Fam := Fam) hraw hk
    (fun i => G.nonempty i) G m hm hpow
  obtain ⟨C⟩ := continuousAmbientData_of_rawAmbientData (n := k + G.mU)
    (Nat.le_add_right k G.mU) hk0 R
  exact ⟨m, hm, toAmbientCollapseEnd (Nat.le_add_right k G.mU) C,
    ambientOrientationDataFree_of_datum
      (D := toAmbientCollapseEnd (Nat.le_add_right k G.mU) C)
      (horg (k + G.mU) k D (Fin m × ι) (fun a => Fam a.2)
        (Nat.le_add_right k G.mU) C)⟩

end

end Work.PTGeometric
