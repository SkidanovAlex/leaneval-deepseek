import Submission.Work.ThomBordism.concreteLastMileConn
import Submission.Work.PTGeometric.SourceWiring
import Submission.Work.StemsB.rh3Strict
import Submission.Work.StemsB.gysinStrict
import Submission.Work.ThomBordism.connAssembly
import Submission.Work.ThomBordism.boundarySigmaWiring
import Submission.Work.ThomBordism.boundaryMaximalIsotropic
import Submission.Work.ThomBordism.smooth8Fundamental
import Submission.Work.ThomBordism.tubeConnProved
import Submission.Work.ThomBordism.tubeConnForm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The final wiring through area PTGEOMETRIC's *oriented* source wiring

Project lead, probe round 20: the target is to be closed through area PTGEOMETRIC's deliverable
`Work.PTGeometric.transversalityCoreFamilyConn_oriented`, which replaces the last mile
(`ConcreteLastMile`) by its two remaining inputs: the genuine tube geometry of the family
(`Nonempty (GenuineTubeGeometry k (grTarget hΦ k) ι F)`) and the orientation datum of the collapse
end (`Work.PTGeometric.OrientationProducer`).

**Quantifier caveat (the same one as for the collar interfaces).**  PTGEOMETRIC's `hgeo` quantifies
over **every** `k ≥ 11`, and `GenuineTubeGeometry` contains the pieces' embeddings in `ℝ^{8+k}`; since
Mathlib's Whitney embedding theorem gives one codimension *per manifold* (unbounded, padded up only),
a family's embeddings exist at a *chosen* codimension but not at every `k ≥ 11`.  The wiring below
therefore takes the **per-family** form: for every family of connected members there is an odd
`k ≥ 11` **above the family's embedding bound** at which the genuine geometry exists.  That is the
form a producer can fill (`Work.ThomBordism.nonempty_genuineTubeData_family_at`,
`Submission/Work/ThomBordism/genuineTubeDataFamily.lean`, and, for the coordinate half,
`Work.ThomBordism.nonempty_genuineTubeGeometry_at`); the `∀ k ≥ 11` form of
`Work.PTGeometric.transversalityCoreFamilyConn_oriented` is recovered from it by instantiating the
producer's `k` — but it cannot be *filled* for a fixed `k`.

The comparison map of the universal target is the canonical `Φ := PhiG k` (so that the target is
`Work.ThomBordism.connTarget`, the target of the tubular data
`Work.ThomBordism.tubeDataPerFamilyConn_at`); `Work.PTGeometric.grTarget (fun k => PhiG k _) k _` is
*definitionally* `connTarget k _ (PhiG k _)` (checked in `_tbchk/compat.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

noncomputable section

/-- **The transversality core, from area PTGEOMETRIC's oriented source wiring and the per-family
genuine tube geometry.** -/
theorem transversalityCoreFamilyConn_orientedFam
    (hrat : Work.Drive.RationalHurewiczStable3)
    (hgeo : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hO : Work.PTGeometric.OrientationProducer) :
    TransversalityCoreFamilyConn :=
  Work.PTGeometric.transversalityCoreFamilyConn_of_concreteDataConn
    (fun ι _ F hconn => by
      obtain ⟨k, hk, hG⟩ := hgeo ι F hconn
      exact ⟨k, hk, connTarget k (by omega) (PhiG k (by omega)), hG,
        Work.PTGeometric.concreteLastMile_of_source
          (Work.PTGeometric.concreteLastMileSource_of_orientationProducer hO k _ hk)⟩)
    hrat

/-- **The target from the strict Gysin range, area PTGEOMETRIC's oriented source wiring and the
per-family genuine tube geometry.** -/
theorem thomRational_of_serreE3bStrict_orientedFam (hS : Work.StemsB.SerreE3bStrict)
    (hgeo : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hO : Work.PTGeometric.OrientationProducer) :
    Work.Drive.ThomRational :=
  thomRational_of_transversalityCoreConn
    (transversalityCoreFamilyConn_orientedFam (Work.StemsB.rh3_of_e3bStrict hS) hgeo hO)
    (boundarySigma_of_maximalIsotropic boundaryMaximalIsotropic) smooth8Fundamental

/-- The same from the full-range Gysin theorem. -/
theorem thomRational_of_serreE3b_orientedFam (hS : Work.Serre.SerreE3b)
    (hgeo : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hO : Work.PTGeometric.OrientationProducer) :
    Work.Drive.ThomRational :=
  thomRational_of_serreE3bStrict_orientedFam (Work.StemsB.serreE3bStrict_of_serreE3b hS) hgeo hO

/-! ## The connector to the geometry producer at a prescribed codimension

`Work.ThomBordism.nonemptyGenuineTubeGeometryAtFamily` (delegated, child H4-L2427) produces the
genuine tube geometry of a family at a *prescribed* odd `k ≥ 11` above the family's embedding bound.
The wiring above wants the per-family existential form (the codimension chosen *after* the family);
the connector below turns the prescribed-codimension producer into it, using
`Work.ThomBordism.exists_embeddingData_ge_family_odd'`.  With both, the target's proof is a single
application of `thomRational_of_serreE3bStrict_orientedFam`. -/

/-- **The target from the strict Gysin range, a *prescribed-codimension* genuine-tube-geometry
producer and the orientation datum.** -/
theorem thomRational_of_serreE3bStrict_at
    (hgen : ∀ (k : ℕ) (hk : 11 ≤ k) (hodd : Odd k) (ι : Type) [Fintype ι] (F : ι → Man8)
      (hconn : ∀ i, ConnectedSpace (F i).pt)
      (hE : ∀ i, Nonempty (EmbeddingData (F i) (8 + k))),
      Nonempty (Work.PTGeometric.GenuineTubeGeometry k
        (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hS : Work.StemsB.SerreE3bStrict)
    (hO : Work.PTGeometric.OrientationProducer) :
    Work.Drive.ThomRational :=
  thomRational_of_serreE3bStrict_orientedFam hS
    (fun ι _ F hconn => by
      obtain ⟨k, hk, hodd, hE⟩ := exists_embeddingData_ge_family_odd' F
      exact ⟨k, hk, hgen k hk hodd ι F hconn hE⟩)
    hO

/-! ## The same wirings from the CONNECTED-FAMILY orientation producer

`Submission/Work/ThomBordism/NOTE_SESSION64.md` (sections 8-10): the last mile needs connectedness of
the pieces (the branch of `pulledThom_gauss` — which the coorientation of the level set inherits from
`GenuineTubeGeometry.gauss` — is pinned only through
`Work.ThomBordism.localDegree_universalThomClass`, whose statement carries `[ConnectedSpace V.pt]`),
and every invocation of the producer in this file is on a family of connected manifolds anyway
(`hgeo`'s `hconn`).  These are the same wirings with `Work.PTGeometric.OrientationProducer` replaced
by its connected-family form `Work.PTGeometric.OrientationProducerConn`
(`Work.ThomBordism.transversalityCoreFamilyConn_of_concreteLastMileConn` is the consumer). -/

/-- The `TransversalityCoreFamilyConn` assembly from the connected-family orientation producer. -/
theorem transversalityCoreFamilyConn_orientedFamConn
    (hrat : Work.Drive.RationalHurewiczStable3)
    (hgeo : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hO : Work.PTGeometric.OrientationProducerConn) :
    TransversalityCoreFamilyConn :=
  Work.ThomBordism.transversalityCoreFamilyConn_of_concreteLastMileConn
    (fun ι _ F hconn => by
      obtain ⟨k, hk, hG⟩ := hgeo ι F hconn
      exact ⟨k, hk, connTarget k (by omega) (PhiG k (by omega)), hG,
        Work.ThomBordism.ConcreteLastMileConn.of_orientationProducerConn
          (D := connTarget k (by omega) (PhiG k (by omega))) hO hk⟩)
    hrat

/-- **The target from the strict Gysin range and the connected-family orientation producer.** -/
theorem thomRational_of_serreE3bStrict_orientedFamConn (hS : Work.StemsB.SerreE3bStrict)
    (hgeo : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hO : Work.PTGeometric.OrientationProducerConn) :
    Work.Drive.ThomRational :=
  thomRational_of_transversalityCoreConn
    (transversalityCoreFamilyConn_orientedFamConn (Work.StemsB.rh3_of_e3bStrict hS) hgeo hO)
    (boundarySigma_of_maximalIsotropic boundaryMaximalIsotropic) smooth8Fundamental

/-- The same from the full-range Gysin theorem. -/
theorem thomRational_of_serreE3b_orientedFamConn (hS : Work.Serre.SerreE3b)
    (hgeo : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k),
        Nonempty (Work.PTGeometric.GenuineTubeGeometry k
          (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hO : Work.PTGeometric.OrientationProducerConn) :
    Work.Drive.ThomRational :=
  thomRational_of_serreE3bStrict_orientedFamConn (Work.StemsB.serreE3bStrict_of_serreE3b hS) hgeo hO

/-- **The target from the strict Gysin range, a prescribed-codimension genuine-tube-geometry
producer and the connected-family orientation producer.** -/
theorem thomRational_of_serreE3bStrict_atConn
    (hgen : ∀ (k : ℕ) (hk : 11 ≤ k) (hodd : Odd k) (ι : Type) [Fintype ι] (F : ι → Man8)
      (hconn : ∀ i, ConnectedSpace (F i).pt)
      (hE : ∀ i, Nonempty (EmbeddingData (F i) (8 + k))),
      Nonempty (Work.PTGeometric.GenuineTubeGeometry k
        (connTarget k (by omega) (PhiG k (by omega))) ι F))
    (hS : Work.StemsB.SerreE3bStrict)
    (hO : Work.PTGeometric.OrientationProducerConn) :
    Work.Drive.ThomRational :=
  thomRational_of_serreE3bStrict_orientedFamConn hS
    (fun ι _ F hconn => by
      obtain ⟨k, hk, hodd, hE⟩ := exists_embeddingData_ge_family_odd' F
      exact ⟨k, hk, hgen k hk hodd ι F hconn hE⟩)
    hO

end

end Work.ThomBordism
