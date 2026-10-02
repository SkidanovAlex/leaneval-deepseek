import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.Pad
import Submission.Work.ThomBordism.PontryaginThom.embeddingData_exists
import Submission.Work.ThomBordism.tubeSign
import Submission.Work.ThomBordism.degenerateFamily
import Submission.Work.Tubular.Interface
import Submission.Work.ThomBordism.pieceConnectivity
import Submission.Work.ThomBordism.Grassmann.thomSpaceClassesDetect_of_lowDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The connected-family form of obligation 2, and the named per-member interface

`Work.ThomBordism.tubeDataPerFamily` (`Submission/Work/ThomBordism/tubeDataPerFamily.lean`) is the
*unconditional* statement demanded by `Work.ThomBordism.thomRational_of_serreE3b_tubeData_collar`.
The reachable form — the one the project lead's funded route produces and the one consumed by
`Work.ThomBordism.thomRational_of_serreE3b_connData` — carries the connectedness of the members; it
is recorded here, with the residual geometric content exposed as a **named** interface
(`Work.ThomBordism.TubeAssemblyInterface`) so that area PTGEOMETRIC (whose boundary-sign argument
must consume exactly the same per-member choice) can import it instead of restating it.

* `Work.ThomBordism.connTarget` — the universal Grassmann Thom target at `m = 10` with the
  comparison map chosen by the producer; it is the body of `Work.ThomBordism.connGrTarget`
  (`Submission/Work/ThomBordism/connFinalWiring.lean`), re-stated as an `abbrev` here only because
  that module currently depends on area PTGEOMETRIC, which is in flux.  An `abbrev` unfolds, so the
  two spellings are definitionally equal up to the proof of `10 ≤ k`.
* `Work.ThomBordism.TubeAssemblyInterface` — the per-member assembly: for every connected `V`, every
  *odd* codimension `k ≥ 11` and every embedding `E : V ↪ ℝ^{8+k}`, the tubular data
  (`Work.Tubular.TubeThomRep`) of `V` at `connTarget k _ (PhiG k _)` exist, for every normal-bundle
  datum.  This is the per-member Pontryagin–Thom construction with `Φ := PhiG k` (*not* a
  `Classical.choose`) and the per-member sign absorbed inside the chosen based classifying map
  (`Odd k` makes the fibrewise reflection of `γ` flip the Thom class:
  `Work.ThomBordism.Grassmann.tautological_negMap_thomClass`).
* `Work.ThomBordism.tubeDataPerFamilyConn` — `Work.ThomBordism.tubeDataPerFamily` for *connected*
  families, proved from that interface: see `Submission/Work/ThomBordism/tubeConnProved.lean` (it
  cannot live here because it imports the per-member assembly, which imports this file for
  `connTarget`).  The family's codimension is chosen odd and above its embedding bound
  (`Work.ThomBordism.exists_embeddingData_ge_family_odd'`), the comparison map is `Φ := PhiG k`, and
  a connected member is nonempty, so the empty case does not arise.

Nothing here is a hypothesis of the final theorem: `TubeAssemblyInterface` is exactly the residual
geometric content of obligation 2 (the tubular Pontryagin–Thom construction at a *prescribed* odd
codimension with the *canonical* comparison map), and it is the shape which the per-member proof
strategy of `Submission/Work/ThomBordism/TUBEDATA_NOTES.md` produces.
-/

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom

/-- The universal Grassmann Thom target at `m = 10` with the comparison map chosen by the producer:
literally the body of `Work.ThomBordism.connGrTarget`. -/
abbrev connTarget (k : ℕ) (hk : 10 ≤ k)
    (Φ : Work.Thom.OpenThom (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
      Work.ThomBordism.Grassmann.TSCoh k 10) : ThomTarget k :=
  Work.ThomBordism.Grassmann.grassmannThomTarget k 10
    (Work.ThomBordism.thomSpaceConnected_of_pieceConnectivity k 10)
    (Work.ThomBordism.Grassmann.tautologicalThomClass k 10) Φ
    (Work.ThomBordism.Grassmann.thomSpaceClassesDetect_of_lowDegree k 10 hk (by norm_num)
      (Work.ThomBordism.Grassmann.tautologicalThomClass k 10) Φ)

/-- **A finite family of closed oriented `8`-manifolds embeds in `ℝ^{8+k}` for a common *odd*
`k ≥ 11`**: the family-wise form of Whitney's weak embedding theorem with the codimension chosen
after the family, and odd because that is what the Thom-class reflection of the tautological bundle
needs.  (This is `Work.ThomBordism.exists_embeddingData_ge_family_odd` in
`Submission/Work/ThomBordism/tubeGeometryData.lean`, re-derived here so that this module does not
depend on the (much heavier) `tubeGeometryData`.) -/
theorem exists_embeddingData_ge_family_odd' {ι : Type} [Fintype ι] (F : ι → Man8) :
    ∃ k : ℕ, 11 ≤ k ∧ Odd k ∧ ∀ i, Nonempty (EmbeddingData (F i) (8 + k)) := by
  classical
  obtain ⟨k₀, _hk₀, hE⟩ := Work.ThomBordism.PontryaginThom.exists_embeddingData_ge_family F
  refine ⟨2 * k₀ + 1, by omega, ⟨k₀, by ring⟩, fun i => ?_⟩
  obtain ⟨E⟩ := hE i
  have hcast : 8 + k₀ + (k₀ + 1) = 8 + (2 * k₀ + 1) := by ring
  exact ⟨hcast ▸ (Nat.add_comm k₀ 8 ▸ E).pad (k₀ + 1)⟩

/-- **The normal-bundle datum is irrelevant**: all `NormalBundlData` of a manifold have the same
`normalP1Sq`/`normalP2` (`Work.ThomBordism.PontryaginThom.NormalBundlData.normalP1Sq_eq`,
`…normalP2_eq` — both are the *tangent* numbers), so a `TubeThomRep` for one datum gives one for any
other.  (Useful because the per-member assembly produces its tubular data for the *geometric* normal
datum, while `Work.ThomBordism.FamilyTubeData` quantifies over every datum.) -/
theorem tubeThomRep_of_normalBundlData_eq {V : Man8} {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {N N' : NormalBundlData V} (r : Work.Tubular.TubeThomRep k D V N') :
    Nonempty (Work.Tubular.TubeThomRep k D V N) := by
  refine ⟨{ collapse := r.collapse, hurewicz_p1sq := ?_, hurewicz_p2 := ?_ }⟩
  · rw [r.hurewicz_p1sq, N'.normalP1Sq_eq, N.normalP1Sq_eq]
  · rw [r.hurewicz_p2, N'.normalP2_eq, N.normalP2_eq]

/-- **The per-member assembly interface of obligation 2**: for every connected closed oriented
`8`-manifold, every *odd* codimension `k ≥ 11` and every embedding `E : V ↪ ℝ^{8+k}`, the
Pontryagin–Thom data `Work.Tubular.TubeThomRep` of `V` at the universal target with the canonical
comparison map `Φ := Work.ThomBordism.PhiG k` exists, for every normal-bundle datum. -/
def TubeAssemblyInterface : Prop :=
  ∀ (V : Man8) [ConnectedSpace V.pt] (k : ℕ) (_hk : 11 ≤ k) (_hodd : Odd k),
    Nonempty (EmbeddingData V (8 + k)) → ∀ N : NormalBundlData V,
      Nonempty (Work.Tubular.TubeThomRep k
        (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) V N)

end

end Work.ThomBordism
