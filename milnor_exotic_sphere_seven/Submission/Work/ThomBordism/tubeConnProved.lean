import Submission.Work.ThomBordism.tubeConnForm
import Submission.Work.ThomBordism.tubeThomRepOfEmbeddingOdd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The connected-family form of obligation 2, discharged — with the per-member choice named

`Work.ThomBordism.TubeAssemblyInterface` (`Submission/Work/ThomBordism/tubeConnForm.lean`) is the
per-member assembly of the Pontryagin–Thom construction at a *prescribed* odd codimension `k ≥ 11`
with the *canonical* comparison map `Φ := PhiG k`.  It is proved by
`Work.ThomBordism.tubeThomRepOfEmbeddingOdd`
(`Submission/Work/ThomBordism/tubeThomRepOfEmbeddingOdd.lean`), whose content is the whole chain of
`Submission/Work/ThomBordism/TUBEDATA_NOTES.md`: the Gauss/classifying data of the embedding, the
(2b) description of the universal classes (`universalClassPullbackPair` + the concrete/generic bridge
`compPull_compPullZ_absNZ`), the local degree
(`Work.Tubular.exists_localDegree_at_collapseRelK8_of_connected`) with the sign absorbed by the
per-member choice of the based map out of the normal Thom space (odd `k`:
`Work.ThomBordism.Grassmann.tautological_negMap_thomClass`), and the number identities
`Work.ThomBordism.gauss_p1Sq_pairing` / `gauss_p2_pairing`
(`Submission/Work/ThomBordism/tubeNumberStep.lean`).

Everything is *named*, so that area PTGEOMETRIC's boundary-sign argument can consume exactly the same
choice:

* `Work.ThomBordism.familyTubeRep` — the chosen tubular datum of one member at a prescribed odd
  `(k, E)`, with its spec `…hurewicz_p1sq` / `…hurewicz_p2` (the two pairings with `p₁(γ)²U`, `p₂U`);
* `Work.ThomBordism.familyCodim` (+ `…_spec`), `Work.ThomBordism.familyPhi`,
  `Work.ThomBordism.familyData` — the *per-family* choice of the common odd codimension `k ≥ 11`, of
  the comparison map `Φ := PhiG k`, and of the tubular data of every member;
* **`Work.ThomBordism.tubeDataPerFamilyConn`** — `Work.ThomBordism.tubeDataPerFamily`'s body with
  `(∀ i, ConnectedSpace (F i).pt)` added, the form consumed by
  `Work.ThomBordism.thomRational_of_serreE3b_connData`.
-/

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom

/-- **The per-member Pontryagin–Thom datum chosen by the assembly**, as a *named* object: the tubular
data of `V` at the universal target `connTarget k _ (PhiG k _)` for a prescribed *odd* codimension
`k ≥ 11` and a prescribed embedding `E : V ↪ ℝ^{8+k}`.  (`Work.ThomBordism.tubeThomRepOfEmbeddingOdd`
is the `Nonempty` statement; this is its `Classical.choice`, so that every consumer uses the *same*
choice.) -/
def familyTubeRep (V : Man8) [ConnectedSpace V.pt] (k : ℕ) (hk : 11 ≤ k) (hodd : Odd k)
    (E : EmbeddingData V (8 + k)) (N : NormalBundlData V) :
    Work.Tubular.TubeThomRep k
      (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) V N :=
  Classical.choice (Work.ThomBordism.tubeThomRepOfEmbeddingOdd V hk hodd E N)

/-- The spec of `Work.ThomBordism.familyTubeRep`: the pairing of its collapse class with `p₁(γ)²U` is
the normal `p₁²`-number. -/
theorem familyTubeRep_hurewicz_p1sq (V : Man8) [ConnectedSpace V.pt] (k : ℕ) (hk : 11 ≤ k)
    (hodd : Odd k) (E : EmbeddingData V (8 + k)) (N : NormalBundlData V) :
    Work.Cohomology.kronH ℤ (Work.ThomBordism.PontryaginThom.ssetOf
        (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).T) (k + 8)
        (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).p1sqU
        (Work.ThomBordism.PontryaginThom.hurewiczClassOf (k + 8) (one_le_add_eight k)
          (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
          (Quotient.mk _ (familyTubeRep V k hk hodd E N).collapse))
      = N.normalP1Sq :=
  (familyTubeRep V k hk hodd E N).hurewicz_p1sq

/-- The spec of `Work.ThomBordism.familyTubeRep`: the pairing of its collapse class with `p₂U` is the
normal `p₂`-number. -/
theorem familyTubeRep_hurewicz_p2 (V : Man8) [ConnectedSpace V.pt] (k : ℕ) (hk : 11 ≤ k)
    (hodd : Odd k) (E : EmbeddingData V (8 + k)) (N : NormalBundlData V) :
    Work.Cohomology.kronH ℤ (Work.ThomBordism.PontryaginThom.ssetOf
        (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).T) (k + 8)
        (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).p2U
        (Work.ThomBordism.PontryaginThom.hurewiczClassOf (k + 8) (one_le_add_eight k)
          (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
          (Quotient.mk _ (familyTubeRep V k hk hodd E N).collapse))
      = N.normalP2 :=
  (familyTubeRep V k hk hodd E N).hurewicz_p2

/-- **The named per-member interface, discharged.** -/
theorem tubeAssemblyInterface : TubeAssemblyInterface := by
  intro V _inst k hk hodd hE N
  obtain ⟨E⟩ := hE
  exact ⟨familyTubeRep V k hk hodd E N⟩

/-! ## The per-family choice -/

/-- **The common codimension chosen for a finite family**: the odd `k ≥ 11` above the family's
embedding bound (`Work.ThomBordism.exists_embeddingData_ge_family_odd'`). -/
def familyCodim {ι : Type} [Fintype ι] (F : ι → Man8) : ℕ :=
  Classical.choose (Work.ThomBordism.exists_embeddingData_ge_family_odd' F)

/-- The spec of `Work.ThomBordism.familyCodim`: it is `≥ 11`, odd, and every member embeds in
`ℝ^{8 + familyCodim F}`. -/
theorem familyCodim_spec {ι : Type} [Fintype ι] (F : ι → Man8) :
    11 ≤ familyCodim F ∧ Odd (familyCodim F) ∧
      ∀ i, Nonempty (EmbeddingData (F i) (8 + familyCodim F)) :=
  Classical.choose_spec (Work.ThomBordism.exists_embeddingData_ge_family_odd' F)

/-- **The comparison map chosen for a finite family**: `Φ := PhiG k` at the family's codimension. -/
def familyPhi {ι : Type} [Fintype ι] (F : ι → Man8) :
    Work.Thom.OpenThom (Work.ThomBordism.Grassmann.tautologicalBundle (familyCodim F) 10)
      (8 + familyCodim F) ≃ₗ[ℤ] Work.ThomBordism.Grassmann.TSCoh (familyCodim F) 10 :=
  Work.ThomBordism.PhiG (familyCodim F)
    (by have h := (familyCodim_spec F).1; omega)

/-- **The tubular data of a finite *connected* family, from the named per-member choice**: at the
family's codimension and comparison map, with the member's embedding given by
`Work.ThomBordism.familyCodim_spec`. -/
theorem tubeDataPerFamily_data {ι : Type} [Fintype ι] (F : ι → Man8)
    (hconn : ∀ i, ConnectedSpace (F i).pt) :
    Work.ThomBordism.FamilyTubeData (familyCodim F)
      (connTarget (familyCodim F) (by have h := (familyCodim_spec F).1; omega)
        (familyPhi F)) ι F := by
  obtain ⟨hk, hodd, hE⟩ := familyCodim_spec F
  intro i N
  haveI : ConnectedSpace (F i).pt := hconn i
  obtain ⟨E⟩ := hE i
  exact ⟨familyTubeRep (F i) (familyCodim F) hk hodd E N⟩

/-- **`Work.ThomBordism.tubeDataPerFamily` for *connected* families** (the funded form): exactly
`htube`'s body with `(∀ i, ConnectedSpace (F i).pt)` added, with the codimension chosen odd and above
the family's embedding bound (`Work.ThomBordism.familyCodim`), the comparison map
`Φ := Work.ThomBordism.PhiG k` (`Work.ThomBordism.familyPhi`) and the per-member data given by the
named choice `Work.ThomBordism.familyTubeRep`. -/
theorem tubeDataPerFamilyConn :
    ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ (k : ℕ) (_ : 11 ≤ k)
        (Φ : Work.Thom.OpenThom (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ]
          Work.ThomBordism.Grassmann.TSCoh k 10),
        Work.ThomBordism.FamilyTubeData k (connTarget k (by omega) Φ) ι F := by
  intro ι _ F hconn
  exact ⟨familyCodim F, (familyCodim_spec F).1, familyPhi F, tubeDataPerFamily_data F hconn⟩

end

end Work.ThomBordism
