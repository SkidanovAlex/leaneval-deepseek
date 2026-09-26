import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.Drive.EpsForm.discAttach_clusters

/-!
# Transport across a disc attached along its free boundary

`Work.Drive.EpsForm.regionEquivalent_of_discAttach` is the local model of the sideways sweep of
Pardon's Lemma 3 in the **transport** form (see `EpsForm/NOTES_discAttach.md` §1 and
`EpsForm/NOTES_discAttach_proof.md`): if

* `B ⊆ D.carrier` is open in the surface `F = P.carrier` of a parametrised torus,
* every point of the frontier of `B` lies in `A`, and
* any two frontier points of `B` are joined inside `A ∩ D.carrier`,

then the regions `A ∪ B` and `A` realise the same winding vectors: every closed curve of `F` inside
`A ∪ B` is matched, with its winding vector, by a closed curve inside `A`, and conversely (the
converse being the monotonicity `A ⊆ A ∪ B`).

The mathematical content is that every excursion of a loop into `B` lies in the embedded disc
`D.carrier`, where any two paths with the same endpoints are homotopic rel endpoints; `hconn`
supplies the replacement in `A ∩ D.carrier`, so the winding vector is unchanged.  The
accumulation points of the excursion set `γ⁻¹B` -- which are the one genuine subtlety of the
statement, since `hconn` supplies joins but not their convergence -- are handled by
`Work.Drive.EpsForm.cluster_cover` (finitely many disjoint "clusters" of frontier points with
`γ`-image inside a *thickening* `D₂` of `D`), and the assembly is
`Work.Drive.EpsForm.discAttach_clusters`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.EpsForm

theorem regionEquivalent_of_discAttach {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hB : B ⊆ D.carrier)
    (hBopen : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hcl : ∀ x : LeanEval.KnotTheory.PardonDistortion.R3, x ∈ P.carrier →
      x ∈ closure B → x ∉ B → x ∈ A)
    (hconn : ∀ p : LeanEval.KnotTheory.PardonDistortion.R3, p ∈ closure B → p ∉ B →
      ∀ q : LeanEval.KnotTheory.PardonDistortion.R3, q ∈ closure B → q ∉ B →
      JoinedIn (A ∩ D.carrier) p q) :
    Work.SurgeryInvariance.RegionEquivalent P (A ∪ B) A :=
  ⟨fun γ hγ => discAttach_clusters hB hBopen hcl hconn γ hγ,
   fun γ hγ => ⟨γ, fun t => Or.inl (hγ t), rfl⟩⟩

end Work.Drive.EpsForm
