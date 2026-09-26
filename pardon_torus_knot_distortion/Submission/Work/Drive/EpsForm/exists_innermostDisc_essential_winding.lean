import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.EpsForm.exists_innermostDisc_standardCurve

namespace Work.Drive.EpsForm

/-- **The crux of the workspace's coherence question: a *dirty* innermost-disc datum with an essential boundary curve whose winding has both components non-zero.**

`Work.Drive.CleansDiscsW` (the legacy unclaused cut-and-paste input) demands a weak bounding disc for the boundary of *every* `InnermostDisc`.  By the *proved* `Work.Drive.innermostDiscWindingDichotomy_of_disjoint` a datum whose boundary has *both* winding components non-zero can only be *dirty* (some interior curve touching `alpha`), and by the *proved* `Work.Drive.compressing_winding_dichotomyW` such a datum admits no weak bounding disc at all; so this statement is exactly `¬ Work.Drive.CleansDiscsW Work.CoreTopology.standard`.  If it holds, then `CleansDiscsAllW`, `CleansDiscsAll` and both fields of `Work.BoxShrink.ClassicalInputs` (the ledger `Submission/Work/BoxShrink/ledger.lean`) are vacuous, and `Work.Drive.EpsForm.arcBodyOff_holds` follows vacuously via the proved `Work.Drive.EpsForm.arcBodyOff_of_forall_not_cleansDiscsW` together with the transport of this refutation along an ambient homeomorphism.

WHAT IS KNOWN (read `Submission/Work/Drive/EpsForm/NOTES_satisfiability.md`, Part V, before starting; it is in this directory):
* clean datums (all interior curves disjoint from `alpha`) are excluded by the proved `innermostDiscWindingDichotomy_of_disjoint`;
* the cone `e z = |z| * (standardCurve 1 1 (arg z))` over `alpha = standardCurve 1 1` is injective, has `e '' (open ball) ∩ carrier` equal to a *single* arc, and fails `covers` (its only admissible circles have winding `(1,0)`/`(0,-1)`);
* **every single-arc dirty datum is impossible** (the two closing curves both have non-zero winding — NOTES §5); do NOT chase a single-arc shape.

THE SURVIVING SHAPE (NOTES §6, numerically scanned): `e '' (open ball) ∩ carrier` is a union of **at least two** arcs, all contained in the range of **one** inessential simple closed curve `kappa` with `range kappa ⊆ range e`.  Candidate family: the cones over `alpha = standardCurve 1 1` from `p = (2, b, 2 - b / sqrt 2)`; for every `b` the tangency equation `2 cos t + 1 - 2 cos^2 t - b cos t sin t - c sin t = 0` (with `c = 2 - b/sqrt 2`) has the *antipodal* solutions `t = pi/4, 5 pi/4`, and for `b > 0` a numeric scan of 720 angles gives two or three interior intersection points for a large range of `t`.  The remaining work: check `e` injective, compute the interior arcs exactly, find `kappa` (its lifted displacements must total `(0,0)` so that it is inessential), and formalize the covering identity.

DO NOT declare this false without a machine-checked obstruction: no datum-refutation exists in the tree, and the informal report `lemma-Drive_cleansDiscsAllW.md` was never formalized. -/
theorem exists_innermostDisc_essential_winding :
    ∃ (S : Set LeanEval.KnotTheory.PardonDistortion.R3)
      (D : Work.InnermostDisk.InnermostDisc Work.CoreTopology.standard S),
      (∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α, (L.winding).1 ≠ 0) ∧
      (∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α, (L.winding).2 ≠ 0) := by
  obtain ⟨S, D, hα⟩ := Work.Drive.EpsForm.exists_innermostDisc_standardCurve
  -- The explicit lift `t ↦ (t, t)` of `D.α`, with winding vector `(1, 1)`.
  have hkey : ∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α,
      L.winding = (1, 1) := by
    let L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α :=
      { Θ := fun t => t
        Φ := fun t => t
        contΘ := continuous_id
        contΦ := continuous_id
        lifts := by
          intro t
          show (Work.CoreTopology.standard).psi t t = D.α.γ t
          rw [hα]
          simp [Work.CoreTopology.standardCurve] }
    refine ⟨L, ?_⟩
    have hw := Work.CoreTopology.LiftOf.winding_congr
      (P := Work.CoreTopology.standard) (γ := Work.CoreTopology.standardCurve 1 1)
      (P' := Work.CoreTopology.standard) (γ' := D.α)
      (Work.CoreTopology.standardCurveLift 1 1) L
      (fun t => by simp [L, Work.CoreTopology.standardCurveLift])
      (fun t => by simp [L, Work.CoreTopology.standardCurveLift])
    rw [hw, Work.CoreTopology.standardCurveLift_winding]
    norm_num
  exact ⟨S, D, (by obtain ⟨L, hL⟩ := hkey; exact ⟨L, by rw [hL]; norm_num⟩),
    (by obtain ⟨L, hL⟩ := hkey; exact ⟨L, by rw [hL]; norm_num⟩)⟩

end Work.Drive.EpsForm
