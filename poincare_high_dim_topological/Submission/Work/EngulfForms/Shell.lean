import Submission.Work.EngulfForms.Prelude

/-!
# A4: the shelling form `SubdivShellForm`

`Work.Engulf.SubdivShellForm N` is the `shell` field of `Work.Engulf.SubdivTools` written at the
concrete barycentric subdivision `Work.PL.Subdiv.sdIter` (see
`Submission/Work/Engulf/ToolsInstance.lean`).  It is discharged here from A4's shelling
`Work.PL.Shell.shell_form` (which packages `Work.PL.Shell.sd_iter_shelling_strong`, together with
the bridge `Work.PL.Shell.shellOrd_mem_sdIter` from the shelling order of the *single* simplex
`Δ` to the faces of the complex-level subdivision `Work.PL.Subdiv.sdIter r K hK`).

The only plumbing left is the presentation of the "previous simplices" union: the form writes it
as `⋃ j < i, ⋃ (hj : j < ord.length), simp ord[j]`, while `Work.PL.Shell.preUnion ord i` reads out
of range entries as `∅` (`Work.EngulfForms.preUnion_eq_iUnion_get`).
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms

/-- **A4**: the shelling form, from `Work.PL.Shell.shell_form`. -/
theorem shellForm (N : ℕ) : SubdivShellForm N := by
  intro r K hK Δ τ₁ hΔK h₁ h₂
  obtain ⟨ord, hnd, hprop, hcov, hmain⟩ :=
    Work.PL.Shell.shell_form r K hK Δ τ₁ (K.indep hΔK) hΔK h₁ h₂
  refine ⟨ord, hnd, hprop, hcov, fun i hi => ?_⟩
  obtain ⟨τ₁', hne, hss, heq⟩ := hmain i hi
  exact ⟨τ₁', hne, hss, by rw [preUnion_eq_iUnion_get] at heq; exact heq⟩

end Work.EngulfForms
