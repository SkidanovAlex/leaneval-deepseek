import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.DomainTiling
import Submission.Work.Modular.quotient_linearIndependent
import Submission.Work.Residues.Basic
import Submission.Work.Asymptotics.linearMap_killing_idealIOdd_exists

namespace Work.Asymptotics

/-- The six classes of the elements `MpElem i` in `R ⧸ 𝓘_odd` are linearly independent.

This follows from the existence of a `ℂ`-linear map `Λ : R → (Fin 6 → ℂ)` which kills
`𝓘_odd` and is injective on the span of the six elements `MpElem i`: if a linear combination
of the classes vanishes, the combination lies in `𝓘_odd`, so `Λ` of it vanishes, and the
independence of the six images forces all coefficients to vanish. -/
theorem linearIndependent_Mp_idealIOdd :
    LinearIndependent ℂ
      (fun i : Fin 6 => Submodule.mkQ Work.Asymptotics.idealIOdd (Work.Asymptotics.MpElem i)) := by
  obtain ⟨Λ, hΛ, hLI⟩ := linearMap_killing_idealIOdd_exists
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hsum : Submodule.mkQ idealIOdd (∑ i, g i • MpElem i) = 0 := by
    rw [map_sum]; simpa only [map_smul] using hg
  have hmem : (∑ i, g i • MpElem i) ∈ idealIOdd :=
    (Submodule.Quotient.mk_eq_zero idealIOdd).mp hsum
  have h0 : Λ (∑ i, g i • MpElem i) = 0 := hΛ _ hmem
  rw [map_sum] at h0
  simp only [map_smul] at h0
  exact Fintype.linearIndependent_iff.mp hLI g h0 j

end Work.Asymptotics
