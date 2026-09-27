import ChallengeDeps
import Submission.Helpers
import Submission.Work.Mostow.assembly_of_areas

open LeanEval.Geometry.MostowRigidity
open MeasureTheory

namespace Submission

theorem mostow_rigidity (n : ℕ) (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (covol_Λ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) : ∃ g : PO n 1, ∀ γ : Γ, f γ = g * γ * g⁻¹ :=
  Work.Mostow.mostow_rigidity_of_areas n hn Γ Λ disc_Γ disc_Λ covol_Γ covol_Λ f

end Submission
