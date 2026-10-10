import Mathlib.GroupTheory.Nilpotent
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- The lower central series of `P` (the series `γ₀ = ⊤`, `γ_{ν+1} = ⁅γ_ν, ⊤⁆`) is
contained in the descending `p`-central series `P₀ = ⊤`, `P_{ν+1} = P_ν^p ⁅P_ν, ⊤⁆`.

Indeed `γ_{ν+1} = ⁅γ_ν, ⊤⁆ ≤ ⁅P_ν, ⊤⁆ ≤ P_ν^p ⁅P_ν, ⊤⁆ = P_{ν+1}` as soon as
`γ_ν ≤ P_ν`, and `γ₀ = ⊤ = P₀`. -/
theorem lowerCentralSeries_le_pCentralSeries (p : ℕ) (P : Type*) [Group P] (ν : ℕ) :
    (⊤ : Subgroup P).lowerCentralSeries ν ≤ Work.Shrinking.pCentralSeries p P ν := by
  induction ν with
  | zero => simp
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ, Work.Shrinking.pCentralSeries_succ,
      Work.Shrinking.pCentralStep]
    exact le_trans (Subgroup.commutator_mono ih le_rfl) le_sup_right

end Work.ProP
