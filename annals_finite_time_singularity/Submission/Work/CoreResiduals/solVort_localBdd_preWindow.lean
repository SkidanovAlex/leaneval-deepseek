import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.exists_eps_min_lam
import Submission.Work.ConstructionInstance.Reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **Local uniform boundedness of the constructed vorticity near every time of `preWindow T`.**

On `preWindow T` the boxed bound `λ̄(t)·‖ω(x,t)‖ ≤ M` holds (`solVort_bdd`), and `λ̄` is locally
bounded below by a positive constant (`exists_eps_min_lam`).  Combining the two gives, around any
`t₀ ∈ preWindow T`, a symmetric neighbourhood on which `‖ω(x,t)‖` is uniformly bounded by
`M / m`, `m > 0` the local lower bound of `λ̄`. -/
theorem solVort_localBdd_preWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : Work.CoreResiduals.R3,
        ‖Work.ConstructionInstance.solVort P y t‖ ≤ M := by
  intro t₀ ht₀
  obtain ⟨ε, hεpos, hsub, m, hmpos, hmle⟩ :=
    exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hεpos, P.M / m, ?_⟩
  intro t ht y
  have htIcc : t ∈ Set.Icc (t₀ - ε) (t₀ + ε) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have htpre : t ∈ Work.ConstructionInstance.preWindow P.T := hsub htIcc
  have hbdd := Work.ConstructionInstance.solVort_bdd P t htpre y
  have hmle' : m ≤ P.lam t := hmle t htIcc
  rw [le_div_iff₀ hmpos]
  calc ‖Work.ConstructionInstance.solVort P y t‖ * m
      ≤ ‖Work.ConstructionInstance.solVort P y t‖ * P.lam t :=
        mul_le_mul_of_nonneg_left hmle' (norm_nonneg _)
    _ = P.lam t * ‖Work.ConstructionInstance.solVort P y t‖ := mul_comm _ _
    _ ≤ P.M := hbdd

end Work.CoreResiduals
