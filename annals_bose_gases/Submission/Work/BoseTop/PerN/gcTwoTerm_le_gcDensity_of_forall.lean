import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseTop.PerN

/-- If every admissible particle number satisfies the per-state two-term bound
(measured against `L³`), then the two-term value bounds the truncated
grand-canonical energy density: `gcSet v (8πAρ) (2ρ) L` is the set of values
`boxEnergy N L v - (8πAρ)N` over admissible `N`, it is nonempty (`N = 0`),
and all of its elements dominate `gcTwoTerm A Cw s ρ · L³`. -/
theorem gcTwoTerm_le_gcDensity_of_forall {v : EuclideanSpace ℝ (Fin 3) → ℝ} {A Cw s ρ L : ℝ}
    (hL : 0 < L) (hρmax : 0 ≤ 2 * ρ)
    (h : ∀ N : ℕ, Submission.BoseGases.gcAdmissible (2 * ρ) L N →
      Submission.BoseGases.gcTwoTerm A Cw s ρ * L ^ 3 ≤
        Submission.BoseGases.boxEnergy N L v - (8 * Real.pi * A * ρ) * (N : ℝ)) :
    Submission.BoseGases.gcTwoTerm A Cw s ρ ≤
      Submission.BoseGases.gcDensity v (8 * Real.pi * A * ρ) (2 * ρ) L := by
  have hmain : Submission.BoseGases.gcTwoTerm A Cw s ρ * L ^ 3 ≤
      Submission.BoseGases.gcBox v (8 * Real.pi * A * ρ) (2 * ρ) L :=
    Submission.BoseGases.le_gcBox_of_forall
      (v := v) (μ := 8 * Real.pi * A * ρ) (ρmax := 2 * ρ) (L := L)
      hρmax hL.le (by
        rintro y ⟨N, hN, rfl⟩
        exact h N hN)
  rw [Submission.BoseGases.gcDensity, le_div_iff₀ (pow_pos hL 3)]
  exact hmain

end Work.BoseTop.PerN
