import Mathlib
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereCohomologyOne
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial Topology

namespace Work.Cohomology

noncomputable section

/-! ## 4. The cohomology of the sphere -/

/-- **The main computation**: `Hⁿ(Sⁿ; ℤ) ≅ ℤ` for `n ≥ 1`, for the sphere `Sⁿ ⊆ ℝ^(n+1)`. -/
theorem sphereCohomology_aux (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (singularCohomology ℤ n (sphTop (n + 1)) ≅ ModuleCat.of ℤ ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst h1
      exact sphereCohomologyOne
    · haveI hA : ContractibleSpace ↥(capA n) := contractibleSpace_capA n
      haveI hB : ContractibleSpace ↥(capB n) := contractibleSpace_capB n
      obtain ⟨e1⟩ := mvCohIso (X := sphTop (n + 1)) (capA n) (capB n)
        (isOpen_capA n) (isOpen_capB n) (capA_union_capB n) (n - 1) (by omega)
      rw [Nat.sub_add_cancel hn] at e1
      obtain ⟨e2⟩ := cohomologyIso_of_homotopyEquiv (bandHomotopyEquiv n (by omega)).some (n - 1)
      obtain ⟨e3⟩ := ih (n - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel hn] at e3
      exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

theorem sphereCohomologyTop (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (Work.Cohomology.singularCohomology ℤ n
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≅
        ModuleCat.of ℤ ℤ) := by
  obtain ⟨e'⟩ := sphereCohomology_aux n hn
  obtain ⟨e''⟩ := cohomologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq (n + 1))).toHomotopyEquiv n
  exact ⟨e'' ≪≫ e'⟩

end

end Work.Cohomology
