import Mathlib
import Submission.Work.Drive.BoxParityDefs

namespace Work.Drive

open Set

/-- The interior of the unit box `[0,1]^{m+1}` is the open unit box `(0,1)^{m+1}`.

`EuclideanSpace ℝ (Fin (m+1))` is `PiLp 2 (fun _ => ℝ)`, so we transfer the statement along the
homeomorphism `PiLp.homeomorph 2 (fun _ => ℝ) : Amb m ≃ₜ (Fin (m+1) → ℝ)`; there the box is the
product `∏ᵢ [0,1]`, whose interior is `∏ᵢ (0,1)` by `interior_pi_set` and `interior_Icc`. -/
theorem interior_unitBox (m : ℕ) :
    interior (Submission.Drive.unitBox m) =
      {x : Work.Drive.Amb m | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} := by
  have hbox : Submission.Drive.unitBox m =
      (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)) ⁻¹'
        (Set.univ.pi (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) := by
    ext x
    simp only [Submission.Drive.unitBox, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Icc]
    exact Iff.rfl
  rw [hbox, ← Homeomorph.preimage_interior, interior_pi_set Set.finite_univ, interior_Icc]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo]
  exact Iff.rfl

end Work.Drive
