/-
  WilG1 — delivery module.

  This file assembles the two frozen holes of area G1 (`Submission/Work/Wilkies/CG/Spec.lean`):
  * `G1_choice`        — effective definable choice with sharp bounds (BNZ §2.3);
  * `G1_generic_smooth` — the set on which a definable function is not `C^k` has empty interior.

  Both are proved in this directory without touching any `sorry`: the choice theorem is
  `Work.WilG1.Choice.G1_choice_proved` (sharp cell decomposition + the selection set
  `Work.WilG1.selSet` + the cell-fibre structure of `WilG4a.isCell_fiber`), and the generic
  smoothness theorem is the finite cover `Work.WilG1.Cell.smooth_k_cover` followed by
  finite-union thinness `Work.WilG1.Cell.thin_union`.
-/
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Choice.G1_choice_proved
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Cell.thin_union

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Classical

namespace WilkiesDesign.CG

open WilkiesDesign

/-- **G1_choice** (BNZ §2.3): definable choice with `Ω`-bounds, from sharp cell decomposition. -/
theorem G1_choice_proved (S : SOMin) (hcd : S.SharpCD) (F p n : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin (p + n) → ℝ)),
      X ∈ S.Ω F D (p + n) →
      ∃ f : (Fin p → ℝ) → (Fin n → ℝ),
        (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
        {z : Fin (p + n) → ℝ | ∀ j : Fin n,
            z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j} ∈ S.Ω a (b.eval D) (p + n) :=
  Work.WilG1.Choice.G1_choice_proved S hcd F p n

/-- **G1_generic_smooth**: a definable function is `C^k` off a set with empty interior. -/
theorem G1_generic_smooth_proved (S : SOMin) (hcd : S.SharpCD) {n F D : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : graphOf f ∈ S.Ω F D (n + 1)) (k : ℕ) :
    interior {x | ¬ ContDiffAt ℝ k f x} = ∅ := by
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ := Work.WilG1.Cell.smooth_k_cover hcd f hf (k := k)
  have hcov : interior {x : Fin n → ℝ | ¬ ContDiffAt ℝ k f x} ⊆ interior (⋃ i, A i) :=
    interior_mono hsub
  have hthin : interior (⋃ i, A i) = ∅ := Work.WilG1.Cell.thin_union hcd m a b D A hA hint
  rw [hthin] at hcov
  exact Set.eq_empty_of_subset_empty hcov

end WilkiesDesign.CG
