import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.StepFiberEnds

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

theorem StepCellParam (S : SOMin) (p N F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (C : Finset (Set (Fin (p + N) → ℝ))), IsCylDecomp (p + N) C →
      (∀ κ ∈ C, κ ∈ S.Ω F0 D (p + N)) →
      ∀ (κ : Set (Fin (p + N) → ℝ)), κ ∈ C → κ ⊆ inCubeSet p N →
      ∀ (Λ : Set (Fin p → ℝ)), (∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ κ) →
        ∃ Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ),
          (∀ j : Fin N,
            famGraph (fun l t => Ψ l t j) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Ψ l t ∈ openCube N) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Fin.append l (Ψ l t) ∈ κ) ∧
          (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ → ∃ t ∈ openCube N, Ψ l t = y) := by
  sorry

end Work.WilG4c
