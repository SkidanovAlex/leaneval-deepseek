/-
  Area G4b, final assembly: `G4_bdd_dx_proved` (the frozen `WilkiesDesign.CG.G4_bdd_dx`, with
  the definable-choice hypothesis `G1_choice` added as a leading hypothesis).

  The proof reduces to finiteness of the exceptional set `badSet f s` of `G4_bdd_dx`:
  * `badSet_finite_zero` (in `Submission/Work/WilG4b/GlueAux.lean`) covers `n = 0`;
  * `Work.WilG4b.badSet_finite_of_one_le` (in `Submission/Work/WilG4b/AsmAux.lean`) covers
    `n ≥ 1` by the contradiction argument of BNZ `lem:uniforly-bdd-Fx`;
  * `conclusion_of_finite_badSet` (in `Submission/Work/WilG4b/GlueAux.lean`) transforms
    finiteness of `badSet` into the claimed boundedness of `∂₀ f` off a finite exceptional set.

  The `*Aux.lean` modules are the supporting development of this area; they were moved into
  this directory from the scratch directory `Submission/Work/WilG4bF/` (which survives on
  disk but is imported by nothing here).
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.GlueAux
import Submission.Work.WilG4b.AsmAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Classical MeasureTheory Filter
open scoped Topology

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

theorem G4_bdd_dx_proved (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hchoice : ∀ (F p n : ℕ), ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (X : Set (Fin (p + n) → ℝ)), X ∈ S.Ω F D (p + n) →
        ∃ f : (Fin p → ℝ) → (Fin n → ℝ),
          (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
          {z : Fin (p + n) → ℝ | ∀ j : Fin n,
              z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j}
            ∈ S.Ω a (b.eval D) (p + n))
    {n F D : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (n + 1 + 1))
    (hI : ∀ z ∈ WilkiesDesign.openCube (n + 1), f z ∈ Set.Ioo (0 : ℝ) 1)
    (hy : ∃ s : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ,
      ∀ y ∈ WilkiesDesign.openCube n, Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        ∀ i : Fin n, |fderiv ℝ f (Fin.cons x y) (Pi.single i.succ 1)| ≤ B) :
    ∃ s : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ,
      ∀ y ∈ WilkiesDesign.openCube n, Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        |fderiv ℝ f (Fin.cons x y) (Pi.single 0 1)| ≤ B := by
  obtain ⟨s, hs⟩ := hy
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact conclusion_of_finite_badSet f s (badSet_finite_zero s)
  · exact conclusion_of_finite_badSet f s
      (badSet_finite_of_one_le S hcd hder hchoice f hf hI hs (by omega))

end Work.WilG4b
