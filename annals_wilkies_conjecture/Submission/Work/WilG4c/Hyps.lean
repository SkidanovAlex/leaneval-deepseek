/-
  WilG4c — other areas' holes that the §§5.2–5.5 reductions consume, restated as named
  `abbrev`s with the area parameters instantiated.  Each `abbrev` is *definitionally* the
  verbatim statement of the corresponding frozen hole, so passing `<hole>_proved` to it is
  the intended integration step.  Nothing here is a new mathematical assumption: these are
  exactly `CG.G0_calculus`, `CG.G1_choice` and `CG.G4_bdd_dx` with their leading arguments
  (`S`, and for the choice lemma `hcd`) already supplied.
-/
import Submission.Work.WilG4c.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Area G4b's hole `CG.G4_bdd_dx`**, verbatim with `S`, `hcd`, `hder` fixed. If the
`y`-partials of a definable `f : I_x × I_y^{n-1} → I` are bounded in `y` for all but finitely
many `x`, then so is the `x`-partial; `Fin.cons x y` is the point with `x` first. -/
abbrev BddDxHyp (S : SOMin) : Prop :=
  ∀ {n F D : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ), graphOf f ∈ S.Ω F D (n + 1 + 1) →
    (∀ z ∈ openCube (n + 1), f z ∈ Set.Ioo (0 : ℝ) 1) →
    (∃ s : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ, ∀ y ∈ openCube n,
      Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        ∀ i : Fin n, |(fderiv ℝ f (Fin.cons x y)) (Pi.single i.succ 1)| ≤ B) →
    ∃ s : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ, ∀ y ∈ openCube n,
      Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        |(fderiv ℝ f (Fin.cons x y)) (Pi.single 0 1)| ≤ B

/-- **Area G1's hole `CG.G1_choice`**, verbatim with `S` and `hcd` fixed: definable choice
with sharp format and degree bounds. -/
abbrev ChoiceHyp (S : SOMin) : Prop :=
  ∀ (F p n : ℕ), ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (D : ℕ) (X : Set (Fin (p + n) → ℝ)), X ∈ S.Ω F D (p + n) →
      ∃ f : (Fin p → ℝ) → (Fin n → ℝ),
        (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
        {z : Fin (p + n) → ℝ | ∀ j : Fin n,
            z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j} ∈ S.Ω a (b.eval D) (p + n)

/-- **Area G0's hole `CG.G0_calculus`**, verbatim with `S` fixed: the `Ω`-formula calculus. -/
abbrev G0Hyp (S : SOMin) : Prop :=
  ∀ {n : ℕ} (s : OShape n) (F : ℕ), ∃ a : ℕ, ∀ d : s.Data,
    s.Good S F d → s.realize d ∈ S.Ω a (s.deg d) n

end Work.WilkG4c
