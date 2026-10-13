/-
  WilG4a — the corrected target of BNZ Corollary 5.5 in `ℝ`-coordinates.

  The lead's audit (`sources/wilkiesG4/wilkies_g4_audit.md`, 2026-10-11) shows that the frozen
  `CG.F1Affine` is FALSE at `p = 1`: requiring every chart to satisfy `0 < β l` at every
  `l ∈ Λ` leaves no chart that can be "switched off" at the parameters where the cell structure
  degenerates.  The corrected statement `Work.WilG4a.F1AffineW` (lead-owned,
  `F1AffineW.lean`) allows a chart to be degenerate (`β l = 0`, i.e. the constant chart
  `t ↦ α l`) at some parameters, while still requiring the `ε`-cover to be achieved by
  non-degenerate charts.

  This file is the `ℝ`-coordinate copy `F1Affine1W` of `F1AffineW` (`I = (0,1)` and
  `iteratedDeriv` for `openCube 1` and the iterated Fréchet derivative), mirroring the relation
  between `F1Affine1` and `F1Affine`.
-/
import Submission.Work.WilG4a.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-- **BNZ Cor 5.5, corrected, in `ℝ`-coordinates.**  As `F1Affine1`, except that a chart may be
degenerate (`β l = 0`) at some parameters; the `ε`-cover must be achieved by non-degenerate
charts (`0 < αβ.2 l`).  The per-chart conditions include that the image of the chart lies in
`I`, which is what makes the degenerate case meaningful. -/
def F1Affine1W (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ αβ ∈ Φ, graphOf αβ.1 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          graphOf αβ.2 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          ∀ l ∈ Λ, 0 ≤ αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧
            (∀ t ∈ I, αβ.1 l + αβ.2 l * t ∈ I) ∧
            ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) I ∧
              ∀ m ≤ r, ∀ t ∈ I,
                |iteratedDeriv m (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) t| ≤ 1) ∧
        ∀ l ∈ Λ, ∀ x ∈ I, ∃ αβ ∈ Φ, 0 < αβ.2 l ∧ ∃ t ∈ I,
          |αβ.1 l + αβ.2 l * t - x| < ε

end Work.WilG4a
