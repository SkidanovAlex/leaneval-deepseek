/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): the interface Props of the
  complex Puiseux development.

  These are exactly the statements of the sibling holes of this area
  (`exists_analytic_root_of_simple`, `sqfree_branches`, `exists_cluster_factor`), packaged as
  `Prop`s so that they can be passed around as hypotheses.  In the final assembly each of them
  is instantiated by its proven sibling.
-/
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- Statement shape of `exists_analytic_root_of_simple` (the analytic implicit function
statement, in the form needed here). -/
def SimpleRootLift : Prop :=
  ∀ (P : Polynomial (ℂ → ℂ)), P.Monic → HolCoeffs P 0 → ∀ α : ℂ,
    (Pz P 0).eval α = 0 → (Pz P 0).derivative.eval α ≠ 0 →
    ∃ (ζ : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ AnalyticOnNhd ℂ ζ (Metric.ball 0 ρ) ∧ ζ 0 = α ∧
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, (Pz P z).eval (ζ z) = 0

/-- Statement shape of `sqfree_branches` (complex Puiseux, square-free case). -/
def SqfreeBranches : Prop :=
  ∀ {m : ℕ} (P : Polynomial (ℂ → ℂ)), P.Monic → P.natDegree = m → HolCoeffs P 0 →
    ∀ ρ₀ > (0 : ℝ), SimpleRootsOn P {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ₀} →
    ∃ (η : Fin m → ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      (∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball 0 ρ)) ∧ FactoredOn P m.factorial η ρ

/-- Statement shape of `exists_cluster_factor` (analytic Hensel splitting). -/
def ClusterSplitting : Prop :=
  ∀ {m : ℕ} (P : Polynomial (ℂ → ℂ)), P.Monic → P.natDegree = m → HolCoeffs P 0 →
    ∀ (α : ℂ) (k : ℕ), (Pz P 0).rootMultiplicity α = k → 0 < k →
    ∃ G : Polynomial (ℂ → ℂ), G.Monic ∧ G.natDegree = k ∧ HolCoeffs G 0 ∧
      Pz G 0 = (X - C α) ^ k ∧ ∃ H : Polynomial (ℂ → ℂ), H.Monic ∧ P = G * H

/-- **The general complex Puiseux statement.** Every monic polynomial with holomorphic
coefficients at `0` has, after some ramification `s = u ^ N`, roots that are single-valued
holomorphic functions of `u`. -/
def ComplexPuiseux : Prop :=
  ∀ {m : ℕ} (P : Polynomial (ℂ → ℂ)), P.Monic → P.natDegree = m → HolCoeffs P 0 →
    ∃ (N : ℕ) (η : Fin m → ℂ → ℂ) (ρ : ℝ), 0 < N ∧ 0 < ρ ∧
      (∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball 0 ρ)) ∧ FactoredOn P N η ρ

end Work.WilC4aP
