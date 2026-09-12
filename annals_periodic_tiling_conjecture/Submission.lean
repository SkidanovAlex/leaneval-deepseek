/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.ContinuousClean.LiftClean
import Submission.Commons.PeriodicTiling.theorem_1_4
import Submission.Commons.PeriodicTiling.corollary_1_6_of_theorem_1_4
/-!
# Main Statements from A counterexample to the periodic tiling conjecture

We formalise the statements of the main results from R. Greenfeld and T. Tao,
`A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024.
-/

namespace Submission

open _root_.PeriodicTilingConjecture
open _root_.PeriodicTilingConjecture.IsAperiodicContinuousTilingEquation
open _root_.PeriodicTilingConjecture.IsAperiodicTilingEquation
set_option autoImplicit false

namespace PeriodicTilingConjecture

open Filter Bornology MeasureTheory

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

/-- Convert an aperiodic tiling equation from the Commons formulation to the
`PeriodicTilingConjecture` formulation of `ChallengeDeps`. -/
private theorem commonsAperiodicToPTC {F : Set G}
    (h : Commons.PeriodicTiling.IsAperiodicTilingEquation F) :
    IsAperiodicTilingEquation F := by
  constructor
  · exact h.solvable
  · intro A hA
    exact h.aperiodic A hA

/-- Convert an aperiodic tiling equation from the `PeriodicTilingConjecture`
formulation to the Commons formulation. -/
private theorem ptcAperiodicToCommons {F : Set G}
    (h : IsAperiodicTilingEquation F) :
    Commons.PeriodicTiling.IsAperiodicTilingEquation F := by
  constructor
  · exact h.solvable
  · intro A hA
    exact h.aperiodic A hA

/-- Convert the Commons continuous aperiodic tiling equation (as produced by the
safe local lift) to the `PeriodicTilingConjecture` formulation. -/
private theorem continuousCleanToPTC {d : ℕ} {σ : Set (Fin d → ℝ)}
    (h : Submission.ContinuousClean.IsAperiodicContinuousTilingEquation σ) :
    IsAperiodicContinuousTilingEquation σ := by
  constructor
  · rcases h.solvable with ⟨Λ, hΛ⟩
    exact ⟨Λ, hΛ⟩
  · intro Λ hΛ
    exact h.aperiodic Λ hΛ

/--
Statement of Theorem 1.4 (Counterexample to Conjecture 1.2, I):

There exists a finite abelian group `G₀` and a finite non-empty `F ⊆ ℤ² × G₀` such that
`F` forms an aperiodic tiling equation.
-/
theorem theorem_1_4 : ∃ (G₀ : Type) (_ : AddCommGroup G₀) (_ : Finite G₀),
    ∃ F : Set (ℤ × ℤ × G₀), F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F := by
  rcases Commons.PeriodicTiling.theorem_1_4 with ⟨G₀, hGadd, hGfin, F, hFfin, hFne, hF⟩
  exact ⟨G₀, hGadd, hGfin, F, hFfin, hFne, commonsAperiodicToPTC hF⟩

/--
Statement of Corollary 1.6 (Counterexample to Conjecture 1.2, II):

For all sufficiently large `d`, there exists a finite non-empty `F ⊆ ℤᵈ` such that
`F` forms an aperiodic tiling equation.
-/
theorem corollary_1_6 : ∀ᶠ d in atTop, ∃ (F : Set (Fin d → ℤ)),
    F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F := by
  have h16c := Commons.PeriodicTiling.corollary_1_6_of_theorem_1_4
    Commons.PeriodicTiling.theorem_1_4
  refine h16c.mono ?_
  intro d hd
  rcases hd with ⟨F, hFfin, hFne, hF⟩
  exact ⟨F, hFfin, hFne, commonsAperiodicToPTC hF⟩

variable {d : ℕ}

/--
Statement of Corollary 1.7 (Counterexample to Conjecture 1.3):

For all sufficiently large `d`, there exists a bounded measurable set `σ ⊆ ℝᵈ` of positive
measure such that `σ` forms an aperiodic continuous tiling equation.
-/
theorem corollary_1_7 : ∀ᶠ d in atTop, ∃ σ : Set (Fin d → ℝ), IsBounded σ ∧ MeasurableSet σ ∧
    0 < volume σ ∧ IsAperiodicContinuousTilingEquation σ := by
  have hpos : ∀ᶠ d in atTop, 0 < d := eventually_gt_atTop 0
  refine (corollary_1_6.and hpos).mono ?_
  intro d hd
  rcases hd with ⟨⟨F, hFfin, hFne, hF⟩, hdpos⟩
  have hFc : Commons.PeriodicTiling.IsAperiodicTilingEquation F := ptcAperiodicToCommons hF
  obtain ⟨σ, hb, hm, hp, hcont⟩ :=
    Submission.ContinuousClean.lift_discrete_aperiodic_clean hdpos hFfin hFne hFc
  exact ⟨σ, hb, hm, hp, continuousCleanToPTC hcont⟩

end PeriodicTilingConjecture

end Submission
