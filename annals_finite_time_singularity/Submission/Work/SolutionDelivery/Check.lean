/-
# `Work.SolutionDelivery.Check` — the wiring check

Two theorems:

* `Work.SolutionDelivery.check_theorem_1_of_inputs` — **the verbatim wiring check**: the lead's
  `Work.StabilityFar.theorem_1_of_inputs` applied to an `AssemblyInputs` and the scaling input
  produces *exactly* the challenge statement `∃ α > 0, ∃ u₀, …` of `Challenge.lean`;
* `Work.SolutionDelivery.theorem_1_of_constructed` — **the same statement, closed**: from the
  constructed-solution input package `ConstructedSolution α` alone (through
  `assemblyInputs_of_constructed` and the proved scaling `eulerScalingToUnitData_holds`).

The second is the strongest statement this area delivers: everything in it except the fields of
`ConstructedSolution α` is proved in `Work.SolutionDelivery`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SolutionDelivery.Assembly
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- The challenge statement of `theorem_1`, as a reusable `Prop`-valued abbreviation. -/
abbrev Theorem1Statement : Prop :=
  ∃ β > 0, ∃ u₀ : R3 → R3, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
    (∃ C > 0, ∀ x : R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
      ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
        (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
        IsLocalEulerEquationSolution p u₀ 1 u ∧
        (∀ T ∈ Set.Ioo 0 1, IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
        Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
          (𝓝[<] 1) Filter.atTop

/-- **The challenge statement is *definitionally* `Theorem1Statement`.**  The left-hand side
below is the conclusion of `Challenge.lean`'s `theorem_1` copied verbatim (with `ℝ³` and the
notation `∇×` unfolded); the proof `Iff.rfl` certifies that it is the same `Prop` as
`Theorem1Statement`. -/
theorem theorem1Statement_iff_challenge :
    ((∃ β > 0, ∃ u₀, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
      (∃ C > 0, ∀ x, ‖(vorticity u₀) x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p, ∃ u, (∀ t ∈ Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ β u.uncurry (univ ×ˢ Icc 0 T)) ∧
                Tendsto (fun t ↦ ∫ s in 0..t, ⨆ x, ‖(vorticity (u · s)) x‖) (𝓝[<] 1) atTop)
      ↔ Theorem1Statement) := Iff.rfl

/-- **The wiring check.**  With the assembly's `AssemblyInputs` and the scaling input
`Work.StabilityFar.EulerScalingToUnit`, `Work.StabilityFar.theorem_1_of_inputs` is *literally*
the challenge statement (up to the definitional unfolding of `Work.LWP.bkm`). -/
theorem check_theorem_1_of_inputs {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (D : Work.StabilityFar.AssemblyInputs α) (hscl : Work.StabilityFar.EulerScalingToUnit) :
    Theorem1Statement :=
  Work.StabilityFar.theorem_1_of_inputs hα hα1 D hscl

/-- **The challenge statement, closed from the constructed solution.**  The scaling input is *not*
assumed: it is proved (`Work.SolutionDelivery.eulerScalingToUnitData_holds`) from the datum
clauses of the assembly, which the construction delivers (`Work.SolutionDelivery.datum_eulerData`).

This is the statement that the lead's `Submission.theorem_1` can be wired to once the fields of
`Work.SolutionDelivery.ConstructedSolution` are instantiated by the construction. -/
theorem theorem_1_of_constructed {α : NNReal} (C : ConstructedSolution α)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) : Theorem1Statement := by
  have hstrip := stability_strip_holder_of_constructed C hα hα1
  have hbkm := stability_bkm_divergence_of_constructed C hα hα1
  obtain ⟨u₀', p', u', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    eulerScalingToUnitData_holds α (Work.LWP.biotSavart C.ω₀) C.T C.p C.u
      (C.datum_eulerData hα hα1) C.hT C.sol C.odd hstrip hbkm
  exact ⟨α, hα, u₀', h1, h2, h3, h4, p', u', h5, h6, h7, h8⟩

/-- The same conclusion, with the scaling input of `Work.StabilityFar` *derived* from the datum
clauses of the assembly (rather than assumed): the corrected scaling theorem applies to any pair
`(D.sol, D.odd, …)` whose datum is `EulerData`. -/
theorem scaled_shape_of_assembly {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (D : Work.StabilityFar.AssemblyInputs α)
    (hdata : Work.LWP.EulerData α D.u₀) :
    ∃ u₀' : R3 → R3, ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      div u₀' = 0 ∧ IsOdd u₀' ∧ IsContDiffHolder ℝ α u₀' ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀' x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)) ∧
      (∀ t ∈ Set.Ico 0 1, IsOdd (u' · t)) ∧
      IsLocalEulerEquationSolution p' u₀' 1 u' ∧
      (∀ S ∈ Set.Ioo 0 1, IsContDiffHolderOn ℝ α u'.uncurry (Set.univ ×ˢ Set.Icc 0 S)) ∧
      Filter.Tendsto (Work.LWP.bkm u') (𝓝[<] 1) Filter.atTop :=
  eulerScalingToUnitData_holds α D.u₀ D.T D.p D.u hdata D.hT D.sol D.odd
    (Work.StabilityFar.stability_strip_holder D hα hα1)
    (Work.StabilityFar.stability_bkm_divergence D)

/-- **The datum clauses of an `AssemblyInputs` *are* `Work.LWP.EulerData` of its datum.**  This is
what makes the corrected scaling input (`EulerScalingToUnitData`, which asks for `EulerData` of the
datum) applicable at the level of `AssemblyInputs` with *no* extra hypothesis. -/
theorem eulerData_of_assemblyInputs {α : NNReal} (D : Work.StabilityFar.AssemblyInputs α) :
    Work.LWP.EulerData α D.u₀ :=
  ⟨D.div_u₀, D.odd_u₀, D.cdh_u₀, D.vortDecay_u₀⟩

/-- **The scaled shape of `theorem_1` from an `AssemblyInputs` alone**: the scaling input of
`Work.StabilityFar.theorem1_shape_of_inputs_scaled` is *discharged* — it is the proved
`Work.SolutionDelivery.eulerScalingToUnitData_holds`, applied to the datum clauses that
`AssemblyInputs` already carries. -/
theorem theorem1_shape_of_inputs_scaled_proved {α : NNReal}
    (D : Work.StabilityFar.AssemblyInputs α) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    ∃ u₀' : R3 → R3, ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      div u₀' = 0 ∧ IsOdd u₀' ∧ IsContDiffHolder ℝ α u₀' ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀' x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)) ∧
      (∀ t ∈ Set.Ico 0 1, IsOdd (u' · t)) ∧
      IsLocalEulerEquationSolution p' u₀' 1 u' ∧
      (∀ S ∈ Set.Ioo 0 1, IsContDiffHolderOn ℝ α u'.uncurry (Set.univ ×ˢ Set.Icc 0 S)) ∧
      Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u' y s) x‖)
        (𝓝[<] 1) Filter.atTop :=
  scaled_shape_of_assembly hα hα1 D (eulerData_of_assemblyInputs D)

/-- **The conclusion of `Work.StabilityFar.theorem_1_of_inputs`, with the scaling input
discharged.**  This is the strongest form in which the assembly closes: from `0 < α`, `α ≤ 1` and
an `AssemblyInputs α` alone — `hscl` is not an argument. -/
theorem theorem_1_of_inputs_proved {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (D : Work.StabilityFar.AssemblyInputs α) : Theorem1Statement := by
  obtain ⟨u₀', p', u', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    theorem1_shape_of_inputs_scaled_proved D hα hα1
  exact ⟨α, hα, u₀', h1, h2, h3, h4, p', u', h5, h6, h7, h8⟩

/-- **The challenge statement from an `AssemblyInputs` whose datum is Lichtenstein–Gunther
admissible.**  This is the entry point for a caller who has assembled the
`Work.StabilityFar.AssemblyInputs` by hand (rather than through `ConstructedSolution`): the only
extra input is `EulerData` of the datum, which for the constructed datum is
`Work.SolutionDelivery.datum_eulerData`. -/
theorem theorem_1_of_assembly {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (D : Work.StabilityFar.AssemblyInputs α) (hdata : Work.LWP.EulerData α D.u₀) :
    Theorem1Statement := by
  obtain ⟨u₀', p', u', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    scaled_shape_of_assembly hα hα1 D hdata
  exact ⟨α, hα, u₀', h1, h2, h3, h4, p', u', h5, h6, h7, h8⟩

/-- **The challenge's own notation.**  The statement of `Challenge.lean`, written with the
notation of the challenge (`∇×`, `∫ s in 0..t`, `⨆ x`, `Ico`/`Ioo`/`univ`), closed from the
constructed solution.  This certifies that `Theorem1Statement` is the challenge's statement and
not merely a variant of it. -/
theorem challenge_shape_of_constructed {α : NNReal} (C : ConstructedSolution α)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    ∃ β > 0, ∃ u₀, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
      (∃ C > 0, ∀ x, ‖(vorticity u₀) x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p, ∃ u, (∀ t ∈ Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ β u.uncurry (univ ×ˢ Icc 0 T)) ∧
                Tendsto (fun t ↦ ∫ s in 0..t, ⨆ x, ‖(vorticity (u · s)) x‖) (𝓝[<] 1) atTop :=
  theorem_1_of_constructed C hα hα1

end Work.SolutionDelivery
