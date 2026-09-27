import Mathlib
import Submission.Work.EKLRelCross.atomic_defs

/-!
# `Work.EKLRelCross.conjBox_mass_tendsto` — the masses of the contracted boxes converge

For a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical subgroup `U ≤ SL₃(ℝ)`,
a leafwise system `ν` on a conull set `X'`, and an exponent vector `t₀` whose diagonal flow
*contracts* `U` (i.e. `(aDiag t₀)ⁿ u (aDiag t₀)⁻ⁿ → 1` for every `u ∈ U`), the masses of the
contracted boxes

`conjBox U (n t₀) = (aDiag t₀)ⁿ · B₁^U · (aDiag t₀)⁻ⁿ`

converge, at every `x ∈ X'`, to the mass of the singleton `{1}`.

Mathematically this is just continuity from above for the finite measure `ν x`: the family
`n ↦ conjBox U (n t₀)` is antitone (`Work.EKLRelCross.conjBox_antitone`), its intersection is
`{1}` (`Work.EKLRelCross.conjBox_iInter_eq_singleton`, i.e. `box_iInter_conjBox`), and every
term is contained in `B₁^U`, which has `ν x`-mass `1` by the normalisation field of
`IsLeafwise`.  The final passage from `ℝ≥0∞`-valued masses to `ℝ` is the composition with
`ENNReal.toReal`, which is continuous at the (finite) limit `ν x {1}`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- **The masses of the contracted boxes tend to the mass of `{1}`.**  Continuity from above
along the antitone family `n ↦ conjBox U (n t₀)`, whose intersection is `{1}` and all of whose
members sit inside the normalising box `B₁^U` of finite `ν x`-mass. -/
theorem conjBox_mass_tendsto {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹)
      Filter.atTop (nhds (1 : Work.EKLContract.SL3)))
    {x : Work.EKLContract.X3} (hx : x ∈ X') :
    Filter.Tendsto
      (fun n : ℕ => (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))).toReal)
      Filter.atTop (nhds (ν x {1}).toReal) := by
  -- the antitone family of contracted boxes
  set A : ℕ → Set SL3 := fun n => Work.EKLC6Core.conjBox U (((n:ℝ)) • t0) with hA
  have hanti : Antitone A := conjBox_antitone hU hcontr
  have hInter : (⋂ n, A n) = {1} := conjBox_iInter_eq_singleton hU hcontr
  -- each box is Borel, hence null-measurable for the leafwise measure `ν x`
  have hmeas : ∀ n : ℕ, NullMeasurableSet (A n) (ν x) := fun n =>
    (Work.EKLC6Core.conjBox_measurable hU (((n:ℝ)) • t0)).nullMeasurableSet
  -- the `n = 0` box is the normalising box `B₁^U`, of `ν x`-mass `1`
  have hA0 : A 0 = Box1 U := by
    rw [hA]
    simp
  have hnorm : ν x (Box1 U) = 1 := hL.normalised x hx
  have hfin : ∃ n : ℕ, ν x (A n) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    rw [hA0, hnorm]
    exact ENNReal.one_ne_top
  -- continuity from above
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [hInter] at hlim
  -- the limit `ν x {1}` is finite, since it is bounded by `ν x (A 0) = 1`
  have hle : ν x ({1} : Set SL3) ≤ 1 := by
    have h := measure_mono (Set.iInter_subset A 0) (μ := ν x)
    rwa [hInter, hA0, hnorm] at h
  have hne : ν x ({1} : Set SL3) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  -- `toReal` is continuous at the finite limit
  exact (ENNReal.tendsto_toReal hne).comp hlim

end Work.EKLRelCross
