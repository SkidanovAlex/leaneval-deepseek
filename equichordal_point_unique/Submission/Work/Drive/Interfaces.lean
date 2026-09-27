import Mathlib
import Submission.UnifDeps
import Submission.Work.SimplyConnected.ABS.period_interface
import Submission.Work.Parabolic.uniformization_of_greenFunctionAt
import Submission.Work.UnitGreen.normalize

/-!
# Drive interfaces (written by the driver, 2026-09-23)

The drive replaces the topological input G0 (`SimplyConnectedSpace X` from `Hom(π₁ X, ℝ) = 0`)
by an analytic statement that is exactly what the hyperbolic branch consumes:

* `PeriodsHold X` — on `X`, every harmonic `E` on `X ∖ {z₀}` with a unit logarithmic pole at `z₀`
  has all conjugate periods in `2πℤ` (`Work.SimplyConnected.ABS.PeriodsAreMultiplesOfTwoPi`).

Area A proves `PeriodsHold X` from `¬ CompactSpace X` and `Hom(π₁ X, ℝ) = 0`.
`hyperbolic_case_of_periods` below (proved) turns it plus a Green function into the challenge
conclusion.  Area B (the parabolic case) may assume `PeriodsHold X`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Every harmonic function on `X ∖ {z₀}` with a unit logarithmic pole at `z₀` has all its
conjugate periods in `2πℤ`. -/
def PeriodsHold (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    Prop :=
  ∀ (z₀ : X) (E : X → ℝ) (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})),
    Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E →
    Work.SimplyConnected.ABS.PeriodsAreMultiplesOfTwoPi E hEharm

/-- **The hyperbolic branch, from the periods.** -/
theorem hyperbolic_case_of_periods (hX : ¬ CompactSpace X) (hP : PeriodsHold X) {z₀ : X}
    {E : X → ℝ} (hE : Work.Parabolic.IsGreenFunctionAt (X := X) z₀ E) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  obtain ⟨E', hE'⟩ := Work.UnitGreen.exists_isUnitGreenFunctionAt_of_isGreenFunctionAt hX hE
  have hharm : Submission.HarmonicOnX E' (Set.univ \ {z₀}) := hE'.1.harmonic
  have hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E' := by
    obtain ⟨C, V, hV, hb⟩ := hE'.2
    exact ⟨C, V, hV, fun x hx _ hne => hb x hx hne⟩
  obtain ⟨Φ, hΦ, -, hmod, hlp⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods hharm hpole (hP z₀ E' hharm hpole)
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE'.1 hΦ hmod hlp

/-- `X` carries a (weak) Green function: a positive harmonic function on `X ∖ {z₀}` with a unit
logarithmic pole at `z₀`.  No decay at the ideal boundary is asked for. -/
def HasWeakGreen (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    Prop :=
  ∃ (z₀ : X) (E : X → ℝ), (∀ x : X, x ≠ z₀ → 0 < E x) ∧
    Submission.HarmonicOnX E (Set.univ \ {z₀}) ∧
    Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E

/-- The challenge conclusion. -/
def Conclusion (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane)

/-- **Final wiring**: the challenge conclusion from the three areas, passed as hypotheses
(A: periods; W: the weak-Green case; O: the case with no weak Green function). -/
theorem uniformization_of_parts (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hA : PeriodsHold X)
    (hW : PeriodsHold X → HasWeakGreen X → Conclusion X)
    (hO : PeriodsHold X → ¬ HasWeakGreen X → Conclusion X) :
    Conclusion X := by
  by_cases h : HasWeakGreen X
  · exact hW hA h
  · exact hO hA h

end Work.Drive
