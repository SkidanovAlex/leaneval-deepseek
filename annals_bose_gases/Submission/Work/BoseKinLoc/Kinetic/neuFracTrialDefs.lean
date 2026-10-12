import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS's `eq:DefT` trial functional** for the box Neumann fraction, as a function of the
trial `g`:

`T(φ,g) = ∫_Λ φ² − 2a²∫_Λ φ g + a²(Σ_k∫_Λ (∂_k g)² + a²∫_Λ g²)`,  `Λ = lamBox ℓ u`.

Every integral is a Bochner integral over `Λ = lamBox ℓ u`; the derivative is the Fréchet
derivative in the standard orthonormal frame `kcStdBasis`. -/
def trialVal (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) (g : ℝ³ → ℝ) : ℝ :=
  (∫ z in lamBox ℓ u, (φ z) ^ 2)
    - 2 * a2 * (∫ z in lamBox ℓ u, φ z * g z)
    + a2 * ((∑ k : Fin 3, ∫ z in lamBox ℓ u,
              (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
            + a2 * (∫ z in lamBox ℓ u, (g z) ^ 2))

/-- The **trial set** of `neuFrac`: the values `T(φ,g)` as `g` ranges over the globally
smooth compactly supported trials. -/
def trialSet (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) : Set ℝ :=
  {c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      c = trialVal ℓ a2 u φ g}

/-- The trial set restricted to trials in the `L²(Λ)`-ball of radius `M`:
`{T(φ,g) : g smooth, compactly supported, ∫_Λ g² ≤ M²}`. -/
def trialBallSet (ℓ a2 M : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) : Set ℝ :=
  {c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      (∫ z in lamBox ℓ u, (g z) ^ 2) ≤ M ^ 2 ∧ c = trialVal ℓ a2 u φ g}

/-- `neuFrac` is by definition the `sInf` of the trial set. -/
theorem neuFrac_eq_sInf_trialSet (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ = sInf (trialSet ℓ a2 u φ) := rfl

/-- The trial `g = 0` has value `∫_Λ φ²`. -/
lemma trialVal_zero (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) :
    trialVal ℓ a2 u φ (fun _ => (0 : ℝ)) = ∫ z in lamBox ℓ u, (φ z) ^ 2 := by
  simp [trialVal, integral_zero]

/-- The trial `g = 0` is admissible: `∫_Λ φ² ∈ trialSet ℓ a² u φ`. -/
lemma zero_mem_trialSet (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) :
    (∫ z in lamBox ℓ u, (φ z) ^ 2) ∈ trialSet ℓ a2 u φ :=
  ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, (trialVal_zero ℓ a2 u φ).symm⟩

/-- The trial `g = 0` is admissible in the ball of every radius `M ≥ 0`. -/
lemma zero_mem_trialBallSet {M : ℝ} (hM : 0 ≤ M) (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) :
    (∫ z in lamBox ℓ u, (φ z) ^ 2) ∈ trialBallSet ℓ a2 M u φ :=
  ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, by
    have : (∫ z in lamBox ℓ u, ((fun _ => (0 : ℝ)) z) ^ 2) = 0 := by simp
    rw [this]; exact pow_nonneg hM 2,
    (trialVal_zero ℓ a2 u φ).symm⟩

/-- The restricted ball is contained in the full trial set. -/
lemma trialBallSet_subset_trialSet (ℓ a2 M : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) :
    trialBallSet ℓ a2 M u φ ⊆ trialSet ℓ a2 u φ := by
  rintro c ⟨g, hg, hgs, -, hc⟩
  exact ⟨g, hg, hgs, hc⟩

/-- Boundedness below of the trial set, from global square integrability of `φ`
(the hypotheses of `Work.BoseKinLoc.NeuFrac.bddBelow_trialSet`, restated for `trialSet`). -/
lemma bddBelow_trialSet' {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : ℝ³ => (φ z) ^ 2)) :
    BddBelow (trialSet ℓ a2 u φ) :=
  Work.BoseKinLoc.NeuFrac.bddBelow_trialSet ha2 u hφ

/-- Boundedness below of the trial set, from square integrability of `φ` **on the box**
(the box-restricted strengthening, restated for `trialSet`). -/
lemma bddBelow_trialSet_of_integrableOn' {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : ℝ³ => (φ z) ^ 2)
      (MeasureTheory.volume.restrict (lamBox ℓ u))) :
    BddBelow (trialSet ℓ a2 u φ) :=
  Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn ha2 u hφ

/-- Boundedness below of the restricted trial ball, inherited from the full trial set. -/
lemma bddBelow_trialBallSet {ℓ a2 M : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : ℝ³ => (φ z) ^ 2)) :
    BddBelow (trialBallSet ℓ a2 M u φ) :=
  (bddBelow_trialSet' ha2 u hφ).mono (trialBallSet_subset_trialSet ℓ a2 M u φ)

end Work.BoseKinLoc.Kinetic
