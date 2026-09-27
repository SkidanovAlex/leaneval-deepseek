import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.USCBasic

/-!
# C4c — definitions for the entropy upper semicontinuity input

The frozen `P_USC` quantifies over **all** `t : Fin 3 → ℝ`, constant ones included.  For constant
`t` one has `aDiag t = 1`, and its first clause (a uniform finite bound on `ent ν id` over all
probabilities carried by `K`) is **false**.  The maximiser argument of C4c however only uses
`t = a0v = ![-2,1,1]`, which is non-constant, so we work with the corrected statement `P_USC'`,
obtained from `P_USC` by adding the hypothesis `∃ i j, t i ≠ t j`.  `P_USC'` is exactly what
EKL §9 (Prop 9.2 + Cor 9.3) proves.

`AtomSmallEntropy` is EKL Prop 9.2 in the exact shape needed by the two halves of `P_USC'`.

This module contains **definitions and elementary partition lemmas only** (it is imported by the
two halves `ErgMax.USC_finite` and `ErgMax.USC_limsup`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

set_option linter.style.haveILetI false

/-- `P_USC` with the necessary non-degeneracy hypothesis on `t` (`aDiag t ≠ 1`). -/
def P_USC' : Prop :=
  ∀ (t : Fin 3 → ℝ), (∃ i j : Fin 3, t i ≠ t j) → ∀ (K : Set X3), IsCompact K →
    (∀ x ∈ K, aDiag t • x ∈ K) →
    (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : Measure X3, IsProbabilityMeasure ν → ν K = 1 →
        MeasurePreserving (fun x : X3 => aDiag t • x) ν ν →
        ent ν (fun x : X3 => aDiag t • x) ≤ C) ∧
    (∀ (νseq : ℕ → Measure X3) (νlim : Measure X3), (∀ n, IsProbabilityMeasure (νseq n)) →
        IsProbabilityMeasure νlim → (∀ n, νseq n K = 1) →
        (∀ n, MeasurePreserving (fun x : X3 => aDiag t • x) (νseq n) (νseq n)) →
        (∀ f : X3 →ᵇ ℝ,
          Tendsto (fun n => ∫ x, f x ∂(νseq n)) atTop (𝓝 (∫ x, f x ∂νlim))) →
        limsup (fun n => ent (νseq n) (fun x : X3 => aDiag t • x)) atTop ≤
          ent νlim (fun x : X3 => aDiag t • x))

/-- **EKL Prop 9.2**, in the shape consumed by the two halves of `P_USC'`: an `AtomSmall`
partition computes the entropy of every invariant probability carried by `K`. -/
def AtomSmallEntropy (t : Fin 3 → ℝ) (K : Set X3) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : FinPart X3, AtomSmall K δ P →
    ∀ ν : Measure X3, IsProbabilityMeasure ν → ν K = 1 →
      MeasurePreserving (fun x : X3 => aDiag t • x) ν ν →
      ent ν (fun x : X3 => aDiag t • x)
        = ENNReal.ofReal (hPart ν (fun x : X3 => aDiag t • x) P)

/-- `hPart μ T P ≤ Hfam μ P.parts`: the `N = 0` term of the defining infimum is `Hfam μ P`. -/
theorem hPart_le_Hfam {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (P : FinPart X) : hPart μ T P ≤ Hfam μ P.parts := by
  have h := Work.EKLComp.Core.hPart_le_avg μ T P 0
  have h' : hPart μ T P ≤ Hfam μ (joinSets T P 1) := by simpa using h
  have hcongr : Hfam μ (joinSets T P 1)
      = Hfam μ (fun v : Fin 1 → Fin P.n => P.parts (v 0)) := by
    congr 1
    funext v
    exact Work.EKLComp.Core.joinSets_one T P v
  have h2 : Hfam μ (fun v : Fin 1 → Fin P.n => P.parts (v 0)) = Hfam μ P.parts := by
    let e : (Fin 1 → Fin P.n) ≃ Fin P.n :=
      { toFun := fun v => v 0
        invFun := fun i => fun _ => i
        left_inv := by intro v; funext k; fin_cases k; rfl
        right_inv := by intro i; rfl }
    have := Work.EKLComp.Core.Hfam_equiv μ e P.parts
    simpa [e] using this
  rw [hcongr, h2] at h'
  exact h'

/-- An `IsMPart` from a `FinPart`. -/
theorem isMPart_parts {X : Type*} [MeasurableSpace X] (P : FinPart X) :
    Work.EKLComp.Core.IsMPart P.parts :=
  ⟨P.measurable, P.disjoint, P.cover⟩

end

end Work.EKLComp.ErgMax
