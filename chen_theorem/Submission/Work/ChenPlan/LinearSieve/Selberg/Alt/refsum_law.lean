import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab

/-!
# The canonical model for the reference sum `Σ_{k ≥ 1} e^{-S_k}`

`cY` is the extremal reference variable of `Selberg/Alt/vocab.lean`, transported to the
canonical product space `canonM = ⊗_{n} Exp(1)` (iid standard exponentials).  The plan
(see `Selberg/scratch_alt/PLAN_ALT.md`) is:

* the law `cNu` of `cY` is a fixed point of `Y =_d U (1 + Y)`, `U` uniform on `(0,1)`;
* hence `ν(Iic θ) = θ · ∫ (1+t)⁻¹ dν(t)` for `θ ≤ 1`;
* the Laplace transform of `ν` solves `λ φ(λ) = ∫_0^λ e^{-s} φ(s) ds`, so `φ(λ) = e^{-A(λ)}`
  with `A(λ) = ∫_0^λ (1-e^{-s})/s ds`;
* hence `∫ (1+t)⁻¹ dν(t) = lim_{λ→∞} λ φ(λ) = e^{-γ}`,
  and `ν(Iic θ) = θ e^{-γ}`.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The standard exponential law (rate `1`) on `ℝ`. -/
noncomputable def expLaw : Measure ℝ := ProbabilityTheory.expMeasure 1

instance instExpLawProb : IsProbabilityMeasure expLaw :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos

/-- The canonical iid standard exponential product space `ℝ^ℕ`. -/
noncomputable def canonM : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => expLaw)

instance instCanonMProb : IsProbabilityMeasure canonM := by
  rw [canonM]; infer_instance

/-- Partial sums of the coordinates. -/
def cSum (x : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, x i

/-- The reference sum `Σ_{k ≥ 1} e^{-S_k}` on the canonical space. -/
noncomputable def cY (x : ℕ → ℝ) : ℝ := ∑' k : ℕ, Real.exp (-(cSum x (k + 1)))

/-- The shift `(x₀, x₁, …) ↦ (x₁, x₂, …)`. -/
def cshift (x : ℕ → ℝ) : ℕ → ℝ := fun i => x (i + 1)

/-- The event `{x | cY x < θ}`. -/
def cSet (θ : ℝ) : Set (ℕ → ℝ) := {x | cY x < θ}

/-- The law of the reference sum. -/
noncomputable def cNu : Measure ℝ := canonM.map cY

/-- The law of `u = e^{-E}` for `E` standard exponential: uniform on `(0,1)`. -/
noncomputable def cUnif : Measure ℝ := expLaw.map (fun t : ℝ => Real.exp (-t))

/-- Prepending a coordinate: the inverse of `x ↦ (x 0, cshift x)`. -/
def ccons (p : ℝ × (ℕ → ℝ)) : ℕ → ℝ := fun i => Nat.casesOn i p.1 p.2

lemma cSum_eq_partialSum (x : ℕ → ℝ) (k : ℕ) :
    cSum x k = partialSum (fun i => x i) k := rfl

lemma cY_eq_refSum (x : ℕ → ℝ) : cY x = refSum (fun i => x i) := rfl

lemma cSet_eq_refSumLt (θ : ℝ) :
    cSet θ = refSumLt (fun i (x : ℕ → ℝ) => x i) θ := rfl

lemma measurable_cshift : Measurable cshift := by
  rw [measurable_pi_iff]
  intro i
  simpa [cshift] using measurable_pi_apply (i + 1)

lemma measurable_ccons : Measurable ccons := by
  rw [measurable_pi_iff]
  intro i
  cases i with
  | zero => simpa [ccons] using measurable_fst
  | succ n =>
      have h : Measurable (fun p : ℝ × (ℕ → ℝ) => p.2 n) :=
        (measurable_pi_apply n).comp measurable_snd
      simpa [ccons] using h

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
