import Mathlib
import Submission.Work.EKLComp.Core

/-!
# Auxiliary objects for `ent_jacobs` (Jacobs' theorem)

`HcondFam μ A m` is the conditional entropy `∫ ∑_i -E(1_{A_i}|m) log E(1_{A_i}|m) dμ` of a
finite indexed family of sets `A`, and `hPartCond μ T Q m` is its Fekete infimum along the
joins `⋁_{k<N} T^{-k} Q`.

These organise the proof of `ent_jacobs`:

* `hPart_le_hPartCond` : `hPart μ T Q ≤ hPartCond μ T Q (invariants T)`;
* `hPartCond_eq_integral_hPartKernel` :
  `hPartCond μ T Q (invariants T) = ∫ x, hPart (condExpKernel μ (invariants T) x) T Q ∂μ`;
* `ent_generating_jacobs` : the Kolmogorov–Sinai generating-sequence theorem;
* the final assembly in `Submission/Work/EKLComp/ent_jacobs.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type*} [mX : MeasurableSpace X]

/-- Conditional Shannon entropy `H_μ(A | m) = ∫ ∑_i -E(1_{A_i}|m) log E(1_{A_i}|m) dμ`. -/
noncomputable def HcondFam (μ : Measure X) {ι : Type*} [Fintype ι] (A : ι → Set X)
    (m : MeasurableSpace X) : ℝ :=
  ∫ x, ∑ i, Real.negMulLog (condExp m μ ((A i).indicator (fun _ => (1 : ℝ))) x) ∂μ

/-- `hPartCond μ T Q m = inf_N (1/N) H_μ(⋁_{k<N} T^{-k}Q | m)`. -/
noncomputable def hPartCond (μ : Measure X) (T : X → X) (Q : FinPart X)
    (m : MeasurableSpace X) : ℝ :=
  letI : MeasurableSpace X := mX
  ⨅ N : ℕ, HcondFam μ (joinSets T Q (N + 1)) m / ((N : ℝ) + 1)

end Work.EKLComp

