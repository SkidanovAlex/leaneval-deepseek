import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

/-!
# The major arcs as `Finset`s of the circle

`ArcDefs.lean` records Tao's arc sets `Σ_A`, `Σ_{⊆A}`, `Σ_{≤k}`, `Σ_{(A₀)}` as `Set`s of the circle
`𝕋 = ℝ/ℤ`, which is the right notion for *support* statements (`HasFreqSupport h hh (arcSet α ε)`,
the hypotheses of `BandLimitedL2Ortho.lean`), but not for *sums*: Tao's major arc system is
`f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`, a sum over the (finite) set of arc points.

This file supplies the `Finset` versions: `sigmaSubAFinset A` (the points `a/Q_A`, `a < Q_A`) and
`sigmaAFinset A` (those of *exact* denominator `Q_A`, i.e. `gcd (a, Q_A) = 1`).  The companions
(`mem_sigmaAFinset`, `coe_sigmaAFinset`, `coe_sigmaSubAFinset`, `card_sigmaSubAFinset`) identify them
with the corresponding `Set`s of `ArcDefs.lean` and compute their cardinalities.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- Tao's `Σ_{⊆ A} = 𝕋[Q_A]`, the `Q_A`-torsion points of the circle, as a `Finset`. -/
noncomputable def sigmaSubAFinset (A : Finset ℕ) : Finset Circle :=
  (Finset.range (QA A)).image (fun a : ℕ => arcPt (QA A) (a : ℤ))

/-- Tao's `Σ_A`, the points of the circle of *exact* denominator `Q_A`, as a `Finset`. -/
noncomputable def sigmaAFinset (A : Finset ℕ) : Finset Circle :=
  ((Finset.range (QA A)).filter (fun a : ℕ => Nat.Coprime a (QA A))).image
    (fun a : ℕ => arcPt (QA A) (a : ℤ))

end Work.BourgainPlan.IonescuWainger
