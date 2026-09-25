/-
The weighted `L²` vocabulary of the *perturbed* basic estimate (`pertBasicEstimate`).

This small module collects the two definitions that the interface between
`Work.NN.Assemble.pertHarmonicVanishes` and the perturbed Kohn--Morrey estimate
`Work.NN.Assemble.pertBasicEstimate` needs:

* `wt n K` — the quadratic weight `z ↦ K * Σ_j ‖z j‖²` of the target statement,
  in the flat model `ℂⁿ = Fin n → ℂ` (note that the norm of the Pi-type is the
  sup-norm, so this weight is *not* `K‖z‖²`; it is nevertheless a smooth strictly
  plurisubharmonic weight with the same complex Hessian `K·δ`);
* `wN2J φ F` — the weighted `L²` square norm of a perturbed `(0,2)`-form, sampled
  on the standard basis `eb n j` of `ℂⁿ`.
-/
import Mathlib
import Submission.Work.NN.Assemble.L2Forms

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.NN.Assemble

/-- The quadratic weight `z ↦ K * Σ_j ‖z j‖²` of the statement. -/
def wt (n : ℕ) (K : ℝ) : Cn n → ℝ := fun z => K * ∑ j, ‖z j‖ ^ 2

/-- The weighted `L²` square norm of a perturbed `(0,2)`-form `F`, sampled on the
standard basis of `ℂⁿ`: `∫ (1/2) Σ_{j,k} ‖F z (e_j) (e_k)‖² e^{-φ}`. -/
def wN2J {n : ℕ} (φ : Cn n → ℝ) (F : Cn n → Cn n → Cn n → ℂ) : ℝ :=
  ∫ z, ((1 / 2) * ∑ j, ∑ k, ‖F z (eb n j) (eb n k)‖ ^ 2) * Real.exp (-(φ z))

end Work.NN.Assemble
