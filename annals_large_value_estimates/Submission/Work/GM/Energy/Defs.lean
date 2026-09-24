import Mathlib
import Submission.GM.Interfaces

/-!
# Energy area: shared vocabulary (GM §11)

This module is the entry point for the `Energy` area. It re-exports the definitions and
statements of `Submission/GM/Interfaces.lean` that the area's lemmas are stated against:

* `Submission.LargeValues.bumpW`, `M`, `smoothedPoly` (the smoothed Dirichlet polynomial `D_N`),
* `Submission.GM.Rfun` (GM's `R(v) = Σ_{t∈W}|v|^{it}`),
* `Submission.GM.energy` (GM's additive energy `E(W)`),
* `Submission.GM.Separated` (δ-separation),
* `Submission.GM.HBStatement` (Heath-Brown, Theorem 1.6),
* `Submission.GM.EnergyStatement` (GM Proposition 11.1), the goal of this area.
-/

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

namespace Work.GM.Energy

/-- Alias for the smoothed Dirichlet polynomial `D(t) = Σ_{n∈[N,2N]} w(n/N) b_n n^{it}`. -/
noncomputable def D (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ := Submission.LargeValues.smoothedPoly N b t

/-- GM's `R(v) = Σ_{t∈W} |v|^{it}`. -/
noncomputable def R (W : Finset ℝ) (v : ℝ) : ℂ := Submission.GM.Rfun W v

/-- GM's additive energy `E(W)`. -/
noncomputable def E (W : Finset ℝ) : ℕ := Submission.GM.energy W

end Work.GM.Energy
