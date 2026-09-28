import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero

/-!
# Theta functions of a lattice (`Work.HP.Sig2.ThetaDefs`)

For a `ℤ`-submodule `Λ ⊆ ι → ℝ` (with `ι` finite) we define

* `theta Λ s t = ∑' z : Λ, exp(-π ‖z - t‖² / s²)`, the (Euclidean, shifted) theta function;
* `rhoD Λ s = ∑' w : dualLat Λ, exp(-π s² ‖w‖²)`, the dual theta sum `ρ_s(Λ*)`.

These are the quantities appearing in Banaszczyk's transference theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- Theta function of a lattice: `θ_Λ(s,t) = Σ_{z ∈ Λ} exp(-π ‖z - t‖² / s²)`. -/
def theta (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) (t : ι → ℝ) : ℝ :=
  ∑' z : Λ, Real.exp (-(Real.pi / s ^ 2) * (rNorm ((z : ι → ℝ) - t)) ^ 2)

/-- The dual theta sum: `ρ_Λ(s) = Σ_{w ∈ Λ*} exp(-π s² ‖w‖²)`. -/
def rhoD (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) : ℝ :=
  ∑' w : dualLat Λ, Real.exp (-(Real.pi * s ^ 2) * (rNorm (w : ι → ℝ)) ^ 2)

end Work.HP
