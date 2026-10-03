import Mathlib
import Submission.Work.Repel.Koebe.Setup

/-!
# The auxiliary function `Φ` for the winding number of an exterior univalent map

For `g : ℂ → ℂ` and a target point `ζ`, the map `v ↦ v * (g v⁻¹ - ζ)` is holomorphic on the
punctured unit disc; when `g w - w → 0` as `w → ∞` it has the finite limit `1` at `v = 0`, so it
extends to a function `Phi g ζ` holomorphic on the unit disc with `Phi g ζ 0 = 1`.

Writing `phi g v = g v⁻¹ - v⁻¹` (see `Work.Repel.Koebe.Setup`), this extension is
`Phi g ζ v = v * phi g v + 1 - v * ζ`.
-/

open Filter Topology
open scoped Topology

namespace Work.Repel.Koebe

/-- `Φ g ζ v = v * (g v⁻¹ - ζ)` for `v ≠ 0`, with the value `1` at `v = 0`; concretely
`Phi g ζ v = v * phi g v + 1 - v * ζ`. -/
noncomputable def Phi (g : ℂ → ℂ) (ζ : ℂ) : ℂ → ℂ := fun v => v * phi g v + 1 - v * ζ

@[simp]
lemma Phi_zero (g : ℂ → ℂ) (ζ : ℂ) : Phi g ζ 0 = 1 := by simp [Phi, phi_zero]

lemma Phi_apply (g : ℂ → ℂ) (ζ : ℂ) {v : ℂ} (hv : v ≠ 0) :
    Phi g ζ v = v * (g v⁻¹ - ζ) := by
  rw [Phi, phi_apply hv, mul_sub, mul_inv_cancel₀ hv]
  ring

end Work.Repel.Koebe
