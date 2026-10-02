import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.norm_symm_sub_le
import Submission.Work.MRMT.Found.surjective_of_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.MRMT.Found

/-- A locally uniform limit of homeomorphisms of `ℂ` which are `O(1/‖z‖)`-close to the identity
at infinity is itself surjective.

The limit `φ` inherits both properties needed by `surjective_of_decay`: it is continuous, being a
locally uniform limit of continuous maps, and it inherits the decay bound `‖φ z - z‖ ≤ Cd / ‖z‖`
pointwise, since `‖Fn n z - z‖ ≤ Cd / ‖z‖` for every `n`. -/
theorem surjective_of_tendstoLocallyUniformly_of_decay {Fn : ℕ → ℂ ≃ₜ ℂ} {φ : ℂ → ℂ} {Cd Rd : ℝ}
    (hRd : 1 ≤ Rd) (hCd : 0 ≤ Cd)
    (hdec : ∀ n : ℕ, ∀ z : ℂ, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖)
    (hconv : TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ)) φ Filter.atTop) :
    Function.Surjective φ := by
  have hcont : Continuous φ :=
    hconv.continuous ((Filter.Eventually.of_forall fun n => (Fn n).continuous).frequently)
  refine surjective_of_decay (C := Cd) (R := Rd) hcont fun z hz => ?_
  have hpoint : Tendsto (fun n : ℕ => (Fn n : ℂ → ℂ) z) Filter.atTop (𝓝 (φ z)) :=
    hconv.tendsto_comp hcont.continuousAt tendsto_const_nhds
  have hnorm : Tendsto (fun n : ℕ => ‖(Fn n : ℂ → ℂ) z - z‖) Filter.atTop (𝓝 ‖φ z - z‖) :=
    (hpoint.sub tendsto_const_nhds).norm
  exact le_of_tendsto' hnorm fun n => hdec n z hz

end Work.MRMT.Found
