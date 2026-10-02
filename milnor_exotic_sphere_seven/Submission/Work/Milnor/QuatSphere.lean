import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The unit quaternions as `S³`

This file sets up the 3-sphere as the unit sphere inside the quaternions, together with the
clutching maps `(x, y) ↦ (x, x^k * y * x⁻¹)` used in Milnor's construction of exotic `7`-spheres
(Milnor, *On manifolds homeomorphic to the 7-sphere*, Ann. of Math. 64 (1956)).

The map `x ↦ (y ↦ x^k * y * x⁻¹)` is a group homomorphism `S³ → Diff(S³)`; it is the clutching
function of the `S³`-bundle over `S⁴` whose total space is Milnor's manifold `M_k`.
-/

open scoped Manifold ContDiff Topology
open Metric (sphere)

namespace Submission.Milnor

noncomputable section

/-- The 3-sphere, realised as the unit sphere of the quaternions. -/
abbrev QS3 : Type := sphere (0 : Quaternion ℝ) 1

instance : Fact (Module.finrank ℝ (Quaternion ℝ) = 3 + 1) :=
  ⟨by rw [Quaternion.linearIsometryEquivTuple.finrank_eq]; simp⟩

/-- The norm of a unit quaternion is one. -/
theorem norm_coe (x : QS3) : ‖(x : Quaternion ℝ)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using x.2

/-- The clutching function of Milnor's construction, as a quaternion valued map:
`(x, y) ↦ x^k * y * x⁻¹`, where `x, y` are unit quaternions. -/
def clutchVal (k : ℤ) (x y : QS3) : Quaternion ℝ :=
  (x : Quaternion ℝ) ^ k * (y : Quaternion ℝ) * (x : Quaternion ℝ)⁻¹

theorem norm_clutchVal (k : ℤ) (x y : QS3) : ‖clutchVal k x y‖ = 1 := by
  rw [clutchVal, norm_mul, norm_mul, norm_zpow, norm_inv, norm_coe, norm_coe]
  simp

/-- The clutching function, as a map `S³ × S³ → S³`. -/
def clutch (k : ℤ) (p : QS3 × QS3) : QS3 :=
  ⟨clutchVal k p.1 p.2, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_clutchVal k p.1 p.2⟩

end

end Submission.Milnor
