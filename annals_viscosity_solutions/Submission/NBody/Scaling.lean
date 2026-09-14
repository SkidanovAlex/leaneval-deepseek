import ChallengeDeps
import Submission.NBody.Virial
import Mathlib

/-!
# Scaling (homogeneity) of the Newtonian potential and of the force field

The Newtonian potential is homogeneous of degree `-1`:

    `U m (c • x) = c⁻¹ * U m x`   for `c > 0`,

and its gradient (the Newtonian force field) is homogeneous of degree `-2`:

    `∇(U m)(c • x) = (c²)⁻¹ • ∇(U m)(x)`,  `∇ₘ(U m)(c • x) = (c²)⁻¹ • ∇ₘ(U m)(x)`,

for every collision-free `x`.  These are the homogeneity identities used, e.g., in Chazy's
lemma (the force decays like `t⁻²` along a hyperbolic motion) and in the definition of the
configurational measure `μ = √I · U`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The mutual distance scales linearly under a dilation of the configuration. -/
lemma r_smul (x : EN E N) (i j : Fin N) (c : ℝ) :
    r (c • x) i j = |c| * r x i j := by
  rw [r_eq_norm_sub, r_eq_norm_sub, PiLp.smul_apply, PiLp.smul_apply, ← smul_sub,
    norm_smul, Real.norm_eq_abs]

/-- Collision-freeness is preserved by dilations with a non-zero factor. -/
lemma withoutCollisions_smul {x : EN E N} (hx : WithoutCollisions x) {c : ℝ} (hc : c ≠ 0) :
    WithoutCollisions (c • x) := by
  intro i j hij
  rw [r_smul]
  exact mul_ne_zero (abs_ne_zero.mpr hc)
    (by simpa [r_ne_zero_iff] using hx i j hij)

/-- **Homogeneity of the Newtonian potential**: `U` is homogeneous of degree `-1`. -/
theorem U_smul (m : Fin N → ℝ) (c : ℝ) (x : EN E N) :
    U m (c • x) = |c|⁻¹ * U m x := by
  rw [U_eq_pairFinset, U_eq_pairFinset, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [r_smul, mul_inv_rev]
  ring

/-- **Homogeneity of the Newtonian force field**: `∇U` is homogeneous of degree `-2`. -/
theorem gradient_U_smul (m : Fin N → ℝ) {c : ℝ} (hc : 0 < c) (x : EN E N)
    (hx : WithoutCollisions x) :
    gradient (U m) (c • x) = ((c ^ 2)⁻¹) • gradient (U m) x := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hxc : WithoutCollisions (c • x) := withoutCollisions_smul hx hc0
  refine PiLp.ext fun k => ?_
  have key : ∀ j ∈ Finset.univ.erase k,
      (m k * m j * (‖(c • x) j - (c • x) k‖ ^ 3)⁻¹) • ((c • x) j - (c • x) k)
        = (c ^ 2)⁻¹ • ((m k * m j * (‖x j - x k‖ ^ 3)⁻¹) • (x j - x k)) := by
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    have hR : ‖x j - x k‖ ≠ 0 := by
      have h := hx j k hjk
      rwa [r_eq_norm_sub] at h
    have hsub : (c • x) j - (c • x) k = c • (x j - x k) := by
      rw [PiLp.smul_apply, PiLp.smul_apply, ← smul_sub]
    have hnorm : ‖(c • x) j - (c • x) k‖ = c * ‖x j - x k‖ := by
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    rw [hnorm, hsub, mul_pow, mul_inv_rev, smul_smul, smul_smul]
    congr 1
    field_simp
  rw [gradient_U_coord m (c • x) hxc k, Finset.sum_congr rfl key, ← Finset.smul_sum,
    ← gradient_U_coord m x hx k, ← PiLp.smul_apply]

/-- **Homogeneity of the mass-weighted force field** `∇ₘ U`: it is homogeneous of degree `-2`. -/
theorem weightedGrad_U_smul (m : Fin N → ℝ) {c : ℝ} (hc : 0 < c) (x : EN E N)
    (hx : WithoutCollisions x) :
    weightedGrad m (U m) (c • x) = ((c ^ 2)⁻¹) • weightedGrad m (U m) x := by
  refine PiLp.ext fun k => ?_
  have h1 : (weightedGrad m (U m) (c • x)) k = (m k)⁻¹ • (gradient (U m) (c • x)) k := by
    simp [weightedGrad]
  have h2 : (weightedGrad m (U m) x) k = (m k)⁻¹ • (gradient (U m) x) k := by
    simp [weightedGrad]
  have h3 : ((c ^ 2)⁻¹ • weightedGrad m (U m) x) k
      = (c ^ 2)⁻¹ • (weightedGrad m (U m) x) k := PiLp.smul_apply ..
  have h4 : (gradient (U m) (c • x)) k = (c ^ 2)⁻¹ • (gradient (U m) x) k := by
    rw [gradient_U_smul m hc x hx, PiLp.smul_apply]
  rw [h1, h3, h2, h4, smul_smul, smul_smul, mul_comm]

end Submission.NBody
