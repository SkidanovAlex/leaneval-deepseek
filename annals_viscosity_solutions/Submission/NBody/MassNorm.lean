import ChallengeDeps
import Submission.NBody.Action

/-!
# The mass norm as a Euclidean norm

The mass norm of a configuration, `‖x‖ₘ = √(∑ᵢ mᵢ ‖xᵢ‖²)`, is the Euclidean norm of the
"mass-scaled" configuration `(√mᵢ • xᵢ)ᵢ`.  This file records the scaling map `massScale` and the
resulting metric properties of the mass norm (triangle inequality, homogeneity, non-degeneracy),
which are used whenever the mass geometry of the `N`-body problem is used variationally.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The mass scaling of a configuration: `x ↦ (√mᵢ • xᵢ)ᵢ`. -/
noncomputable def massScale (m : Fin N → ℝ) (x : EN E N) : EN E N :=
  WithLp.toLp 2 fun i => Real.sqrt (m i) • x i

@[simp]
lemma massScale_apply (m : Fin N → ℝ) (x : EN E N) (i : Fin N) :
    massScale m x i = Real.sqrt (m i) • x i := rfl

@[simp]
lemma massScale_zero (m : Fin N → ℝ) : massScale m (0 : EN E N) = 0 := by
  refine PiLp.ext fun i => ?_
  simp

lemma massScale_add (m : Fin N → ℝ) (x y : EN E N) :
    massScale m (x + y) = massScale m x + massScale m y := by
  refine PiLp.ext fun i => ?_
  rw [massScale_apply, PiLp.add_apply, PiLp.add_apply, massScale_apply, massScale_apply, smul_add]

lemma massScale_sub (m : Fin N → ℝ) (x y : EN E N) :
    massScale m (x - y) = massScale m x - massScale m y := by
  refine PiLp.ext fun i => ?_
  rw [massScale_apply, PiLp.sub_apply, PiLp.sub_apply, massScale_apply, massScale_apply, smul_sub]

lemma massScale_smul (m : Fin N → ℝ) (c : ℝ) (x : EN E N) :
    massScale m (c • x) = c • massScale m x := by
  refine PiLp.ext fun i => ?_
  rw [massScale_apply, PiLp.smul_apply, PiLp.smul_apply, massScale_apply, smul_comm]

lemma massScale_neg (m : Fin N → ℝ) (x : EN E N) : massScale m (-x) = -massScale m x := by
  refine PiLp.ext fun i => ?_
  rw [massScale_apply, PiLp.neg_apply, PiLp.neg_apply, massScale_apply, smul_neg]

/-- **The mass norm is the Euclidean norm of the mass-scaled configuration.** -/
theorem weightedNorm_eq_norm_massScale {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x : EN E N) :
    ‖x‖_[m] = ‖massScale m x‖ := by
  rw [weightedNorm, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [massScale_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (hm i)]

/-- The mass norm is non-negative. -/
theorem weightedNorm_nonneg (m : Fin N → ℝ) (x : EN E N) : 0 ≤ ‖x‖_[m] := Real.sqrt_nonneg _

/-- The triangle inequality for the mass norm. -/
theorem weightedNorm_add_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x y : EN E N) :
    ‖x + y‖_[m] ≤ ‖x‖_[m] + ‖y‖_[m] := by
  rw [weightedNorm_eq_norm_massScale hm, weightedNorm_eq_norm_massScale hm,
    weightedNorm_eq_norm_massScale hm, massScale_add]
  exact norm_add_le _ _

/-- The triangle inequality for the mass distance. -/
theorem weightedNorm_sub_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x y z : EN E N) :
    ‖x - z‖_[m] ≤ ‖x - y‖_[m] + ‖y - z‖_[m] := by
  have h := weightedNorm_add_le hm (x - y) (y - z)
  rwa [sub_add_sub_cancel] at h

/-- Homogeneity of the mass norm. -/
theorem weightedNorm_smul {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (c : ℝ) (x : EN E N) :
    ‖c • x‖_[m] = |c| * ‖x‖_[m] := by
  rw [weightedNorm_eq_norm_massScale hm, weightedNorm_eq_norm_massScale hm, massScale_smul,
    norm_smul, Real.norm_eq_abs]

/-- The mass norm vanishes exactly at the origin (for strictly positive masses). -/
theorem weightedNorm_eq_zero_iff {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) (x : EN E N) :
    ‖x‖_[m] = 0 ↔ x = 0 := by
  rw [weightedNorm_eq_norm_massScale (fun i => (hm i).le), norm_eq_zero]
  constructor
  · intro h
    refine PiLp.ext fun i => ?_
    have hi : Real.sqrt (m i) • x i = 0 := by
      have h1 : (massScale m x) i = (0 : EN E N) i := congrFun (congrArg WithLp.ofLp h) i
      simpa using h1
    exact (smul_eq_zero.mp hi).resolve_left (ne_of_gt (Real.sqrt_pos.mpr (hm i)))
  · intro h
    rw [h, massScale_zero]

end Submission.NBody
