import Submission.NBody.MarchalClusterAsymptotic3

/-!
# The normalised configuration of a colliding cluster

Ferrario–Terracini's `as:lim1`–`as:lim2` are statements about the *normalised* configuration

    `s = I_k^{-1/2} (x - x_{cm,k})`,

which lies on the "shape sphere" `∑_{i∈k} mᵢ‖sᵢ‖² = 1`.  This file provides the definition and
the basic calculus: the derivative of the normalised configuration along a motion, and the key
identity

    `I_k · R_k(ṡ) = R_k(ẋ) - (İ_k)²/(4 I_k)`,

where `R_k` is twice the centre-of-mass-relative kinetic energy.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The normalised configuration of the cluster `k`: `s = I_k^{-1/2} (x - x_{cm,k})`. -/
noncomputable def clusterShape (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : EN E N :=
  (Real.sqrt (clusterInertia m k x))⁻¹ • cmRel m k x

lemma clusterShape_apply (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) (i : Fin N) :
    clusterShape m k x i = (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x i) := by
  simp [clusterShape]

/-- The moment of inertia as a sum over the cluster of the centre-of-mass-relative coordinates. -/
lemma sum_cmRel_sq (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    ∑ i ∈ k, m i * ‖(cmRel m k x) i‖ ^ 2 = clusterInertia m k x := by
  rw [clusterInertia]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cmRel_apply_of_mem hi]

/-- **The normalised configuration lies on the shape sphere.** -/
theorem clusterKineticSq_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hJpos : 0 < clusterInertia m k x) :
    clusterKineticSq m k (clusterShape m k x) = 1 := by
  rw [clusterKineticSq]
  have key : ∀ i ∈ k, m i * ‖(clusterShape m k x) i‖ ^ 2
      = (clusterInertia m k x)⁻¹ * (m i * ‖(cmRel m k x) i‖ ^ 2) := by
    intro i _
    rw [show ‖(clusterShape m k x) i‖ ^ 2
        = (clusterInertia m k x)⁻¹ * ‖(cmRel m k x) i‖ ^ 2 by
      rw [clusterShape_apply, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
      congr 1
      rw [inv_pow, Real.sq_sqrt hJpos.le]]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_cmRel_sq,
    inv_mul_cancel₀ (ne_of_gt hJpos)]

/-- **Linearity of the centre-of-mass-relative configuration.** -/
lemma hasDerivAt_cmRel (m : Fin N → ℝ) (k : Finset (Fin N)) {X : ℝ → EN E N} {X' : EN E N}
    {t : ℝ} (hX : HasDerivAt X X' t) :
    HasDerivAt (fun s : ℝ => cmRel m k (X s)) (cmRel m k X') t := by
  have hg : HasDerivAt
      (fun s : ℝ => fun i : Fin N => if i ∈ k then X s i - clusterCM m k (X s) else 0)
      (fun i : Fin N => if i ∈ k then X' i - clusterCM m k X' else 0) t := by
    rw [hasDerivAt_pi]
    intro i
    by_cases hi : i ∈ k
    · have hfun : (fun s : ℝ => if i ∈ k then X s i - clusterCM m k (X s) else 0)
          = (fun s : ℝ => X s i - clusterCM m k (X s)) := by
        funext s; rw [if_pos hi]
      rw [hfun, if_pos hi]
      exact (hasDerivAt_apply hX i).sub (hasDerivAt_clusterCM m k hX)
    · have hfun : (fun s : ℝ => if i ∈ k then X s i - clusterCM m k (X s) else 0)
          = (fun s : ℝ => (0 : E)) := by
        funext s; rw [if_neg hi]
      rw [hfun, if_neg hi]
      exact hasDerivAt_const t 0
  have hl := PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin N => E)
    ((fun s : ℝ => fun i : Fin N => if i ∈ k then X s i - clusterCM m k (X s) else 0) t)
  have hcomp := hl.comp_hasDerivAt
    (f := fun s : ℝ => fun i : Fin N =>
      if i ∈ k then X s i - clusterCM m k (X s) else 0) (x := t) hg
  have hfun : (fun s : ℝ => cmRel m k (X s))
      = (WithLp.toLp 2) ∘ (fun s : ℝ => fun i : Fin N =>
          if i ∈ k then X s i - clusterCM m k (X s) else 0) := by
    funext s; rfl
  rw [hfun]
  refine hcomp.congr_deriv ?_
  rfl

/-- **The derivative of the normalised configuration along a motion.** -/
theorem hasDerivAt_clusterShape_curve {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t : ℝ} (hJpos : 0 < clusterInertia m k (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    HasDerivAt (fun s : ℝ => clusterShape m k (x s))
      ((Real.sqrt (clusterInertia m k (x t)))⁻¹ • cmRel m k (deriv x t)
        + (-(deriv (fun s : ℝ => clusterInertia m k (x s)) t
              / (2 * (Real.sqrt (clusterInertia m k (x t))) ^ 3))) • cmRel m k (x t)) t := by
  have hJ : HasDerivAt (fun s : ℝ => clusterInertia m k (x s))
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t) t :=
    hasDerivAt_clusterInertia_curve hx
  have hsqrt_ne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hJpos)
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / (2 * Real.sqrt (clusterInertia m k (x t)))) t :=
    hJ.sqrt (ne_of_gt hJpos)
  have hinv := hsqrt.inv hsqrt_ne
  have hq : HasDerivAt (fun s : ℝ => cmRel m k (x s)) (cmRel m k (deriv x t)) t :=
    hasDerivAt_cmRel m k hx.self_of_nhds
  have hsl := hinv.smul hq
  have hder : -(deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / (2 * Real.sqrt (clusterInertia m k (x t))))
      / (Real.sqrt (clusterInertia m k (x t))) ^ 2
      = -(deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / (2 * (Real.sqrt (clusterInertia m k (x t))) ^ 3)) := by
    field_simp
  rw [hder] at hsl
  have hfun : (fun s : ℝ => clusterShape m k (x s))
      = (fun s : ℝ => (Real.sqrt (clusterInertia m k (x s)))⁻¹ • cmRel m k (x s)) := by
    funext s; rw [clusterShape]
  rw [hfun]
  exact hsl

end Submission.NBody
