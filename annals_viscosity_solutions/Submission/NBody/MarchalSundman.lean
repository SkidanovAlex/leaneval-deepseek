import Submission.NBody.MarchalForce
import Mathlib

/-!
# The Lagrange–Jacobi identity for a colliding cluster, in the form used by Sundman's argument

Collecting `MarchalLagrangeJacobi` (the calculus of the moment of inertia) and `MarchalForce` (the
work of the Newtonian force), the second derivative of the moment of inertia of a cluster along a
motion is

    `Ï_k = 4 E_k + 2 U_k + B(t)`,   `B(t) = 2·crossWork − 2 m_k ‖v_{cm,k}‖²`,

where `E_k = K_k - U_k` is the energy of the cluster and `B` is a *remainder*: it involves only the
pairs of bodies not both in `k` and the velocity of the centre of mass of `k`, hence is bounded as
soon as the cluster is separated from the other bodies (which is exactly what "colliding cluster"
means at the collision time).

For the classical Newtonian exponent (`α = 1`) this is Ferrario–Terracini's
`½ Ï_k = 2E_k + (2−α)U_k + C⁰` with `C⁰` continuous.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The energy of a cluster: kinetic energy of the cluster minus the internal potential. -/
noncomputable def clusterEnergy (m : Fin N → ℝ) (k : Finset (Fin N)) (x v : EN E N) : ℝ :=
  clusterKineticSq m k v / 2 - clusterPotential m k x

/-- The centre-of-mass-relative kinetic energy of a cluster: removing the motion of the centre of
mass. -/
lemma clusterKineticSq_cmRel {m : Fin N → ℝ} (k : Finset (Fin N)) (v : EN E N)
    (hm : ∀ i, 0 < m i) (hk : k.Nonempty) :
    clusterKineticSq m k (cmRel m k v)
      = clusterKineticSq m k v - clusterMass m k * ‖clusterCM m k v‖ ^ 2 := by
  have hMpos : 0 < ∑ i ∈ k, m i := Finset.sum_pos (fun i _ => hm i) hk
  rw [clusterKineticSq, clusterKineticSq, clusterMass]
  have h : ∀ i ∈ k, m i * ‖(cmRel m k v) i‖ ^ 2
      = m i * ‖v i‖ ^ 2
        - 2 * m i * inner ℝ (v i) (clusterCM m k v)
        + m i * ‖clusterCM m k v‖ ^ 2 := by
    intro i hi
    rw [cmRel_apply_of_mem hi, norm_sub_sq_real]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsum : ∑ i ∈ k, m i * inner ℝ (v i) (clusterCM m k v)
      = inner ℝ (∑ i ∈ k, m i • v i) (clusterCM m k v) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left]
  have hcm : clusterCM m k v = (∑ i ∈ k, m i)⁻¹ • (∑ i ∈ k, m i • v i) := rfl
  have h2 : ∑ i ∈ k, 2 * m i * inner ℝ (v i) (clusterCM m k v)
      = 2 * inner ℝ (∑ i ∈ k, m i • v i) (clusterCM m k v) := by
    rw [← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : ∑ i ∈ k, m i * ‖clusterCM m k v‖ ^ 2
      = (∑ i ∈ k, m i) * ‖clusterCM m k v‖ ^ 2 := by
    rw [Finset.sum_mul]
  rw [h2, h3, hcm]
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hMpos)]
  field_simp
  ring

/-- **The Lagrange–Jacobi identity for a cluster in Sundman's form.**  Along a collision-free
motion, `\ddot I_k = 4E_k + 2U_k + B`, where the remainder `B` involves only the interaction with
the other bodies and the centre-of-mass velocity of `k`. -/
theorem iteratedDeriv_two_clusterInertia_energy {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {t : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hnc : WithoutCollisions (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t)) :
    iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
      = 4 * clusterEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
        + (2 * crossWork m k (x t) (cmRel m k (x t))
            - 2 * clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2) := by
  rw [iteratedDeriv_two_clusterInertia_solution (fun i => ne_of_gt (hm i)) (ne_of_gt (clusterMass_pos hm hk))
      hx hd2 hode,
    sum_inner_gradient_cluster m k (x t) hnc, clusterKineticSq_cmRel k (deriv x t) hm hk]
  unfold clusterEnergy
  ring

end Submission.NBody
