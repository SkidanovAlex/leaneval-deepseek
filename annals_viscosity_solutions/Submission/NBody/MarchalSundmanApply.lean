import Submission.NBody.MarchalSundman
import Mathlib

/-!
# From the Lagrange–Jacobi identity to the hypotheses of Sundman's argument

`MarchalSundman.iteratedDeriv_two_clusterInertia_energy` writes the second derivative of the moment
of inertia of a cluster as

    `Ï_k = 4E_k + 2U_k + B(t)`,   `B = 2·crossWork − 2 m_k‖v_{cm,k}‖²`.

Here we turn that identity (together with the Ostrogradsky inequality and the a priori bound
`U_k ≥ c/√I_k`) into the two inequalities which drive Sundman's asymptotic analysis:

* `(İ_k)² ≤ 4 I_k Ï_k + C I_k`  (so that `lemma:bach` applies with `b = 4`, `α = 1`);
* `2 c/√I_k ≤ Ï_k + C`  (so that `Ï_k I_k^{1/2} ≥ c` for small `I_k`).

The constants `Ce`, `Cw`, `Cc` bound respectively the energy of the cluster, the interaction work
and the kinetic energy of its centre of mass; each of them is *bounded* along a trajectory near an
isolated collision (that is the content of the definition of a colliding cluster), but the
boundedness is discharged in a later module.

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

/-- Twice the kinetic energy of the cluster is the energy plus the internal potential. -/
lemma clusterKineticSq_eq_two_mul_energy_add (m : Fin N → ℝ) (k : Finset (Fin N)) (x v : EN E N) :
    clusterKineticSq m k v = 2 * clusterEnergy m k x v + 2 * clusterPotential m k x := by
  unfold clusterEnergy
  ring

/-- The centre-of-mass-relative kinetic energy is at most the kinetic energy. -/
lemma clusterKineticSq_cmRel_le {m : Fin N → ℝ} (k : Finset (Fin N)) (v : EN E N)
    (hm : ∀ i, 0 < m i) (hk : k.Nonempty) :
    clusterKineticSq m k (cmRel m k v) ≤ clusterKineticSq m k v := by
  rw [clusterKineticSq_cmRel k v hm hk]
  have h1 : 0 ≤ clusterMass m k * ‖clusterCM m k v‖ ^ 2 :=
    mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)
  linarith

/-- **The Ostrogradsky inequality in Sundman's form.**  If the energy of the cluster, the
interaction work and the centre-of-mass kinetic energy are bounded by `C`, then

    `(İ_k)² ≤ 4 I_k Ï_k + 24 C I_k`. -/
theorem clusterInertia_deriv_sq_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t C : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hE : |clusterEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hV : clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 ≤ C)
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : WithoutCollisions (x t)) :
    (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
      ≤ 4 * clusterInertia m k (x t) * iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
        + 24 * C * clusterInertia m k (x t) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hE
  have hEnn : -C ≤ clusterEnergy m k (x t) (deriv x t) := (abs_le.mp hE).1
  have hWnn : -C ≤ crossWork m k (x t) (cmRel m k (x t)) := (abs_le.mp hW).1
  have hderiv : deriv (fun s : ℝ => clusterInertia m k (x s)) t
      = 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t)) :=
    (deriv_clusterInertia_eq m k hx).self_of_nhds
  have hLJ := iteratedDeriv_two_clusterInertia_energy hm hk hnc hx hd2 hode
  have hCS : (massInner m (cmRel m k (x t)) (cmRel m k (deriv x t))) ^ 2
      ≤ clusterInertia m k (x t) * clusterKineticSq m k (cmRel m k (deriv x t)) :=
    ostrogradsky (fun i => (hm i).le) k (x t) (deriv x t)
  have hK : clusterKineticSq m k (cmRel m k (deriv x t)) ≤ clusterKineticSq m k (deriv x t) :=
    clusterKineticSq_cmRel_le k (deriv x t) hm hk
  have h2K : clusterKineticSq m k (deriv x t)
      = 2 * clusterEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t) :=
    clusterKineticSq_eq_two_mul_energy_add m k (x t) (deriv x t)
  have hfac : 0 ≤ clusterInertia m k (x t) := clusterInertia_nonneg (fun i => (hm i).le) k (x t)
  have hstep1 : (2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t))) ^ 2
      ≤ 4 * clusterInertia m k (x t) * clusterKineticSq m k (cmRel m k (deriv x t)) := by
    nlinarith [hCS, hfac]
  have hKbound : clusterKineticSq m k (deriv x t)
      ≤ (4 * clusterEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
          + (2 * crossWork m k (x t) (cmRel m k (x t))
              - 2 * clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2)) + 6 * C := by
    rw [h2K]
    linarith
  rw [hderiv, hLJ]
  nlinarith [hstep1, hK, hKbound, hfac, hC0]

/-- **The lower bound on `Ï_k` in Sundman's form.**  If the energy, the interaction work and the
centre-of-mass kinetic energy are bounded by `C` and `U_k ≥ ck/√I_k`, then

    `ck/√I_k ≤ Ï_k + 8C`. -/
theorem clusterInertia_second_deriv_ge {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t C ck : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty) (hC0 : 0 ≤ C) (hck0 : 0 ≤ ck)
    (hE : -C ≤ clusterEnergy m k (x t) (deriv x t))
    (hW : -C ≤ crossWork m k (x t) (cmRel m k (x t)))
    (hV : clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 ≤ C)
    (hU : ck / Real.sqrt (clusterInertia m k (x t)) ≤ clusterPotential m k (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : WithoutCollisions (x t)) :
    ck / Real.sqrt (clusterInertia m k (x t))
      ≤ iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t + 8 * C := by
  have hLJ := iteratedDeriv_two_clusterInertia_energy hm hk hnc hx hd2 hode
  have hsq : 0 ≤ Real.sqrt (clusterInertia m k (x t)) := Real.sqrt_nonneg _
  have hU0 : 0 ≤ clusterPotential m k (x t) := by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (le_of_lt (hm p.1)) (le_of_lt (hm p.2))) (inv_nonneg.mpr dist_nonneg)
  have hck : 0 ≤ ck / Real.sqrt (clusterInertia m k (x t)) :=
    div_nonneg hck0 (Real.sqrt_nonneg _)
  rw [hLJ]
  linarith

end Submission.NBody
