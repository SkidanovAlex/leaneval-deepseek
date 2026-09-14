import Submission.NBody.MarchalLagrangeJacobi
import Submission.NBody.Force
import Mathlib

/-!
# The work of the force on a cluster

The Lagrange–Jacobi identity for a cluster (`MarchalLagrangeJacobi`) exhibits the second derivative
of the moment of inertia of a cluster `k` through

    `W_k(x) = ∑_{i∈k} ⟪qᵢ, (∇U x)ᵢ⟫`,   `qᵢ = xᵢ - x_{cm,k}`,

the work of the Newtonian force.  The present module computes this work: the pairs internal to the
cluster contribute `-U_k` (the *virial* of the cluster), while the remaining pairs contribute a
"cross" term which is bounded as soon as the cluster is separated from the other bodies.  This is
the first half of the classical identity `½ Ï_k = 2E_k + (2-α)U_k + (bounded)` of
Ferrario–Terracini (`lemma:5`/`coro:lagjac`).

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

/-- The configuration relative to the centre of mass of `k`, as a function `Fin N → E`. -/
noncomputable def cmRelVec (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : Fin N → E :=
  fun j => if j ∈ k then x j - clusterCM m k x else 0

lemma cmRel_eq_toLp (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    cmRel m k x = WithLp.toLp 2 (cmRelVec m k x) := rfl

lemma cmRelVec_apply_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {j : Fin N}
    (hj : j ∈ k) : cmRelVec m k x j = x j - clusterCM m k x := by
  simp [cmRelVec, hj]

lemma cmRelVec_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {j : Fin N}
    (hj : j ∉ k) : cmRelVec m k x j = 0 := by
  simp [cmRelVec, hj]

/-- The centre-of-mass-relative configuration is the sum of the single-body displacements. -/
lemma cmRelVec_eq_sum (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    cmRelVec m k x
      = fun j : Fin N => (∑ i ∈ k, singleBodyVec i (x i - clusterCM m k x)).ofLp j := by
  funext j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  by_cases hj : j ∈ k
  · rw [cmRelVec_apply_of_mem hj, Finset.sum_eq_single j]
    · rw [singleBodyVec_self]
    · intro b _ hbj
      rw [singleBodyVec_of_ne (Ne.symm hbj)]
    · intro hj'
      exact absurd hj hj'
  · rw [cmRelVec_apply_of_notMem hj]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    rw [singleBodyVec_of_ne (fun h => hj (h ▸ hi) : j ≠ i)]

/-- The potential of the pairs internal to a cluster. -/
noncomputable def clusterPotential (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : ℝ :=
  ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
    m p.1 * m p.2 * (r x p.1 p.2)⁻¹

/-- The interaction term of the work of the force: the pairs with exactly one body in `k`. -/
noncomputable def crossWork (m : Fin N → ℝ) (k : Finset (Fin N)) (x d : EN E N) : ℝ :=
  ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
    m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2) (d p.1 - d p.2))

lemma cmRel_eq_sum (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    cmRel m k x = ∑ i ∈ k, singleBodyVec i (x i - clusterCM m k x) := by
  rw [cmRel_eq_toLp, cmRelVec_eq_sum]

/-- The work of the force on a cluster is minus the cluster potential plus the interaction term. -/
theorem sum_inner_gradient_cluster (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N)
    (hx : WithoutCollisions x) :
    ∑ i ∈ k, inner ℝ (x i - clusterCM m k x) ((gradient (U m) x) i)
      = - clusterPotential m k x + crossWork m k x (cmRel m k x) := by
  have hsum : (∑ i ∈ k, inner ℝ ((gradient (U m) x) i) (x i - clusterCM m k x))
      = (fderiv ℝ (U m) x) (cmRel m k x) := by
    rw [cmRel_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_singleBody (gradient (U m) x) i (x i - clusterCM m k x),
      inner_gradient_eq_fderiv]
  rw [Finset.sum_congr rfl fun i _ => real_inner_comm _ _]
  rw [hsum, fderiv_U_pair_apply m x (cmRel m k x) hx]
  rw [← Finset.sum_filter_add_sum_filter_not (pairFinset N)
    (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k)
    (fun p : Fin N × Fin N => m p.1 * m p.2 *
      (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
        ((cmRel m k x) p.1 - (cmRel m k x) p.2)))]
  have hQ : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
        ((cmRel m k x) p.1 - (cmRel m k x) p.2)))
      = - clusterPotential m k x := by
    rw [clusterPotential, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hp).2
    have hlt : p.1 < p.2 := by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      simpa using this
    rw [cmRel_apply_of_mem h1, cmRel_apply_of_mem h2]
    rw [show (x p.1 - clusterCM m k x) - (x p.2 - clusterCM m k x) = x p.1 - x p.2 by abel]
    rw [real_inner_self_eq_norm_sq, r_eq_norm_sub]
    have hv : ‖x p.1 - x p.2‖ ≠ 0 := by
      have := hx p.1 p.2 (ne_of_lt hlt)
      rwa [r_eq_norm_sub] at this
    field_simp
  rw [hQ, crossWork]

