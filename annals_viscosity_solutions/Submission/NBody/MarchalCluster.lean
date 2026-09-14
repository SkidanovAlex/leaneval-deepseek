import Submission.NBody.Jacobi
import Submission.NBody.Force
import Submission.NBody.EulerLagrange
import Mathlib

/-!
# Clusters in the Newtonian `N`-body problem

Marchal's theorem (an action-minimising trajectory has no interior collisions) is proved by
contradiction: blowing up a colliding minimiser at the collision time.  The blow-up is governed by
the classical asymptotics of *colliding clusters* (Sperner, Wintner, Sperling), for which the
following objects are the basic ones.  For a set of bodies `k`:

* `clusterMass m k`, `clusterCM m k x` — the mass and the centre of mass of `k`;
* `cmRel m k x` — the configuration relative to that centre of mass (zero outside `k`);
* `clusterInertia m k x = ∑_{i∈k} mᵢ ‖xᵢ - x_{cm,k}‖²` — the moment of inertia of the cluster;
* `clusterKineticSq m k v = ∑_{i∈k} mᵢ ‖vᵢ‖²` — twice the kinetic energy of the cluster.

The main elementary fact recorded here is the Cauchy–Schwarz (Ostrogradsky) inequality

    `(∑_{i∈k} mᵢ ⟪qᵢ, vᵢ⟫)² ≤ (∑_{i∈k} mᵢ‖qᵢ‖²) (∑_{i∈k} mᵢ‖vᵢ‖²)`

in the mass inner product, which is the first ingredient of the Lagrange–Jacobi analysis of a
colliding cluster.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## The mass inner product as a Euclidean inner product -/

lemma massInner_eq_inner_massScale' {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    massInner m v w = inner ℝ (massScale m v) (massScale m w) := by
  rw [massInner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [massScale_apply, massScale_apply, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, Real.mul_self_sqrt (hm i)]

/-- **Cauchy–Schwarz inequality for the mass inner product.** -/
lemma massInner_sq_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    (massInner m v w) ^ 2 ≤ massInner m v v * massInner m w w := by
  rw [massInner_eq_inner_massScale' hm, massInner_eq_inner_massScale' hm,
    massInner_eq_inner_massScale' hm]
  simpa [pow_two] using real_inner_mul_inner_self_le (massScale m v) (massScale m w)

lemma massInner_self_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v : EN E N) :
    0 ≤ massInner m v v := by
  rw [massInner_eq_inner_massScale' hm]
  exact real_inner_self_nonneg

/-! ## Clusters -/

/-- The total mass of a set of bodies. -/
noncomputable def clusterMass (m : Fin N → ℝ) (k : Finset (Fin N)) : ℝ := ∑ i ∈ k, m i

/-- The centre of mass of a set of bodies. -/
noncomputable def clusterCM (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : E :=
  (clusterMass m k)⁻¹ • ∑ i ∈ k, m i • x i

/-- The configuration relative to the centre of mass of `k`, extended by `0` outside `k`. -/
noncomputable def cmRel (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : EN E N :=
  WithLp.toLp 2 fun i => if i ∈ k then x i - clusterCM m k x else 0

@[simp]
lemma cmRel_apply (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) (i : Fin N) :
    cmRel m k x i = if i ∈ k then x i - clusterCM m k x else 0 := rfl

lemma cmRel_apply_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {i : Fin N}
    (hi : i ∈ k) : cmRel m k x i = x i - clusterCM m k x := by
  simp [cmRel_apply, hi]

lemma cmRel_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {i : Fin N}
    (hi : i ∉ k) : cmRel m k x i = 0 := by
  simp [cmRel_apply, hi]

/-- The moment of inertia of a cluster about its centre of mass. -/
noncomputable def clusterInertia (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : ℝ :=
  ∑ i ∈ k, m i * ‖x i - clusterCM m k x‖ ^ 2

/-- Twice the kinetic energy of a cluster. -/
noncomputable def clusterKineticSq (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) : ℝ :=
  ∑ i ∈ k, m i * ‖v i‖ ^ 2

lemma clusterInertia_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (x : EN E N) : 0 ≤ clusterInertia m k x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)

lemma clusterKineticSq_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (v : EN E N) : 0 ≤ clusterKineticSq m k v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)

lemma clusterMass_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N)) :
    0 ≤ clusterMass m k :=
  Finset.sum_nonneg fun i _ => hm i

lemma clusterMass_pos {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} (hk : k.Nonempty) :
    0 < clusterMass m k :=
  Finset.sum_pos (fun i _ => hm i) hk

/-- The centre of mass is the mass centre: `∑_{i∈k} mᵢ (xᵢ - x_{cm,k}) = 0`. -/
lemma clusterCM_sum {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hmk : clusterMass m k ≠ 0) :
    ∑ i ∈ k, m i • (x i - clusterCM m k x) = 0 := by
  have h1 : ∀ i ∈ k, m i • (x i - clusterCM m k x) = m i • x i - m i • clusterCM m k x :=
    fun i _ => smul_sub (m i) (x i) (clusterCM m k x)
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [show (∑ i ∈ k, m i) • clusterCM m k x = clusterMass m k • clusterCM m k x from rfl,
    clusterCM, smul_smul, mul_inv_cancel₀ hmk, one_smul, sub_self]

/-- A sum of the form `∑ i, if i ∈ k then f i else 0` restricted to `k`. -/
private lemma sum_ite_mem_eq {M : Type*} [AddCommMonoid M] (k : Finset (Fin N)) (f : Fin N → M) :
    (∑ i : Fin N, if i ∈ k then f i else 0) = ∑ i ∈ k, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- `clusterInertia` is the square of the mass norm of the centre-of-mass-relative configuration. -/
lemma clusterInertia_eq_massInner (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    clusterInertia m k x = massInner m (cmRel m k x) (cmRel m k x) := by
  have key : (∑ i : Fin N, m i * inner ℝ (cmRel m k x i) (cmRel m k x i))
      = ∑ i ∈ k, m i * ‖x i - clusterCM m k x‖ ^ 2 := by
    have h : ∀ i : Fin N, m i * inner ℝ (cmRel m k x i) (cmRel m k x i)
        = if i ∈ k then m i * ‖x i - clusterCM m k x‖ ^ 2 else 0 := by
      intro i
      rw [cmRel_apply, real_inner_self_eq_norm_sq]
      by_cases hi : i ∈ k
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        simp
    rw [Finset.sum_congr rfl (fun i _ => h i), sum_ite_mem_eq]
  rw [massInner, key, clusterInertia]

lemma clusterKineticSq_eq_massInner (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) :
    clusterKineticSq m k (cmRel m k v) = massInner m (cmRel m k v) (cmRel m k v) := by
  have key : (∑ i : Fin N, m i * inner ℝ (cmRel m k v i) (cmRel m k v i))
      = ∑ i ∈ k, m i * ‖v i - clusterCM m k v‖ ^ 2 := by
    have h : ∀ i : Fin N, m i * inner ℝ (cmRel m k v i) (cmRel m k v i)
        = if i ∈ k then m i * ‖v i - clusterCM m k v‖ ^ 2 else 0 := by
      intro i
      rw [cmRel_apply, real_inner_self_eq_norm_sq]
      by_cases hi : i ∈ k
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        simp
    rw [Finset.sum_congr rfl (fun i _ => h i), sum_ite_mem_eq]
  rw [massInner, key, clusterKineticSq]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cmRel_apply_of_mem hi]

/-- **Ostrogradsky's (Cauchy–Schwarz) inequality for a cluster.** -/
theorem ostrogradsky {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N)) (x v : EN E N) :
    (massInner m (cmRel m k x) (cmRel m k v)) ^ 2
      ≤ clusterInertia m k x * clusterKineticSq m k (cmRel m k v) := by
  calc (massInner m (cmRel m k x) (cmRel m k v)) ^ 2
      ≤ massInner m (cmRel m k x) (cmRel m k x) * massInner m (cmRel m k v) (cmRel m k v) :=
        massInner_sq_le hm _ _
    _ = clusterInertia m k x * clusterKineticSq m k (cmRel m k v) := by
        rw [← clusterInertia_eq_massInner, ← clusterKineticSq_eq_massInner]

end Submission.NBody
