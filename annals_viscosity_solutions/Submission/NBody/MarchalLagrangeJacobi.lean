import Submission.NBody.MarchalCluster
import Submission.NBody.Energy
import Mathlib

/-!
# The Lagrange–Jacobi identity for a cluster

The second derivative of the moment of inertia of a cluster `k` along a motion `x` is the basic
input of the collision asymptotics (Sperner, Wintner, Sperling; Ferrario–Terracini Lemma 5.1):

    `Ï_k = 2 ∑_{i∈k} mᵢ‖q̇ᵢ‖² + 2 ∑_{i∈k} mᵢ ⟪qᵢ, ẍᵢ⟫`,

where `qᵢ = xᵢ - x_{cm,k}` is the configuration relative to the centre of mass of the cluster.
The second term is analysed with the equations of motion (`q̈ᵢ = ∇ᵢU`) and Euler homogeneity; it
equals `-2U_k` plus a bounded interaction remainder.

This module contains the *calculus* part: the first and second derivatives of
`t ↦ clusterInertia m k (x t)` expressed through `massInner m (cmRel ·) (cmRel ·)`.

Everything here is fully proved.
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

/-- A sum of the form `∑ i, if i ∈ k then f i else 0` restricted to `k`. -/
private lemma sum_ite_mem_eq' {M : Type*} [AddCommMonoid M] (k : Finset (Fin N)) (f : Fin N → M) :
    (∑ i : Fin N, if i ∈ k then f i else 0) = ∑ i ∈ k, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- The mass inner product of two centre-of-mass-relative configurations, as a sum over `k`. -/
lemma massInner_cmRel_eq (m : Fin N → ℝ) (k : Finset (Fin N)) (X V : EN E N) :
    massInner m (cmRel m k X) (cmRel m k V)
      = ∑ i ∈ k, m i * inner ℝ (X i - clusterCM m k X) (V i - clusterCM m k V) := by
  have key : ∀ i : Fin N, m i * inner ℝ (cmRel m k X i) (cmRel m k V i)
      = if i ∈ k then m i * inner ℝ (X i - clusterCM m k X) (V i - clusterCM m k V) else 0 := by
    intro i
    by_cases hi : i ∈ k
    · simp [cmRel_apply, hi]
    · simp [cmRel_apply, hi]
  rw [massInner, Finset.sum_congr rfl fun i _ => key i, sum_ite_mem_eq']

/-- The centre of mass of a differentiable curve is differentiable, with the centre of mass of the
velocity as derivative. -/
lemma hasDerivAt_clusterCM (m : Fin N → ℝ) (k : Finset (Fin N)) {X : ℝ → EN E N} {X' : EN E N}
    {t : ℝ} (hX : HasDerivAt X X' t) :
    HasDerivAt (fun s : ℝ => clusterCM m k (X s)) (clusterCM m k X') t := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ i ∈ k, m i • X s i) (∑ i ∈ k, m i • X' i) t := by
    have hfeq : (fun s : ℝ => ∑ i ∈ k, m i • X s i)
        = (∑ i ∈ k, fun s : ℝ => m i • X s i) := by
      funext s
      simp only [Finset.sum_apply]
    rw [hfeq]
    exact HasDerivAt.sum fun i _ => (hasDerivAt_apply hX i).const_smul (m i)
  have h := hsum.const_smul ((clusterMass m k)⁻¹)
  have hfun : (fun s : ℝ => clusterCM m k (X s))
      = ((clusterMass m k)⁻¹ • fun s : ℝ => ∑ i ∈ k, m i • X s i) := by
    funext s
    rw [Pi.smul_apply, clusterCM]
  have hval : clusterCM m k X' = (clusterMass m k)⁻¹ • ∑ i ∈ k, m i • X' i := rfl
  rw [hfun, hval]
  exact h

/-- The derivative of the mass inner product of two centre-of-mass-relative curves. -/
lemma hasDerivAt_inertia_pair (m : Fin N → ℝ) (k : Finset (Fin N)) {X V : ℝ → EN E N}
    {X' V' : EN E N} {t : ℝ} (hX : HasDerivAt X X' t) (hV : HasDerivAt V V' t) :
    HasDerivAt (fun s : ℝ => massInner m (cmRel m k (X s)) (cmRel m k (V s)))
      (massInner m (cmRel m k X') (cmRel m k (V t))
        + massInner m (cmRel m k (X t)) (cmRel m k V')) t := by
  have key : ∀ i : Fin N, HasDerivAt
      (fun s : ℝ => m i * inner ℝ (X s i - clusterCM m k (X s)) (V s i - clusterCM m k (V s)))
      (m i * inner ℝ (X' i - clusterCM m k X') (V t i - clusterCM m k (V t))
        + m i * inner ℝ (X t i - clusterCM m k (X t)) (V' i - clusterCM m k V')) t := by
    intro i
    have h1 : HasDerivAt (fun s : ℝ => X s i - clusterCM m k (X s))
        (X' i - clusterCM m k X') t :=
      (hasDerivAt_apply hX i).sub (hasDerivAt_clusterCM m k hX)
    have h2 : HasDerivAt (fun s : ℝ => V s i - clusterCM m k (V s))
        (V' i - clusterCM m k V') t :=
      (hasDerivAt_apply hV i).sub (hasDerivAt_clusterCM m k hV)
    have h3 := (h1.inner ℝ h2).const_mul (m i)
    rw [mul_add, add_comm] at h3
    exact h3
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ i ∈ k, m i * inner ℝ (X s i - clusterCM m k (X s))
        (V s i - clusterCM m k (V s)))
      ((∑ i ∈ k, m i * inner ℝ (X' i - clusterCM m k X') (V t i - clusterCM m k (V t)))
        + (∑ i ∈ k, m i * inner ℝ (X t i - clusterCM m k (X t))
            (V' i - clusterCM m k V'))) t := by
    have hfeq : (fun s : ℝ => ∑ i ∈ k, m i * inner ℝ (X s i - clusterCM m k (X s))
        (V s i - clusterCM m k (V s)))
        = (∑ i ∈ k, fun s : ℝ => m i * inner ℝ (X s i - clusterCM m k (X s))
            (V s i - clusterCM m k (V s))) := by
      funext s
      simp only [Finset.sum_apply]
    rw [hfeq]
    have hthis := HasDerivAt.sum (u := k)
      (A := fun i : Fin N => fun s : ℝ => m i * inner ℝ (X s i - clusterCM m k (X s))
        (V s i - clusterCM m k (V s)))
      (A' := fun i : Fin N => m i * inner ℝ (X' i - clusterCM m k X')
          (V t i - clusterCM m k (V t))
        + m i * inner ℝ (X t i - clusterCM m k (X t)) (V' i - clusterCM m k V'))
      (fun i _ => key i)
    rw [Finset.sum_add_distrib] at hthis
    exact hthis
  have hL : (fun s : ℝ => massInner m (cmRel m k (X s)) (cmRel m k (V s)))
      = (fun s : ℝ => ∑ i ∈ k, m i * inner ℝ (X s i - clusterCM m k (X s))
          (V s i - clusterCM m k (V s))) := by
    funext s
    rw [massInner_cmRel_eq]
  rw [hL, massInner_cmRel_eq m k X' (V t), massInner_cmRel_eq m k (X t) V']
  exact hsum

/-- The derivative of the moment of inertia of a cluster along a curve. -/
lemma deriv_clusterInertia_eq (m : Fin N → ℝ) (k : Finset (Fin N)) {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    deriv (fun s : ℝ => clusterInertia m k (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s))) := by
  have hcongr : (fun s : ℝ => clusterInertia m k (x s))
      = (fun s : ℝ => massInner m (cmRel m k (x s)) (cmRel m k (x s))) := by
    funext s
    rw [clusterInertia_eq_massInner]
  filter_upwards [hx] with s hs
  have h1 := hasDerivAt_inertia_pair m k hs hs
  rw [hcongr, h1.deriv, massInner_comm m (cmRel m k (deriv x s)) (cmRel m k (x s))]
  ring

/-- **The second derivative of the moment of inertia of a cluster.** -/
theorem iteratedDeriv_two_clusterInertia (m : Fin N → ℝ) (k : Finset (Fin N)) {x : ℝ → EN E N}
    {t : ℝ} (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (deriv (deriv x) t) t) :
    iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
      = 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv x t)) := by
  have hderiv : deriv (fun s : ℝ => clusterInertia m k (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s))) :=
    deriv_clusterInertia_eq m k hx
  have h2 : HasDerivAt (fun s : ℝ => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s)))
      (2 * (massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv x t))
        + massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv x) t)))) t :=
    (hasDerivAt_inertia_pair m k hx.self_of_nhds hd2).const_mul 2
  rw [show iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
      = deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      = deriv (fun s : ℝ => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s))) t
    from Filter.EventuallyEq.deriv_eq hderiv]
  rw [h2.deriv]
  ring

/-- The mass inner product of a centre-of-mass-relative configuration with an arbitrary one. -/
lemma massInner_cmRel_eq' (m : Fin N → ℝ) (k : Finset (Fin N)) (X Z : EN E N) :
    massInner m (cmRel m k X) Z
      = ∑ i ∈ k, m i * inner ℝ (X i - clusterCM m k X) (Z i) := by
  have key : ∀ i : Fin N, m i * inner ℝ (cmRel m k X i) (Z i)
      = if i ∈ k then m i * inner ℝ (X i - clusterCM m k X) (Z i) else 0 := by
    intro i
    by_cases hi : i ∈ k
    · simp [cmRel_apply, hi]
    · simp [cmRel_apply, hi]
  rw [massInner, Finset.sum_congr rfl fun i _ => key i, sum_ite_mem_eq']

/-- The second argument of the mass inner product may be replaced by its centre-of-mass
projection. -/
lemma massInner_cmRel_cmRel_eq (m : Fin N → ℝ) (k : Finset (Fin N)) (X Z : EN E N)
    (hmk : clusterMass m k ≠ 0) :
    massInner m (cmRel m k X) (cmRel m k Z) = massInner m (cmRel m k X) Z := by
  rw [massInner_cmRel_eq' m k X (cmRel m k Z), massInner_cmRel_eq' m k X Z]
  have hpt : ∀ i ∈ k, m i * inner ℝ (X i - clusterCM m k X) ((cmRel m k Z) i)
      = m i * inner ℝ (X i - clusterCM m k X) (Z i)
        - m i * inner ℝ (X i - clusterCM m k X) (clusterCM m k Z) := by
    intro i hi
    rw [cmRel_apply_of_mem hi, inner_sub_right, mul_sub]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  have hzero : ∑ i ∈ k, m i • (X i - clusterCM m k X) = 0 := clusterCM_sum hmk
  have h1 : ∑ i ∈ k, m i * inner ℝ (X i - clusterCM m k X) (clusterCM m k Z)
      = inner ℝ (∑ i ∈ k, m i • (X i - clusterCM m k X)) (clusterCM m k Z) := by
    refine Eq.trans ?_ (sum_inner k (fun i => m i • (X i - clusterCM m k X))
      (clusterCM m k Z)).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left]
  rw [h1, hzero, inner_zero_left, sub_zero]

/-- **The Lagrange–Jacobi identity for a cluster, along a motion.**  The second derivative of the
moment of inertia of the cluster is twice the work of the force, `∑_{i∈k} mᵢ⟪qᵢ, ẍᵢ⟫`, plus twice
its centre-of-mass-relative kinetic energy. -/
theorem iteratedDeriv_two_clusterInertia_solution {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {t : ℝ} (hm : ∀ i, m i ≠ 0) (hmk : clusterMass m k ≠ 0)
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t)) :
    iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
      = 2 * ∑ i ∈ k, inner ℝ ((x t) i - clusterCM m k (x t)) ((gradient (U m) (x t)) i)
        + 2 * clusterKineticSq m k (cmRel m k (deriv x t)) := by
  have hd2' : HasDerivAt (deriv x) (deriv (deriv x) t) t := by
    rw [show deriv (deriv x) t = iteratedDeriv 2 x t by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
    exact hd2
  have hbase := iteratedDeriv_two_clusterInertia m k hx hd2'
  rw [hbase, massInner_cmRel_cmRel_eq m k (x t) (deriv (deriv x) t) hmk,
    massInner_cmRel_eq' m k (x t) (deriv (deriv x) t),
    ← clusterKineticSq_eq_massInner m k (deriv x t)]
  rw [hd2.deriv, hode]
  have hforce : (∑ i ∈ k, m i * inner ℝ (x t i - clusterCM m k (x t))
        ((∇_[m] (U m) (x t)) i))
      = ∑ i ∈ k, inner ℝ (x t i - clusterCM m k (x t)) ((gradient (U m) (x t)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weightedGrad, PiLp.toLp_apply,
      show m i * inner ℝ (x t i - clusterCM m k (x t)) ((m i)⁻¹ • (gradient (U m) (x t)) i)
          = (m i * (m i)⁻¹) * inner ℝ (x t i - clusterCM m k (x t)) ((gradient (U m) (x t)) i) by
        rw [real_inner_smul_right, mul_assoc],
      mul_inv_cancel₀ (hm i), one_mul]
  rw [hforce]

end Submission.NBody
