import Submission.NBody.MarchalMultiEnergy
import Submission.NBody.MarchalThirdDeriv2

/-!
# The third derivative of the sum of the moments of inertia

The refinement of Sundman's analysis (`second_deriv_asymptotic_of_third_deriv_bound`) needs a bound

    `|f'''| ≤ e (f'')^{5/2}`

for `f = ∑_{k∈ks} I_k`, the sum of the moments of inertia of the simultaneously colliding clusters.
The per-cluster `abs_third_deriv_clusterInertia_le` is not available in this situation (its
separation hypothesis `ClusterSeparated k` fails inside the *other* colliding clusters), but the
third derivative is simply additive:

    `f''' = 6 ∑_k massInner (cmRel_k ẋ) (cmRel_k ẍ) + 2 ∑_k massInner (cmRel_k x) (cmRel_k ⃛x)`,

an identity obtained by summing `deriv_deriv_deriv_clusterInertia_eq` over the family.  The first
sum is a "power of the force" expression which is controlled by the internal potentials `U_k` and
the one-sided separation, and the second is analysed with `massInner_cmRel_third_eq`.

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

/-- **The hinge limit of the multi-cluster asymptotics**: `f''(t) * t^(2/3) -> (eta/4)/sqrt kappa`.
This is the estimate that replaces the missing `|E^rel_{C_l}| <= C` in the single-cluster theory.

Three traps (all cost a round each):
* `Real.div_rpow` takes `0 ≤ x` then `0 ≤ y` — the second argument needs `(...).le` of a positivity,
  not the bare positivity;
* `Real.rpow_pos_of_pos` needs its exponent given explicitly when there is no expected type;
* the goal produced by `Tendsto.div` is `(f / g) t`, i.e. under `Pi.div`, so
  `Real.sqrt_eq_rpow` cannot see the `√` until `rw [Pi.div_apply]` beta-reduces it (same
  shape-mismatch family as the `ring`-spine rewrites). -/
theorem hinge {f : ℝ → ℝ} {η κ ε : ℝ} (hη : 0 < η) (hκ : 0 < κ) (hε : 0 < ε)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < f t)
    (h1 : Tendsto (fun t : ℝ => deriv (deriv f) t * (f t) ^ ((1:ℝ)/2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (η / 4)))
    (h2 : Tendsto (fun t : ℝ => (f t / t ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ))) :
    Tendsto (fun t : ℝ => deriv (deriv f) t * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((η / 4) / Real.sqrt κ)) := by
  have h2' : Tendsto (fun t : ℝ => Real.sqrt (f t) / t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) := by
    refine h2.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have ht0 : 0 < t := ht.1
    rw [Real.div_rpow (le_of_lt (hfpos t ht)) (le_of_lt (Real.rpow_pos_of_pos ht0 ((4:ℝ)/3))),
      ← Real.rpow_mul ht0.le, Real.sqrt_eq_rpow]
    norm_num
  have hdiv := h1.div h2' (ne_of_gt (Real.sqrt_pos.mpr hκ))
  refine hdiv.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  have ht0 : 0 < t := ht.1
  have hp : (0:ℝ) < f t ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (hfpos t ht) _
  rw [Pi.div_apply, Real.sqrt_eq_rpow]
  field_simp

/-- Composition step of the multi-cluster asymptotics: from `f(t)/t^{4/3} -> kappa` get
`(f(t)/t^{4/3})^(1/2) -> sqrt kappa`. -/
theorem tendsto_rpow_half_of_tendsto_div_rpow {f : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : Tendsto (fun t : ℝ => f t / t ^ ((4:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ)) :
    Tendsto (fun t : ℝ => (f t / t ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) := by
  have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_eq_rpow] using h1


/-- **The third derivative of the sum of the moments of inertia of a family of clusters.** -/
theorem multiInertia_third_deriv_eq {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t : ℝ} (htm : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hd3 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) s) s) :
    deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t
      = 6 * (∑ k ∈ ks, massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)))
        + 2 * (∑ k ∈ ks,
            massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))) := by
  classical
  set G1 : ℝ → ℝ := fun s => ∑ k ∈ ks, clusterInertia m k (x s) with hG1
  set G2 : ℝ → ℝ := fun s => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s with hG2
  set G3 : ℝ → ℝ := fun s => ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) s
    with hG3
  set G4 : ℝ → ℝ := fun s =>
    ∑ k ∈ ks, deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) s with hG4
  have hloc : ∀ s ∈ Ioo (0:ℝ) ε, ∀ᶠ r in 𝓝 s, HasDerivAt x (deriv x r) r := by
    intro s hs
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact hx r hr
  have hd1 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt G1 (G2 s) s := by
    intro s hs
    rw [hG1, hG2]
    exact hasDerivAt_sum_apply ks (fun k (r : ℝ) => clusterInertia m k (x r))
      (fun k => deriv (fun r : ℝ => clusterInertia m k (x r)) s) s
      (fun k _ => hasDerivAt_clusterInertia_curve (k := k) (x := x) (hloc s hs))
  have hd2all : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt G2 (G3 s) s := by
    intro s hs
    rw [hG2, hG3]
    exact hasDerivAt_sum_apply ks (fun k (r : ℝ) => deriv (fun u : ℝ => clusterInertia m k (x u)) r)
      (fun k => deriv (deriv (fun u : ℝ => clusterInertia m k (x u))) s) s
      (fun k _ => hasDerivAt_deriv_clusterInertia_curve (k := k) (t := s)
        (hloc s hs) (hd2 s hs))
  have hd3all : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt G3 (G4 s) s := by
    intro s hs
    rw [hG3, hG4]
    exact hasDerivAt_sum_apply ks
      (fun k (r : ℝ) => deriv (deriv (fun u : ℝ => clusterInertia m k (x u))) r)
      (fun k => deriv (deriv (deriv (fun u : ℝ => clusterInertia m k (x u)))) s) s
      (fun k _ => hasDerivAt_deriv_deriv_clusterInertia_curve (m := m) (k := k) (x := x)
        (ε := ε) hs hx hd2 hd3)
  have e1 : deriv G1 =ᶠ[𝓝 t] G2 := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact (hd1 s hs).deriv
  have e2 : deriv G2 =ᶠ[𝓝 t] G3 := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact (hd2all s hs).deriv
  have e3 : deriv G3 =ᶠ[𝓝 t] G4 := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact (hd3all s hs).deriv
  have ee : deriv (deriv (deriv G1)) =ᶠ[𝓝 t] G4 :=
    ((Filter.EventuallyEq.deriv (Filter.EventuallyEq.deriv e1)).trans
      (Filter.EventuallyEq.deriv e2)).trans e3
  have hval : deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t
      = ∑ k ∈ ks, deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) t := by
    rw [show (fun s : ℝ => multiInertia m ks (x s)) = G1 from rfl, ee.self_of_nhds, hG4]
  rw [hval]
  have hper : ∀ k ∈ ks, deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) t
      = 6 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t)) :=
    fun k _ => deriv_deriv_deriv_clusterInertia_eq (m := m) (k := k) (x := x) (ε := ε) (t := t)
      htm hx hd2 hd3
  rw [Finset.sum_congr rfl hper]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The first sum in the third derivative is a "power of the force" expression.**  Using the
equations of motion, `A1_k` is the sum of `⟪q̇ᵢ, (∇U)ᵢ⟫` over the cluster, with the centre-of-mass
terms dropping out. -/
theorem sum_massInner_cmRel_deriv_eq {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty)
    {x : ℝ → EN E N} {ε t : ℝ} (htm : t ∈ Ioo (0:ℝ) ε)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s)) :
    (∑ k ∈ ks, massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)))
      = ∑ k ∈ ks, ∑ i ∈ k, inner ℝ ((cmRel m k (deriv x t)) i) ((gradient (U m) (x t)) i) := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hmk : clusterMass m k ≠ 0 := ne_of_gt (clusterMass_pos hm (hne k hk))
  have hode_t : deriv (deriv x) t = ∇_[m] (U m) (x t) := by
    rw [← iteratedDeriv_two_eq_deriv_deriv x t]
    exact hode t htm
  rw [hode_t, massInner_cmRel_cmRel_eq m k (deriv x t) (∇_[m] (U m) (x t)) hmk,
    massInner_cmRel_eq' m k (deriv x t) (∇_[m] (U m) (x t))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cmRel_apply_of_mem hi, weightedGrad, PiLp.toLp_apply,
    show m i * inner ℝ ((deriv x t) i - clusterCM m k (deriv x t))
        ((m i)⁻¹ • (gradient (U m) (x t)) i)
        = (m i * (m i)⁻¹) * inner ℝ ((deriv x t) i - clusterCM m k (deriv x t))
            ((gradient (U m) (x t)) i) by
      rw [real_inner_smul_right, mul_assoc],
    mul_inv_cancel₀ (ne_of_gt (hm i)), one_mul]


/-- The mass-weighted gradient of the potential at a body of a cluster is bounded by the square of
the internal potential plus a constant; only the *one-sided* separation is needed. -/
lemma norm_weightedGrad_coord_le_weak {m : Fin N → ℝ} {k : Finset (Fin N)} {ν κ : ℝ}
    (hm : ∀ i, 0 < m i) (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ) (hν : 0 < ν) :
    ∀ x : EN E N, ClusterSeparatedWeak k x ν → WithoutCollisions x → ∀ i ∈ k,
      ‖(∇_[m] (U m) x) i‖
        ≤ (max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1)
            * (clusterPotential m k x ^ 2 + 1) := by
  intro x hsep hnc i hi
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  have hU0 : 0 ≤ clusterPotential m k x := by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  rw [weightedGrad_U_coord m hmne x hnc i]
  have hterm : ∀ j ∈ Finset.univ.erase i, ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖
      = m j * ((‖x j - x i‖)⁻¹) ^ 2 := by
    intro j _
    have h3 : (‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖ = ((‖x j - x i‖)⁻¹) ^ 2 := by
      rw [inv_mul_eq_div, pow_succ]
      field_simp
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hm j).le (by positivity)), mul_assoc, h3]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j : Fin N => j ∈ k)
      (fun j : Fin N => m j * ((‖x j - x i‖)⁻¹) ^ 2)]
  have hint : (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
      m j * ((‖x j - x i‖)⁻¹) ^ 2) ≤ (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3) :=
    sum_inv_sq_le hm hκ hκpos hi
  have hcross : (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
      m j * ((‖x j - x i‖)⁻¹) ^ 2) ≤ (∑ j : Fin N, m j) * (ν⁻¹) ^ 2 := by
    have hstep : ∀ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m j * ((‖x j - x i‖)⁻¹) ^ 2 ≤ m j * (ν⁻¹) ^ 2 := by
      intro j hj
      obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
      have hdist : ν ≤ ‖x j - x i‖ := by
        have h := hsep i hi j hjk
        rw [r_eq_norm_sub] at h
        rwa [norm_sub_rev] at h
      have hnorm : 0 < ‖x j - x i‖ := lt_of_lt_of_le hν hdist
      have hinv : ((‖x j - x i‖)⁻¹) ^ 2 ≤ (ν⁻¹) ^ 2 := by
        have h2 : (‖x j - x i‖)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hnorm hν).mpr hdist
        exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) h2 2
      exact mul_le_mul_of_nonneg_left hinv (hm j).le
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
    · intro j _ _
      exact mul_nonneg (hm j).le (sq_nonneg _)
  set M : ℝ := max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) with hM
  have hM0 : 0 ≤ M := le_trans (by positivity) (le_max_left _ _)
  have h1 : (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3) ≤ M * clusterPotential m k x ^ 2 := by
    have heq : (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3)
        = ((N : ℝ) / κ ^ 3) * clusterPotential m k x ^ 2 := by ring
    rw [heq, hM]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have h2 : (∑ j : Fin N, m j) * (ν⁻¹) ^ 2 ≤ M := by
    rw [hM]; exact le_max_right _ _
  refine le_trans (add_le_add hint hcross) ?_
  nlinarith [h1, h2, hM0, sq_nonneg (clusterPotential m k x)]

/-- **The power of the force on the relative motion of a cluster.** -/
lemma abs_cluster_power_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {x : EN E N}
    {v : EN E N} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ i ∈ k, ‖(∇_[m] (U m) x) i‖ ≤ A * (clusterPotential m k x ^ 2 + 1)) :
    |∑ i ∈ k, inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)|
      ≤ A * (clusterPotential m k x ^ 2 + 1)
          * Real.sqrt (clusterMass m k * clusterKineticSq m k (cmRel m k v)) := by
  have hcoord : ∀ i ∈ k, (gradient (U m) x) i = m i • (∇_[m] (U m) x) i := by
    intro i hi
    simp only [weightedGrad, PiLp.toLp_apply]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hm i)), one_smul]
  have hU0 : 0 ≤ clusterPotential m k x ^ 2 + 1 := by positivity
  have hterm : ∀ i ∈ k, |inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)|
      ≤ m i * ‖(cmRel m k v) i‖ * (A * (clusterPotential m k x ^ 2 + 1)) := by
    intro i hi
    rw [hcoord i hi, real_inner_smul_right, abs_mul,
      abs_of_nonneg (hm i).le]
    have h2 : |inner ℝ ((cmRel m k v) i) ((∇_[m] (U m) x) i)|
        ≤ ‖(cmRel m k v) i‖ * (A * (clusterPotential m k x ^ 2 + 1)) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hA i hi) (norm_nonneg _))
    calc m i * |inner ℝ ((cmRel m k v) i) ((∇_[m] (U m) x) i)|
        ≤ m i * (‖(cmRel m k v) i‖ * (A * (clusterPotential m k x ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left h2 (hm i).le
      _ = m i * ‖(cmRel m k v) i‖ * (A * (clusterPotential m k x ^ 2 + 1)) := by ring
  calc |∑ i ∈ k, inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)|
      ≤ ∑ i ∈ k, |inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ k, m i * ‖(cmRel m k v) i‖ * (A * (clusterPotential m k x ^ 2 + 1)) :=
        Finset.sum_le_sum hterm
    _ = A * (clusterPotential m k x ^ 2 + 1) * ∑ i ∈ k, m i * ‖(cmRel m k v) i‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ A * (clusterPotential m k x ^ 2 + 1)
          * Real.sqrt (clusterMass m k * clusterKineticSq m k (cmRel m k v)) :=
        mul_le_mul_of_nonneg_left (sum_mass_norm_le_sqrt (fun i => (hm i).le))
          (mul_nonneg hA0 hU0)

/-- **Estimate (a): the power of the force on the relative motion of a family of colliding
clusters.**  The whole family is bounded by `√K` times a power of the sum of the internal
potentials, where `K` bounds the total kinetic energy. -/
theorem abs_sum_cluster_power_le {m : Fin N → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty)
    {ν K : ℝ} (hν : 0 < ν) (hK : 0 ≤ K)
    {x : EN E N} {v : EN E N} (hnc : WithoutCollisions x)
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k x ν)
    (hKin : kinetic m v ≤ K) :
    |∑ k ∈ ks, ∑ i ∈ k, inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)|
      ≤ (max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1)
          * (∑ k ∈ ks, Real.sqrt (clusterMass m k)) * Real.sqrt (2 * K)
          * (1 + (multiPotential m ks x) ^ 2) := by
  classical
  set A : ℝ := max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hUpot0 : ∀ k ∈ ks, 0 ≤ clusterPotential m k x := fun k _ =>
    Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hKrel : ∀ k ∈ ks, clusterKineticSq m k (cmRel m k v) ≤ 2 * K := by
    intro k hk
    have h1 : clusterKineticSq m k (cmRel m k v) ≤ clusterKineticSq m k v := by
      rw [clusterKineticSq_cmRel k v hm (hne k hk)]
      have := mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k)
        (sq_nonneg ‖clusterCM m k v‖)
      linarith
    have h2 : clusterKineticSq m k v ≤ ∑ i, m i * ‖v i‖ ^ 2 := by
      rw [clusterKineticSq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ k)
        (fun i _ _ => mul_nonneg (hm i).le (sq_nonneg _))
    have h3 : (∑ i, m i * ‖v i‖ ^ 2) = 2 * kinetic m v := by
      rw [kinetic]; ring
    linarith [hKin]
  have hstep : ∀ k ∈ ks, |∑ i ∈ k, inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)|
      ≤ A * (clusterPotential m k x ^ 2 + 1)
          * (Real.sqrt (clusterMass m k) * Real.sqrt (2 * K)) := by
    intro k hk
    have hp := abs_cluster_power_le (m := m) (k := k) (x := x) (v := v) (A := A) hm hA0
      (norm_weightedGrad_coord_le_weak (m := m) (k := k) (ν := ν) (κ := κ) hm hκ hκpos hν
        x (hsep k hk) hnc)
    refine hp.trans ?_
    have hfac : Real.sqrt (clusterMass m k * clusterKineticSq m k (cmRel m k v))
        ≤ Real.sqrt (clusterMass m k) * Real.sqrt (2 * K) := by
      rw [Real.sqrt_mul (clusterMass_nonneg (fun i => (hm i).le) k)]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hKrel k hk)) (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left hfac
      (mul_nonneg hA0 (by positivity))
  calc |∑ k ∈ ks, ∑ i ∈ k, inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)|
      ≤ ∑ k ∈ ks, |∑ i ∈ k, inner ℝ ((cmRel m k v) i) ((gradient (U m) x) i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ ks, A * (clusterPotential m k x ^ 2 + 1)
          * (Real.sqrt (clusterMass m k) * Real.sqrt (2 * K)) := Finset.sum_le_sum hstep
    _ = A * Real.sqrt (2 * K) * ∑ k ∈ ks,
          Real.sqrt (clusterMass m k) * (clusterPotential m k x ^ 2 + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ A * Real.sqrt (2 * K) * ((∑ k ∈ ks, Real.sqrt (clusterMass m k))
          * (1 + (∑ k ∈ ks, clusterPotential m k x) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA0 (Real.sqrt_nonneg _))
        have hsum0 : 0 ≤ ∑ k ∈ ks, clusterPotential m k x :=
          Finset.sum_nonneg hUpot0
        have hterm : ∀ k ∈ ks, Real.sqrt (clusterMass m k) * (clusterPotential m k x ^ 2 + 1)
            ≤ Real.sqrt (clusterMass m k)
              * (1 + (∑ k' ∈ ks, clusterPotential m k' x) ^ 2) := by
          intro k hk
          have hle : clusterPotential m k x ≤ ∑ k' ∈ ks, clusterPotential m k' x :=
            Finset.single_le_sum hUpot0 hk
          have hsq : clusterPotential m k x ^ 2 ≤ (∑ k' ∈ ks, clusterPotential m k' x) ^ 2 :=
            pow_le_pow_left₀ (hUpot0 k hk) hle 2
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [← Finset.sum_mul]
    _ = (max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1)
          * (∑ k ∈ ks, Real.sqrt (clusterMass m k)) * Real.sqrt (2 * K)
          * (1 + (multiPotential m ks x) ^ 2) := by
        rw [multiPotential]; ring


/-- **Estimate (a) in the form used by the third-derivative assembly**: the first of the two sums in
`multiInertia_third_deriv_eq`, with the equations of motion substituted. -/
theorem abs_sum_massInner_cmRel_deriv_le {m : Fin N → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty)
    {ν K : ℝ} (hν : 0 < ν) (hK : 0 ≤ K)
    {x : ℝ → EN E N} {ε t : ℝ} (htm : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hKin : kinetic m (deriv x t) ≤ K) :
    |∑ k ∈ ks, massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))|
      ≤ (max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1)
          * (∑ k ∈ ks, Real.sqrt (clusterMass m k)) * Real.sqrt (2 * K)
          * (1 + (multiPotential m ks (x t)) ^ 2) := by
  rw [sum_massInner_cmRel_deriv_eq hm hne htm hode]
  exact abs_sum_cluster_power_le hm hκ hκpos hne hν hK (hnc t htm) hsep hKin


/-- **The external jolt pair sum, with one-sided separation.**  The proof is that of
`abs_external_pair_sum_le`; the separation is used only at the pairs `(i ∈ k, j ∉ k)`. -/
lemma abs_external_pair_sum_le_weak {m : Fin N → ℝ} {k : Finset (Fin N)} {x v : EN E N}
    {Cv M ν : ℝ} (hm : ∀ i, 0 < m i) (hCv : 0 ≤ Cv)
    (hvel : ∀ j, ‖v j‖ ≤ Cv * Real.sqrt M) (hν : 0 < ν)
    (hsep : ClusterSeparatedWeak k x ν) :
    |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
      ≤ 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
          * (2 * (Cv * Real.sqrt M)) := by
  set c : ℝ := 4 * (ν⁻¹) ^ 3 * (2 * (Cv * Real.sqrt M)) with hc
  have hcpos : 0 ≤ c := by rw [hc]; positivity
  have hT : ∀ i : Fin N, (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k)
      ⊆ Finset.univ.filter (fun j : Fin N => j ∉ k) := by
    intro i j hj
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and] at hj ⊢
    exact hj.2
  have hstep1 : |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
      ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
    have hij : ν ≤ ‖x i - x j‖ := by
      have h := hsep i hi j hjk
      rwa [r_eq_norm_sub] at h
    have h1 : |inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
        ≤ 4 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (ν⁻¹) ^ 3 :=
      abs_inner_pairJolt_le hν hij
    have hp : 0 ≤ m i * m j := mul_nonneg (hm i).le (hm j).le
    rw [abs_mul, abs_of_nonneg hp]
    calc (m i * m j) * |inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
        ≤ (m i * m j) * (4 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (ν⁻¹) ^ 3) :=
          mul_le_mul_of_nonneg_left h1 hp
      _ = 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j) := by ring
  have hstep2 : (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j))
      ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hv : ‖v i - v j‖ ≤ 2 * (Cv * Real.sqrt M) := by
      calc ‖v i - v j‖ ≤ ‖v i‖ + ‖v j‖ := norm_sub_le _ _
        _ ≤ Cv * Real.sqrt M + Cv * Real.sqrt M := add_le_add (hvel i) (hvel j)
        _ = 2 * (Cv * Real.sqrt M) := by ring
    have hq : 0 ≤ ‖(cmRel m k x) i‖ := norm_nonneg _
    have hc' : 0 ≤ 4 * (ν⁻¹) ^ 3 := by positivity
    have hp : 0 ≤ m i * m j := mul_nonneg (hm i).le (hm j).le
    rw [hc]
    have hmain : 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j)
        ≤ 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (2 * (Cv * Real.sqrt M)) * (m i * m j) := by
      have hpos : 0 ≤ 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (m i * m j) := by positivity
      calc 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j)
          = (4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (m i * m j)) * ‖v i - v j‖ := by ring
        _ ≤ (4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (m i * m j)) * (2 * (Cv * Real.sqrt M)) :=
            mul_le_mul_of_nonneg_left hv hpos
        _ = 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (2 * (Cv * Real.sqrt M)) * (m i * m j) := by ring
    calc 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j)
        ≤ 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (2 * (Cv * Real.sqrt M)) * (m i * m j) := hmain
      _ = (m i * ‖(cmRel m k x) i‖) * (m j * (4 * (ν⁻¹) ^ 3 * (2 * (Cv * Real.sqrt M)))) := by
          ring
  have hstep3 : (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c))
      ≤ (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c := by
    have h1 : ∀ i ∈ k, (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c))
        ≤ (m i * ‖(cmRel m k x) i‖)
            * ((∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c) := by
      intro i _
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hsub : (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), m j)
          ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j :=
        Finset.sum_le_sum_of_subset_of_nonneg (hT i) (fun j _ _ => (hm j).le)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub hcpos)
        (mul_nonneg (hm i).le (norm_nonneg _))
    calc (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c))
        ≤ ∑ i ∈ k, (m i * ‖(cmRel m k x) i‖)
            * ((∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c) :=
          Finset.sum_le_sum h1
      _ = (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
            * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c := by
          rw [← Finset.sum_mul]
          ring
  calc |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
      ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j) := hstep1
    _ ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c) := hstep2
    _ ≤ (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c := hstep3
    _ = 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
          * (2 * (Cv * Real.sqrt M)) := by
        rw [hc]; ring


/-- **Estimate (b): the jolt pair sum of a family of simultaneously colliding clusters.** -/
theorem abs_sum_jolt_le {m : Fin N → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty)
    {ν K : ℝ} (hν : 0 < ν) (hK : 0 ≤ K)
    {x : ℝ → EN E N} {ε t : ℝ} (htm : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd3 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hKin : kinetic m (deriv x t) ≤ K)
    (hI : ∀ k ∈ ks, clusterInertia m k (x t) ≤ κ) :
    |∑ k ∈ ks, massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))|
      ≤ (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
          * Real.sqrt (2 * K / κ)
        + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
          * (2 * Real.sqrt (2 * K / κ)) := by
  classical
  have hvel : ∀ j : Fin N, ‖deriv x t j‖ ≤ 1 * Real.sqrt (2 * K / κ) := by
    intro j
    rw [one_mul]
    have h3 : m j * ‖deriv x t j‖ ^ 2 ≤ ∑ i, m i * ‖deriv x t i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin N => m i * ‖deriv x t i‖ ^ 2)
        (fun i _ => mul_nonneg (hm i).le (sq_nonneg _)) (Finset.mem_univ j)
    have h4 : (∑ i, m i * ‖deriv x t i‖ ^ 2) = 2 * kinetic m (deriv x t) := by
      rw [kinetic]; ring
    have h2 : ‖deriv x t j‖ ^ 2 ≤ 2 * K / κ := by
      rw [le_div_iff₀ hκpos]
      nlinarith [h3, h4, hKin, hκ j, sq_nonneg ‖deriv x t j‖, hκpos]
    calc ‖deriv x t j‖ = Real.sqrt (‖deriv x t j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * K / κ) := Real.sqrt_le_sqrt h2
  have hQb := fun (k : Finset (Fin N)) (_ : k ∈ ks) =>
    abs_internal_pair_sum_le (m := m) (k := k) (x := x t) (v := deriv x t)
      hm hκ hκpos (by norm_num : (0:ℝ) ≤ 1) hvel
  have hEb := fun (k : Finset (Fin N)) (hk : k ∈ ks) =>
    abs_external_pair_sum_le_weak (m := m) (k := k) (x := x t) (v := deriv x t)
      hm (by norm_num : (0:ℝ) ≤ 1) hvel hν (hsep k hk)
  have hpair : ∀ k ∈ ks, massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))
      = (∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
            * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j))
        - (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
            m i * m j * inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) i j)) :=
    fun k hk => massInner_cmRel_third_eq (m := m) (k := k) (x := x) (ε := ε) (t := t)
      htm hx (hd3 t htm) hode hnc (fun i => ne_of_gt (hm i))
      (ne_of_gt (clusterMass_pos hm (hne k hk)))
  have hq1 : ∀ k ∈ ks, (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖) ≤ clusterMass m k := by
    intro k hk
    rw [clusterMass]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [cmRel_apply_of_mem hi]
    have hle : Real.sqrt (clusterInertia m k (x t) / κ) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact (div_le_one hκpos).mpr (hI k hk)
    calc m i * ‖x t i - clusterCM m k (x t)‖ ≤ m i * 1 :=
          mul_le_mul_of_nonneg_left
            (le_trans (norm_sub_clusterCM_le_sqrt hκ hκpos hi) hle) (hm i).le
      _ = m i := mul_one _
  have hq2 : ∀ k ∈ ks, (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
      ≤ ∑ j : Fin N, m j :=
    fun k hk => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => (hm j).le)
  have hsqrt0 : 0 ≤ Real.sqrt (2 * K / κ) := Real.sqrt_nonneg _
  have hQsum : (∑ k ∈ ks, |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
        * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j)|)
      ≤ (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
          * Real.sqrt (2 * K / κ) := by
    have h1 : ∀ k ∈ ks, |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
        * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j)|
        ≤ (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2)
            * Real.sqrt (2 * K / κ) := by
      intro k hk
      have h := hQb k hk
      refine h.trans (le_of_eq ?_)
      ring
    calc (∑ k ∈ ks, |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
          * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j)|)
        ≤ ∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2)
            * Real.sqrt (2 * K / κ) := Finset.sum_le_sum h1
      _ = (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
            * Real.sqrt (2 * K / κ) := by rw [Finset.sum_mul]
  have hEsum : (∑ k ∈ ks, |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) i j)|)
      ≤ 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
          * (2 * Real.sqrt (2 * K / κ)) := by
    have h1 : ∀ k ∈ ks, |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) i j)|
        ≤ 4 * (ν⁻¹) ^ 3 * clusterMass m k * (∑ j : Fin N, m j)
            * (2 * Real.sqrt (2 * K / κ)) := by
      intro k hk
      have h := hEb k hk
      have h3 : 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
          * (2 * (1 * Real.sqrt (2 * K / κ)))
          ≤ 4 * (ν⁻¹) ^ 3 * clusterMass m k * (∑ j : Fin N, m j)
            * (2 * Real.sqrt (2 * K / κ)) := by
        have hν3 : 0 ≤ (ν⁻¹) ^ 3 := by positivity
        have ha := hq1 k hk
        have hb := hq2 k hk
        have ha0 : 0 ≤ (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (norm_nonneg _)
        have hb0 : 0 ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) :=
          Finset.sum_nonneg fun j _ => (hm j).le
        have hcm0 : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
        have hsm0 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
        have hA : 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖)
            ≤ 4 * (ν⁻¹) ^ 3 * clusterMass m k :=
          mul_le_mul_of_nonneg_left ha (by positivity)
        have hB : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) ≤ ∑ j, m j :=
          hq2 k hk
        have h2K : 0 ≤ 2 * Real.sqrt (2 * K / κ) := by positivity
        calc 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖)
              * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
              * (2 * (1 * Real.sqrt (2 * K / κ)))
            ≤ (4 * (ν⁻¹) ^ 3 * clusterMass m k) * (∑ j : Fin N, m j)
              * (2 * (1 * Real.sqrt (2 * K / κ))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul hA hB hb0 (by positivity)) (by positivity)
          _ = 4 * (ν⁻¹) ^ 3 * clusterMass m k * (∑ j : Fin N, m j)
              * (2 * Real.sqrt (2 * K / κ)) := by ring
      linarith [h, h3]
    calc (∑ k ∈ ks, |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          m i * m j * inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) i j)|)
        ≤ ∑ k ∈ ks, 4 * (ν⁻¹) ^ 3 * clusterMass m k * (∑ j : Fin N, m j)
            * (2 * Real.sqrt (2 * K / κ)) := Finset.sum_le_sum h1
      _ = (4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (2 * Real.sqrt (2 * K / κ)))
            * (∑ k ∈ ks, clusterMass m k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
            * (2 * Real.sqrt (2 * K / κ)) := by ring
  calc |∑ k ∈ ks, massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))|
      = |∑ k ∈ ks, ((∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
              * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j))
            - (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
                m i * m j * inner ℝ ((cmRel m k (x t)) i)
                  (pairJolt (x t) (deriv x t) i j)))| := by
          rw [Finset.sum_congr rfl hpair]
    _ ≤ ∑ k ∈ ks, |(∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
              * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j))
            - (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
                m i * m j * inner ℝ ((cmRel m k (x t)) i)
                  (pairJolt (x t) (deriv x t) i j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ ks, (|∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
              * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j)|
            + |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
                m i * m j * inner ℝ ((cmRel m k (x t)) i)
                  (pairJolt (x t) (deriv x t) i j)|) :=
          Finset.sum_le_sum fun k _ => abs_sub_le_abs_add _ _
    _ = (∑ k ∈ ks, |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
              * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j)|)
          + (∑ k ∈ ks, |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
              m i * m j * inner ℝ ((cmRel m k (x t)) i)
                (pairJolt (x t) (deriv x t) i j)|) := Finset.sum_add_distrib
    _ ≤ (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
          * Real.sqrt (2 * K / κ)
        + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
          * (2 * Real.sqrt (2 * K / κ)) := add_le_add hQsum hEsum


/-- **The third-derivative (jolt) bound for the sum of the moments of inertia.**  This is the input
`Commons.Analysis.Calculus.second_deriv_asymptotic_of_third_deriv_bound` needs.  The analytic input
is deliberately minimal — the caller (`MarchalMultiAsymptotic`, from the F1 geometry) supplies

* `hsep`  : the one-sided separation of each cluster from the rest,
* `hIk`   : `clusterInertia m k (x t) ≤ κ` (small inertia, for the jolt estimate),
* `hKin`  : `kinetic m (deriv x t) ≤ cU * f̈(t)` (kinetic energy controlled by the second derivative),
* `hPerr` : `2 * ∑_k U_k(x t) ≤ f̈(t) + 6C` (Lagrange–Jacobi + bounded energies),
* `hP1`   : `1 ≤ f̈(t)`,

and the conclusion is `∃ e > 0, |f'''| ≤ e · (f̈)^{5/2}` on `(0, ε)`. -/
theorem multiInertia_third_deriv_bound {m : Fin N → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty) (hne2 : ∀ k ∈ ks, 2 ≤ k.card)
    {x : ℝ → EN E N} {ε ν C cU : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hν : 0 < ν) (hcU : 0 ≤ cU)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hIk : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, clusterInertia m k (x t) ≤ κ)
    (hKin : ∀ t ∈ Ioo (0:ℝ) ε,
      kinetic m (deriv x t) ≤ cU * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
    (hPerr : ∀ t ∈ Ioo (0:ℝ) ε, 2 * multiPotential m ks (x t)
      ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C)
    (hP1 : ∀ t ∈ Ioo (0:ℝ) ε,
      1 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t ∈ Ioo (0:ℝ) ε,
        |deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t|
          ≤ e * (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) ^ ((5:ℝ)/2) := by
  classical
  -- the constants
  set A1 : ℝ := (max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1)
      * (∑ k ∈ ks, Real.sqrt (clusterMass m k)) with hA1def
  have hA10 : 0 ≤ A1 := by rw [hA1def]; positivity
  set M2 : ℝ := 2 * (N : ℝ) ^ 2 * (κ⁻¹) ^ 2 with hM2def
  have hM20 : 0 ≤ M2 := by rw [hM2def]; positivity
  set cc : ℝ := max 1 ((6 * C + 1) / 2) with hccdef
  have hcc1 : 1 ≤ cc := by rw [hccdef]; exact le_max_left _ _
  have hcc0 : 0 ≤ cc := le_trans zero_le_one hcc1
  have hccle : (6 * C + 1) / 2 ≤ cc := by rw [hccdef]; exact le_max_right _ _
  refine ⟨max 1 (12 * A1 * Real.sqrt (2 * cU) * cc ^ 2
      + 2 * (M2 * cc ^ 2 + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
        * Real.sqrt (2 * cU / κ)), lt_of_lt_of_le one_pos (le_max_left _ _), fun t ht => ?_⟩
  -- item 1: the internal-potential sum
  have hu0 : ∀ k ∈ ks, 0 ≤ clusterPotential m k (x t) := fun k _ =>
    Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hcard : ∀ k ∈ ks, (k.card : ℝ) ≤ (N : ℝ) := by
    intro k hk
    have h1 : k.card ≤ N := by
      simpa using Finset.card_le_card (Finset.subset_univ k)
    exact_mod_cast h1
  have hQb : (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
      ≤ M2 * (multiPotential m ks (x t)) ^ 2 := by
    calc (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
        ≤ ∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (N : ℝ) ^ 2 * (κ⁻¹) ^ 2) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hsq : (k.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg k.card) (hcard k hk) 2
          have h2 : (2 : ℝ) * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2
              ≤ 2 * (N : ℝ) ^ 2 * (κ⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = M2 * ∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 := by
          rw [hM2def, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ M2 * (∑ k ∈ ks, clusterPotential m k (x t)) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_sq_le_sq_sum_of_nonneg hu0) hM20
      _ = M2 * (multiPotential m ks (x t)) ^ 2 := rfl
  -- hUle
  have hUle : multiPotential m ks (x t)
      ≤ cc * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t := by
    have h1 := hPerr t ht
    have h2 := hP1 t ht
    have h3 : (6 * C + 1) / 2 * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        ≤ cc * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t :=
      mul_le_mul_of_nonneg_right hccle (by linarith)
    nlinarith [h1, h2, h3]
  -- hUle2
  have hU0 : 0 ≤ multiPotential m ks (x t) := multiPotential_nonneg (fun i => (hm i).le) ks (x t)
  have hUle2 : (multiPotential m ks (x t)) ^ 2
      ≤ cc ^ 2 * (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) ^ 2 := by
    have hPp : 0 < deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t :=
      lt_of_lt_of_le one_pos (hP1 t ht)
    have h1 : multiPotential m ks (x t) * multiPotential m ks (x t)
        ≤ (cc * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
          * (cc * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) :=
      mul_le_mul hUle hUle hU0 (mul_nonneg hcc0 hPp.le)
    nlinarith [h1]
  -- hK0
  have hK0 : 0 ≤ cU * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t :=
    mul_nonneg hcU (le_trans zero_le_one (hP1 t ht))
  -- set Pt, then hsqK and hkey
  set Pt : ℝ := deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t with hPtdef
  have hPtpos : 0 < Pt := by rw [hPtdef]; exact lt_of_lt_of_le one_pos (hP1 t ht)
  have hsqK : Real.sqrt (2 * (cU * Pt)) ≤ Real.sqrt (2 * cU) * Real.sqrt Pt := by
    rw [show (2:ℝ) * (cU * Pt) = (2 * cU) * Pt by ring, Real.sqrt_mul (by positivity)]
  have hkey : Real.sqrt Pt * (1 + Pt ^ 2) ≤ 2 * Pt ^ ((5:ℝ)/2) := by
    have h1 : Real.sqrt Pt = Pt ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow Pt
    have h2 : Pt ^ ((1:ℝ)/2) * Pt ^ 2 = Pt ^ ((5:ℝ)/2) := by
      rw [show Pt ^ 2 = Pt ^ (2:ℝ) from (Real.rpow_natCast Pt 2).symm, ← Real.rpow_add hPtpos]
      norm_num
    have h3 : Pt ^ ((1:ℝ)/2) ≤ Pt ^ ((5:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le (hP1 t ht) (by norm_num)
    rw [h1, mul_add, mul_one, h2]
    linarith [h3]
  -- chain (a)
  have ha := abs_sum_massInner_cmRel_deriv_le (m := m) (κ := κ) hm hκ hκpos (ks := ks) hne
    (ν := ν) (K := cU * Pt) hν hK0 (x := x) (ε := ε) (t := t) ht hnc hode (hsep t ht) (hKin t ht)
  have ha' : |∑ k ∈ ks, massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))|
      ≤ A1 * Real.sqrt (2 * (cU * Pt)) * (1 + (multiPotential m ks (x t)) ^ 2) := by
    rw [hA1def]
    exact ha
  have hcc2 : (1:ℝ) ≤ cc ^ 2 := by nlinarith [hcc1]
  have hA1b : |∑ k ∈ ks, massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))|
      ≤ A1 * Real.sqrt (2 * cU) * cc ^ 2 * (2 * Pt ^ ((5:ℝ)/2)) := by
    refine ha'.trans ?_
    have h1 : (1:ℝ) + cc ^ 2 * Pt ^ 2 ≤ cc ^ 2 * (1 + Pt ^ 2) := by
      nlinarith [hcc2, sq_nonneg Pt]
    have h3 : (1:ℝ) + (multiPotential m ks (x t)) ^ 2 ≤ 1 + cc ^ 2 * Pt ^ 2 := by
      linarith [hUle2]
    calc A1 * Real.sqrt (2 * (cU * Pt)) * (1 + (multiPotential m ks (x t)) ^ 2)
        ≤ A1 * (Real.sqrt (2 * cU) * Real.sqrt Pt) * (1 + cc ^ 2 * Pt ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqK hA10) h3 (by positivity) (by positivity)
      _ = A1 * Real.sqrt (2 * cU) * (Real.sqrt Pt * (1 + cc ^ 2 * Pt ^ 2)) := by ring
      _ ≤ A1 * Real.sqrt (2 * cU) * (cc ^ 2 * (Real.sqrt Pt * (1 + Pt ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc Real.sqrt Pt * (1 + cc ^ 2 * Pt ^ 2)
              ≤ Real.sqrt Pt * (cc ^ 2 * (1 + Pt ^ 2)) :=
                mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg Pt)
            _ = cc ^ 2 * (Real.sqrt Pt * (1 + Pt ^ 2)) := by ring
      _ = A1 * Real.sqrt (2 * cU) * cc ^ 2 * (Real.sqrt Pt * (1 + Pt ^ 2)) := by ring
      _ ≤ A1 * Real.sqrt (2 * cU) * cc ^ 2 * (2 * Pt ^ ((5:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
  -- chain (b)
  have hb := abs_sum_jolt_le (m := m) (κ := κ) hm hκ hκpos (ks := ks) hne
    (ν := ν) (K := cU * Pt) hν hK0 (x := x) (ε := ε) (t := t) ht hx hd3 hode hnc
    (hsep t ht) (hKin t ht) (hIk t ht)
  have hb2 : |∑ k ∈ ks, massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))|
      ≤ (M2 * cc ^ 2 * Pt ^ 2
          + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
          * Real.sqrt (2 * cU / κ) * Real.sqrt Pt := by
    refine hb.trans ?_
    have hsq : Real.sqrt (2 * (cU * Pt) / κ) ≤ Real.sqrt (2 * cU / κ) * Real.sqrt Pt := by
      rw [show 2 * (cU * Pt) / κ = (2 * cU / κ) * Pt by ring, Real.sqrt_mul (by positivity)]
    have hfirst : (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
        ≤ M2 * cc ^ 2 * Pt ^ 2 := by
      refine (le_trans hQb (mul_le_mul_of_nonneg_left hUle2 hM20)).trans (le_of_eq ?_)
      ring_nf
    have hbound1 : (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
          * Real.sqrt (2 * (cU * Pt) / κ)
        ≤ (M2 * cc ^ 2 * Pt ^ 2) * (Real.sqrt (2 * cU / κ) * Real.sqrt Pt) :=
      mul_le_mul hfirst hsq (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg hM20 (sq_nonneg cc)) (sq_nonneg Pt))
    have hbound2 : 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
          * (2 * Real.sqrt (2 * (cU * Pt) / κ))
        ≤ 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
          * (2 * (Real.sqrt (2 * cU / κ) * Real.sqrt Pt)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (by
          have hm0 : (0:ℝ) ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
          have hmk0 : (0:ℝ) ≤ ∑ k ∈ ks, clusterMass m k :=
            Finset.sum_nonneg fun k _ => clusterMass_nonneg (fun i => (hm i).le) k
          positivity)
    have hle : Real.sqrt Pt ≤ Pt ^ ((5:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow Pt]
      exact Real.rpow_le_rpow_of_exponent_le (hP1 t ht) (by norm_num)
    calc (∑ k ∈ ks, (clusterPotential m k (x t)) ^ 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2))
            * Real.sqrt (2 * (cU * Pt) / κ)
          + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
            * (2 * Real.sqrt (2 * (cU * Pt) / κ))
        ≤ (M2 * cc ^ 2 * Pt ^ 2) * (Real.sqrt (2 * cU / κ) * Real.sqrt Pt)
          + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k)
            * (2 * (Real.sqrt (2 * cU / κ) * Real.sqrt Pt)) := add_le_add hbound1 hbound2
      _ = (M2 * cc ^ 2 * Pt ^ 2
            + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
            * Real.sqrt (2 * cU / κ) * Real.sqrt Pt := by ring_nf
  -- the triangle step and the final constant
  set A1s : ℝ := ∑ k ∈ ks, massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)) with hA1s
  set A2s : ℝ := ∑ k ∈ ks, massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t)) with hA2s
  have hthird := multiInertia_third_deriv_eq (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
    ht hx hd2 hd3
  have hthird' : deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t = 6 * A1s + 2 * A2s := by
    rw [hA1s, hA2s]
    exact hthird
  have hA1s' : |A1s| ≤ A1 * Real.sqrt (2 * cU) * cc ^ 2 * (2 * Pt ^ ((5:ℝ)/2)) := by
    rw [hA1s]; exact hA1b
  have hA2s' : |A2s| ≤ (M2 * cc ^ 2 * Pt ^ 2
        + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
        * Real.sqrt (2 * cU / κ) * Real.sqrt Pt := by
    rw [hA2s]; exact hb2
  have hPt2sqrt : Pt ^ 2 * Real.sqrt Pt = Pt ^ ((5:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow Pt, show Pt ^ 2 = Pt ^ (2:ℝ) from (Real.rpow_natCast Pt 2).symm,
      ← Real.rpow_add hPtpos]
    norm_num
  have hCc : 0 ≤ 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2 := by
    have hm0 : (0:ℝ) ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have hmk0 : (0:ℝ) ≤ ∑ k ∈ ks, clusterMass m k :=
      Finset.sum_nonneg fun k _ => clusterMass_nonneg (fun i => (hm i).le) k
    positivity
  have h1 : |6 * A1s + 2 * A2s| ≤ 6 * |A1s| + 2 * |A2s| := by
    have h := abs_add_le (6 * A1s) (2 * A2s)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h
  have h2 : 6 * |A1s| ≤ 12 * A1 * Real.sqrt (2 * cU) * cc ^ 2 * Pt ^ ((5:ℝ)/2) := by
    refine (mul_le_mul_of_nonneg_left hA1s' (by norm_num)).trans (le_of_eq ?_)
    ring
  have h3 : 2 * |A2s| ≤ 2 * ((M2 * cc ^ 2 * Pt ^ 2
        + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
        * Real.sqrt (2 * cU / κ) * Real.sqrt Pt) :=
    mul_le_mul_of_nonneg_left hA2s' (by norm_num)
  have hle : Real.sqrt Pt ≤ Pt ^ ((5:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow Pt]
    exact Real.rpow_le_rpow_of_exponent_le (hP1 t ht) (by norm_num)
  have hB : (M2 * cc ^ 2 * Pt ^ 2
        + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
        * Real.sqrt (2 * cU / κ) * Real.sqrt Pt
      ≤ M2 * cc ^ 2 * Pt ^ ((5:ℝ)/2) * Real.sqrt (2 * cU / κ)
        + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2
          * Real.sqrt (2 * cU / κ) * Pt ^ ((5:ℝ)/2) := by
    rw [show (M2 * cc ^ 2 * Pt ^ 2
          + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
          * Real.sqrt (2 * cU / κ) * Real.sqrt Pt
        = M2 * cc ^ 2 * (Pt ^ 2 * Real.sqrt Pt) * Real.sqrt (2 * cU / κ)
          + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2
            * Real.sqrt (2 * cU / κ) * Real.sqrt Pt by ring, hPt2sqrt]
    refine add_le_add le_rfl ?_
    refine mul_le_mul_of_nonneg_left (le_trans hle ?_) ?_
    · linarith [Real.rpow_nonneg hPtpos.le ((5:ℝ)/2)]
    · have hm0 : (0:ℝ) ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
      have hmk0 : (0:ℝ) ≤ ∑ k ∈ ks, clusterMass m k :=
        Finset.sum_nonneg fun k _ => clusterMass_nonneg (fun i => (hm i).le) k
      positivity
  calc |deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t|
      = |6 * A1s + 2 * A2s| := by rw [hthird']
    _ ≤ 6 * |A1s| + 2 * |A2s| := h1
    _ ≤ 12 * A1 * Real.sqrt (2 * cU) * cc ^ 2 * Pt ^ ((5:ℝ)/2)
        + 2 * (M2 * cc ^ 2 * Pt ^ ((5:ℝ)/2) * Real.sqrt (2 * cU / κ)
          + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2
            * Real.sqrt (2 * cU / κ) * Pt ^ ((5:ℝ)/2)) := by
        refine add_le_add h2 ?_
        refine h3.trans ?_
        exact mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = (12 * A1 * Real.sqrt (2 * cU) * cc ^ 2
        + 2 * (M2 * cc ^ 2 + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
          * Real.sqrt (2 * cU / κ)) * Pt ^ ((5:ℝ)/2) := by ring
    _ ≤ (max 1 (12 * A1 * Real.sqrt (2 * cU) * cc ^ 2
        + 2 * (M2 * cc ^ 2 + 4 * (ν⁻¹) ^ 3 * (∑ j : Fin N, m j) * (∑ k ∈ ks, clusterMass m k) * 2)
          * Real.sqrt (2 * cU / κ))) * Pt ^ ((5:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hPtpos.le _)

/-- **`HasDerivAt` form of the third derivative of the sum of the moments of inertia.** -/
lemma hasDerivAt_deriv_deriv_multiInertia_curve {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t : ℝ} (htm : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hd3 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) s) s) :
    HasDerivAt (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))))
      (deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t) t := by
  classical
  have hxev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact hx s hs
  -- `deriv f =ᶠ G2`
  have hG2 : deriv (fun s : ℝ => multiInertia m ks (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact (hasDerivAt_sum_apply ks (fun k (r : ℝ) => clusterInertia m k (x r))
      (fun k => deriv (fun r : ℝ => clusterInertia m k (x r)) s) s
      (fun k _ => hasDerivAt_clusterInertia_curve (k := k) (t := s) (x := x)
        (by filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr; exact hx r hr))).deriv
  -- `deriv G2 =ᶠ G3`
  have hG3 : deriv (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact (hasDerivAt_sum_apply ks (fun k (r : ℝ) => deriv (fun u : ℝ => clusterInertia m k (x u)) r)
      (fun k => deriv (deriv (fun u : ℝ => clusterInertia m k (x u))) s) s
      (fun k _ => hasDerivAt_deriv_clusterInertia_curve (k := k) (t := s)
        (by filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr; exact hx r hr)
        (hd2 s hs))).deriv
  have eG : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) s) :=
    (Filter.EventuallyEq.deriv hG2).trans hG3
  have hsum3 : HasDerivAt
      (fun s : ℝ => ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) s)
      (∑ k ∈ ks, deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) t) t :=
    hasDerivAt_sum_apply ks (fun k (s : ℝ) => deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) s)
      (fun k => deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) t) t
      (fun k _ => hasDerivAt_deriv_deriv_clusterInertia_curve (m := m) (k := k) (x := x) (ε := ε)
        htm hx hd2 hd3)
  have h1 : HasDerivAt (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))))
      (∑ k ∈ ks, deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) t) t :=
    hsum3.congr_of_eventuallyEq eG
  have h2 : deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t
      = ∑ k ∈ ks, deriv (deriv (deriv (fun r : ℝ => clusterInertia m k (x r)))) t := by
    rw [Filter.EventuallyEq.deriv_eq eG]
    exact hsum3.deriv
  rw [h2]
  exact h1

/-- **The asymptotic of the second derivative of the sum of the moments of inertia.**  Feeding the
jolt bound `multiInertia_third_deriv_bound` into Sundman's Tauberian lemma
(`second_deriv_asymptotic_of_third_deriv_bound`) turns the crude bound `f̈ f^{1/2} ≥ d` into the
genuine limit `f̈(t) · f(t)^{1/2} → η/4`. -/
theorem multiInertia_second_deriv_asymptotic {m : Fin N → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty) (hne2 : ∀ k ∈ ks, 2 ≤ k.card)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    {x : ℝ → EN E N} {ε ν C cU : ℝ} (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν) (hcU : 0 ≤ cU)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |multiCrossWork m ks (x t)| ≤ C)
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hIk : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, clusterInertia m k (x t) ≤ κ)
    (hKin : ∀ t ∈ Ioo (0:ℝ) ε,
      kinetic m (deriv x t) ≤ cU * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
    (hPerr : ∀ t ∈ Ioo (0:ℝ) ε, 2 * multiPotential m ks (x t)
      ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C)
    (hP1 : ∀ t ∈ Ioo (0:ℝ) ε,
      1 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < multiInertia m ks (x t))
    (hI : Tendsto (fun t : ℝ => multiInertia m ks (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ η : ℝ, 0 < η ∧ Tendsto
      (fun t : ℝ => deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        * (multiInertia m ks (x t)) ^ ((1:ℝ)/2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (η / 4)) := by
  classical
  obtain ⟨ck, hckpos, hckle⟩ := exists_const_le_multiPotential (E := E) hm ks hne2
  -- shrink eps2 so that `6*C*sqrt(f) <= ck/2`
  have hsqrtf0 : Tendsto (fun t : ℝ => Real.sqrt (multiInertia m ks (x t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp hI
    simpa only [Function.comp_def, Real.sqrt_zero] using h1
  have hthr : (0:ℝ) < ck / (12 * C) := by positivity
  obtain ⟨ε₂, hε₂pos, hε₂le, hε₂⟩ : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ ε ∧
      ∀ t ∈ Ioo (0:ℝ) ε₂, Real.sqrt (multiInertia m ks (x t)) < ck / (12 * C) := by
    have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
        Real.sqrt (multiInertia m ks (x t)) < ck / (12 * C) :=
      hsqrtf0.eventually (isOpen_Iio.mem_nhds hthr)
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, fun t ht => hδ t ?_ ht.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact lt_of_lt_of_le ht.2 (min_le_left _ _)
  -- hbound
  have hbound : ∀ t ∈ Ioo (0:ℝ) ε₂,
      ck / 2 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        * (multiInertia m ks (x t)) ^ ((1:ℝ)/2) := by
    intro t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩
    have hsqrtpos : 0 < Real.sqrt (multiInertia m ks (x t)) :=
      Real.sqrt_pos.mpr (hfpos t htε)
    have hge := multiInertia_second_deriv_ge (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
      (C := C) (ck := ck) hm hne htε hnc hx
      (fun s hs => (hd2 s hs).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x s).symm) hode
      (abs_le.mp (hE t htε)).1 (abs_le.mp (hW t htε)).1 (hckle (x t) (hnc t htε))
    have hmul := mul_le_mul_of_nonneg_right hge hsqrtpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hsqrtpos)] at hmul
    have h6 : 6 * C * Real.sqrt (multiInertia m ks (x t)) ≤ ck / 2 := by
      have h1 : 6 * C * Real.sqrt (multiInertia m ks (x t)) < 6 * C * (ck / (12 * C)) :=
        mul_lt_mul_of_pos_left (hε₂ t ht) (by positivity)
      have h2 : 6 * C * (ck / (12 * C)) = ck / 2 := by field_simp; ring
      linarith
    rw [← Real.sqrt_eq_rpow]
    nlinarith [hmul, h6, hsqrtpos]
  -- hmono
  have hf1 : ∀ t ∈ Ioo (0:ℝ) ε₂, HasDerivAt (fun s : ℝ => multiInertia m ks (x s))
      (deriv (fun s : ℝ => multiInertia m ks (x s)) t) t := by
    intro t ht
    exact hasDerivAt_multiInertia_curve (m := m) (ks := ks) (x := x) (t := t)
      (by filter_upwards [isOpen_Ioo.mem_nhds ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩] with s hs
          exact hx s hs)
  have hf2 : ∀ t ∈ Ioo (0:ℝ) ε₂,
      HasDerivAt (deriv (fun s : ℝ => multiInertia m ks (x s)))
        (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) t := by
    intro t ht
    exact hasDerivAt_deriv_multiInertia_curve (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
      ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩ (fun s hs => hx s hs) (fun s hs => hd2 s hs)
  have hmono : ∀ t ∈ Ioo (0:ℝ) ε₂, 0 ≤ deriv (fun s : ℝ => multiInertia m ks (x s)) t :=
    deriv_nonneg_of_second_deriv_mul_sqrt_ge (f := fun s : ℝ => multiInertia m ks (x s))
      (d := ck / 2) hε₂pos (by positivity) hf1 hf2
      (fun t ht => hfpos t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩) hbound hI
  -- hineq
  have hineq : ∀ t ∈ Ioo (0:ℝ) ε₂,
      (deriv (fun s : ℝ => multiInertia m ks (x s)) t) ^ (2:ℕ)
        ≤ 4 * multiInertia m ks (x t) * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
          + 16 * C * multiInertia m ks (x t) := by
    intro t ht
    exact multiInertia_deriv_sq_le (m := m) (ks := ks) (x := x) (ε := ε) (t := t) (C := C)
      hm hne ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩ hnc hx
      (fun s hs => (hd2 s hs).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x s).symm)
      hode (hE t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩) (hW t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
  -- the Sundman ratio
  obtain ⟨η, hηpos, hη⟩ := Commons.Analysis.Calculus.sundman_asymptotic_ratio
    (f := fun s : ℝ => multiInertia m ks (x s)) (b := 4) (c := 16 * C) (d := ck / 2)
    hε₂pos (by norm_num) (by positivity) hf1 hf2
    (fun t ht => hfpos t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩) hineq hmono hI
    (fun t ht => by
      rw [show ((4:ℝ) - 2)/4 = (1:ℝ)/2 by norm_num]
      exact hbound t ht)
  -- the jolt bound (conclusion is `∀ t ∈ Ioo 0 ε₂`, no extra threshold)
  obtain ⟨e, hepos, hthird⟩ := multiInertia_third_deriv_bound
    (m := m) (κ := κ) hm hκ hκpos (ks := ks) hne hne2
    (x := x) (ε := ε₂) (ν := ν) (C := C) (cU := cU)
    hε₂pos hC hν hcU
    (fun t ht => hnc t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hx t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hd2 t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hd3 t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hode t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hsep t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht k hk => hIk t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩ k hk)
    (fun t ht => hKin t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hPerr t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    (fun t ht => hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)

  -- hf3
  have hf3 : ∀ t ∈ Ioo (0:ℝ) ε₂,
      HasDerivAt (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))))
        (deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t) t :=
    fun t ht => hasDerivAt_deriv_deriv_multiInertia_curve (m := m) (ks := ks) (x := x) (ε := ε)
      ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩ hx hd2 hd3
  -- the Tauberian close
  have hbound' : ∀ t ∈ Ioo (0:ℝ) ε₂,
      ck / 2 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        * (multiInertia m ks (x t)) ^ (((4:ℝ) - 2) / 4) := by
    intro t ht
    rw [show ((4:ℝ) - 2) / 4 = (1:ℝ)/2 by norm_num]
    exact hbound t ht
  have hthird' : ∀ t ∈ Ioo (0:ℝ) ε₂,
      |deriv (deriv (deriv (fun s : ℝ => multiInertia m ks (x s)))) t|
        ≤ e * (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
            ^ (((2:ℝ) * 4 - 3) / (4 - 2)) := by
    intro t ht
    rw [show (((2:ℝ) * 4 - 3) / (4 - 2)) = (5:ℝ)/2 by norm_num]
    exact hthird t ht
  have hfin := Commons.Analysis.Calculus.second_deriv_asymptotic_of_third_deriv_bound
    (f := fun s : ℝ => multiInertia m ks (x s)) (b := 4) (c := 16 * C) (d := ck / 2) (e := e)
    (η := η) (ε := ε₂) hε₂pos (by norm_num) (by positivity) hepos hηpos
    hf1 hf2 hf3 (fun t ht => hfpos t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩) hineq hmono hI hbound' hthird' hη
  rw [show ((4:ℝ) - 2) / 4 = (1:ℝ)/2 by norm_num] at hfin
  exact ⟨η, hηpos, hfin⟩
/-- **The sum-level kinetic bound.**  Keeping the boundedness of the outside and centre-of-mass
kinetic energies as hypotheses, the Tauberian analysis also yields `K ≤ Ck t^{-2/3}`. -/
theorem multiInertia_kinetic_bound {m : Fin N → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    {ks : Finset (Finset (Fin N))} (hne : ∀ k ∈ ks, k.Nonempty) (hne2 : ∀ k ∈ ks, 2 ≤ k.card)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    {x : ℝ → EN E N} {ε ν C cU Cout Ccm2 : ℝ} (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν) (hcU : 0 ≤ cU)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hKout : ∀ t ∈ Ioo (0:ℝ) ε, multiOutsideKineticSq m ks (deriv x t) ≤ Cout)
    (hKcm : ∀ t ∈ Ioo (0:ℝ) ε, multiCMKineticSq m ks (deriv x t) ≤ Ccm2)
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |multiCrossWork m ks (x t)| ≤ C)
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hIk : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, clusterInertia m k (x t) ≤ κ)
    (hKin : ∀ t ∈ Ioo (0:ℝ) ε,
      kinetic m (deriv x t) ≤ cU * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
    (hPerr : ∀ t ∈ Ioo (0:ℝ) ε, 2 * multiPotential m ks (x t)
      ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C)
    (hP1 : ∀ t ∈ Ioo (0:ℝ) ε,
      1 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < multiInertia m ks (x t))
    (hI : Tendsto (fun t : ℝ => multiInertia m ks (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ Ck : ℝ, 0 < Ck ∧
      ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), kinetic m (deriv x t) ≤ Ck * t ^ (-((2:ℝ)/3)) := by
  obtain ⟨η, hηpos, hfin⟩ := multiInertia_second_deriv_asymptotic (m := m) (κ := κ) hm hκ hκpos
    hne hne2 hedj hε hC hν hcU hnc hx hd2 hd3 hode hE hW hsep hIk hKin hPerr hP1 hfpos hI
  obtain ⟨ε₂, hε₂pos, hε₂le⟩ : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_left _ _⟩

  -- the hinge instantiation
  obtain ⟨k0, hk0pos, hklim⟩ := multiInertia_asymptotic (m := m) (ks := ks) (x := x) (ε := ε) (C := C)
    hm hne hne2 hε hC hnc hx
    (fun t ht => (hd2 t ht).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t).symm)
    hode hE hW hfpos hI
  have h2hinge := tendsto_rpow_half_of_tendsto_div_rpow
    (f := fun t : ℝ => multiInertia m ks (x t)) hk0pos hklim
  have hhinge := hinge (f := fun t : ℝ => multiInertia m ks (x t)) (η := η) (κ := k0) (ε := ε₂)
    (by positivity) hk0pos hε₂pos (fun t ht => hfpos t ⟨ht.1, lt_of_lt_of_le ht.2 hε₂le⟩)
    hfin h2hinge
  have hstep1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        ≤ ((η / 4) / Real.sqrt k0 + 1) * t ^ (-((2:ℝ)/3)) := by
    have hc : (η / 4) / Real.sqrt k0 < (η / 4) / Real.sqrt k0 + 1 := by linarith
    have hev := hhinge.eventually (eventually_le_nhds hc)
    filter_upwards [hev, Ioo_mem_nhdsGT hε₂pos] with t ht htI
    have ht0 : 0 < t := htI.1
    have h1 : t ^ ((2:ℝ)/3) * t ^ (-((2:ℝ)/3)) = 1 := by
      rw [← Real.rpow_add ht0, show ((2:ℝ)/3 + -((2:ℝ)/3)) = 0 by norm_num, Real.rpow_zero]
    calc deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        = deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
            * (t ^ ((2:ℝ)/3) * t ^ (-((2:ℝ)/3))) := by rw [h1, mul_one]
      _ = (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t * t ^ ((2:ℝ)/3))
            * t ^ (-((2:ℝ)/3)) := by ring
      _ ≤ ((η / 4) / Real.sqrt k0 + 1) * t ^ (-((2:ℝ)/3)) :=
          mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg ht0.le _)
  have hUle : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      2 * multiPotential m ks (x t)
        ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C := by
    filter_upwards [Ioo_mem_nhdsGT hε₂pos] with t htI
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨htI.1, lt_of_lt_of_le htI.2 hε₂le⟩
    have hLJ := deriv_deriv_multiInertia_curve_eq (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
      hm hne htε hnc hx
      (fun s hs => (hd2 s hs).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x s).symm) hode
    have h1 := (abs_le.mp (hE t htε)).1
    have h2 := (abs_le.mp (hW t htε)).1
    linarith
  -- the derived nonnegativities (look like hypotheses, but follow from `hKout`/`hKcm`)
  have hε2mem : ε / 2 ∈ Ioo (0:ℝ) ε := ⟨by linarith, by linarith⟩
  have hCout0 : 0 ≤ Cout := by
    have h := hKout (ε / 2) hε2mem
    have h0 : 0 ≤ multiOutsideKineticSq m ks (deriv x (ε / 2)) := by
      rw [multiOutsideKineticSq]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
    linarith
  have hCcm20 : 0 ≤ Ccm2 := by
    have h := hKcm (ε / 2) hε2mem
    have h0 : 0 ≤ multiCMKineticSq m ks (deriv x (ε / 2)) := by
      rw [multiCMKineticSq]
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)
    linarith
  have hC00 : 0 ≤ C + Cout / 2 + Ccm2 / 2 := by linarith [hC.le, hCout0, hCcm20]
  have hk0pos' : 0 < k0 := hk0pos
  have hcKpos : 0 < ((η / 4) / Real.sqrt k0 + 1) / 2 + 3 * C + (C + Cout / 2 + Ccm2 / 2) := by
    have h1 : 0 < (η / 4) / Real.sqrt k0 := div_pos (by positivity) (Real.sqrt_pos.mpr hk0pos')
    linarith [h1, hC, hCout0, hCcm20]
  have hKbound : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      kinetic m (deriv x t) ≤ multiPotential m ks (x t) + (C + Cout / 2 + Ccm2 / 2) := by
    filter_upwards [Ioo_mem_nhdsGT hε₂pos] with t htI
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨htI.1, lt_of_lt_of_le htI.2 hε₂le⟩
    have hke := kinetic_le_multi ks hm hne hedj x t
    have h1 := (abs_le.mp (hE t htε)).2
    have h2 := hKout t htε
    have h3 := hKcm t htε
    linarith [hke, h1, h2, h3]
  have hfin_all : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
          ≤ ((η / 4) / Real.sqrt k0 + 1) * t ^ (-((2:ℝ)/3))
        ∧ 2 * multiPotential m ks (x t)
            ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t + 6 * C
        ∧ kinetic m (deriv x t) ≤ multiPotential m ks (x t) + (C + Cout / 2 + Ccm2 / 2)
        ∧ t ≤ 1 := by
    filter_upwards [hstep1, hUle, hKbound, Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)]
      with t a b c d
    exact ⟨a, b, c, le_of_lt d.2⟩
  have hKfinal : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      kinetic m (deriv x t)
        ≤ (((η / 4) / Real.sqrt k0 + 1) / 2 + 3 * C + (C + Cout / 2 + Ccm2 / 2))
          * t ^ (-((2:ℝ)/3)) := by
    filter_upwards [hfin_all, Ioo_mem_nhdsGT hε₂pos] with t h htI
    obtain ⟨h1, h2, h3, h4⟩ := h
    have ht0 : 0 < t := htI.1
    have hpow : (1:ℝ) ≤ t ^ (-((2:ℝ)/3)) := by
      have hle : t ^ ((2:ℝ)/3) ≤ 1 := Real.rpow_le_one ht0.le h4 (by norm_num)
      have hpos : 0 < t ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
      have hneg : t ^ (-((2:ℝ)/3)) = 1 / t ^ ((2:ℝ)/3) := by
        rw [Real.rpow_neg ht0.le]; ring
      rw [hneg]
      exact (one_le_div hpos).mpr hle
    have hC0 : 0 ≤ C + Cout / 2 + Ccm2 / 2 := by
      have hε2 : ε / 2 ∈ Ioo (0:ℝ) ε := ⟨by linarith, by linarith⟩
      have hout0 : 0 ≤ multiOutsideKineticSq m ks (deriv x (ε / 2)) := by
        rw [multiOutsideKineticSq]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
      have hcm0 : 0 ≤ multiCMKineticSq m ks (deriv x (ε / 2)) := by
        rw [multiCMKineticSq]
        exact Finset.sum_nonneg fun k _ =>
          mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)
      linarith [hC.le, hKout (ε / 2) hε2, hout0, hKcm (ε / 2) hε2, hcm0]
    have h6 : 6 * C ≤ 6 * C * t ^ (-((2:ℝ)/3)) := by
      have h := mul_le_mul_of_nonneg_left hpow (by linarith : (0:ℝ) ≤ 6 * C)
      rwa [mul_one] at h
    have h2U : multiPotential m ks (x t)
        ≤ ((η / 4) / Real.sqrt k0 + 1) / 2 * t ^ (-((2:ℝ)/3))
          + 3 * C * t ^ (-((2:ℝ)/3)) := by
      have e : ((η / 4) / Real.sqrt k0 + 1) * t ^ (-((2:ℝ)/3))
            + 6 * C * t ^ (-((2:ℝ)/3))
          = 2 * (((η / 4) / Real.sqrt k0 + 1) / 2 * t ^ (-((2:ℝ)/3))
              + 3 * C * t ^ (-((2:ℝ)/3))) := by ring
      linarith [h1, h2, h6, e]
    have hC0le : C + Cout / 2 + Ccm2 / 2
        ≤ (C + Cout / 2 + Ccm2 / 2) * t ^ (-((2:ℝ)/3)) :=
      le_mul_of_one_le_right hC0 hpow
    have e2 : (((η / 4) / Real.sqrt k0 + 1) / 2 + 3 * C + (C + Cout / 2 + Ccm2 / 2))
          * t ^ (-((2:ℝ)/3))
        = ((η / 4) / Real.sqrt k0 + 1) / 2 * t ^ (-((2:ℝ)/3)) + 3 * C * t ^ (-((2:ℝ)/3))
          + (C + Cout / 2 + Ccm2 / 2) * t ^ (-((2:ℝ)/3)) := by ring
    linarith [h3, h2U, hC0le, e2]
  exact ⟨_, hcKpos, hKfinal⟩

end Submission.NBody
