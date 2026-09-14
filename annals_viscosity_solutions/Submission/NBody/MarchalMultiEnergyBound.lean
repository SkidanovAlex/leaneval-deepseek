import Submission.NBody.MarchalMultiJolt
import Submission.NBody.ClusterCentralConfig
import Submission.Commons.Analysis.Asymptotic.sqrt_le_sqrt_mul_rpow_neg_third
import Submission.Commons.Analysis.Calculus.rpow_neg_third_deriv_le_implies_lower_bound

/-!
# The time-derivative of the relative energy of a colliding cluster

At a collision time `t₀` with several collision classes `C₁, …, C_r`, the sum-level Sundman
analysis (`MarchalMultiJolt`) gives the bound `K ≤ c t^{-2/3}` on the *total* kinetic energy.
Ferrario–Terracini's `lemma:bounded_energy` then bounds each individual relative energy `E^{rel}_{C_l}`
by integrating its derivative, which is bounded by `c K^{1/2} ≤ c' t^{-1/3}` — an integrable
function.

This module supplies the two ingredients:

* `deriv_clusterRelEnergy` — the exact identity
  `Ė^{rel}_k = crossWork m k x (cmRel m k ẋ)`;
* the resulting bound `|Ė^{rel}_k| ≤ (1/ν²)(∑ m) √(m_k) √(R_k)` and hence `≤ c t^{-1/3}`.

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

/-- The centre-of-mass-relative kinetic energy of a cluster is its moment of inertia applied to the
velocity. -/
lemma clusterRelKinetic_eq_clusterInertia (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) :
    clusterRelKinetic m k v = clusterInertia m k v := by
  rw [clusterRelKinetic, clusterKineticSq, clusterInertia]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cmRel_apply_of_mem hi]

/-- The relative kinetic energy of a cluster is at most the total kinetic energy. -/
lemma clusterRelKinetic_le_kinetic {m : Fin N → ℝ} (k : Finset (Fin N)) (v : EN E N)
    (hm : ∀ i, 0 < m i) (hk : k.Nonempty) :
    clusterRelKinetic m k v ≤ 2 * kinetic m v := by
  rw [clusterRelKinetic]
  refine le_trans (clusterKineticSq_cmRel_le k v hm hk) ?_
  rw [clusterKineticSq, kinetic]
  have h2 : 2 * ((1 / 2) * ∑ i : Fin N, m i * ‖v i‖ ^ 2)
      = ∑ i : Fin N, m i * ‖v i‖ ^ 2 := by ring
  rw [h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => m i * ‖v i‖ ^ 2)
    (Finset.subset_univ k) (fun i _ _ => mul_nonneg (le_of_lt (hm i)) (sq_nonneg _))

/-- **The work of the Newtonian force in a direction supported on a cluster.**  For `d` arbitrary,
the sum of the works of the force on the bodies of `k` against the *centre-of-mass-relative*
displacement equals the derivative of the internal potential in the direction `d` plus the
interaction term. -/
lemma sum_inner_gradient_cmRel (m : Fin N → ℝ) (k : Finset (Fin N)) (x d : EN E N)
    (hx : WithoutCollisions x) :
    ∑ i ∈ k, inner ℝ (d i - clusterCM m k d) ((gradient (U m) x) i)
      = (fderiv ℝ (clusterPotential m k) x) (cmRel m k d)
        + crossWork m k x (cmRel m k d) := by
  have hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j := by
    intro i _ j _ hij
    have h := hx i j hij
    rw [r_eq_norm_sub] at h
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp h)
  have hsum : (∑ i ∈ k, inner ℝ ((gradient (U m) x) i) (d i - clusterCM m k d))
      = (fderiv ℝ (U m) x) (cmRel m k d) := by
    rw [cmRel_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_singleBody (gradient (U m) x) i (d i - clusterCM m k d),
      inner_gradient_eq_fderiv]
  rw [Finset.sum_congr rfl
    (fun i _ => real_inner_comm ((gradient (U m) x) i) (d i - clusterCM m k d))]
  rw [hsum, fderiv_U_pair_apply m x (cmRel m k d) hx]
  rw [← Finset.sum_filter_add_sum_filter_not (pairFinset N)
    (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k)
    (fun p : Fin N × Fin N => m p.1 * m p.2 *
      (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
        ((cmRel m k d) p.1 - (cmRel m k d) p.2)))]
  have hQ : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
        ((cmRel m k d) p.1 - (cmRel m k d) p.2)))
      = (fderiv ℝ (clusterPotential m k) x) (cmRel m k d) :=
    (fderiv_clusterPotential_apply m k x (cmRel m k d) hkk).symm
  rw [hQ, crossWork]

/-- **The derivative of the relative energy of a cluster.**  Along a solution of Newton's
equations, the relative energy of a cluster changes at the rate of the *interaction* work: the
internal virial cancels exactly (Ferrario–Terracini, `eq:Ei`). -/
theorem hasDerivAt_clusterRelEnergy {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {t : ℝ}
    (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hnc : WithoutCollisions (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ᶠ s in 𝓝 t, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hode : deriv (deriv x) t = ∇_[m] (U m) (x t)) :
    HasDerivAt (fun s : ℝ => clusterRelEnergy m k (x s) (deriv x s))
      (crossWork m k (x t) (cmRel m k (deriv x t))) t := by

  show HasDerivAt
      (fun s : ℝ => clusterRelKinetic m k (deriv x s) / 2 - clusterPotential m k (x s))
      (crossWork m k (x t) (cmRel m k (deriv x t))) t
  have hM : clusterMass m k ≠ 0 := ne_of_gt (clusterMass_pos hm hk)
  have hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x t i ≠ x t j := by
    intro i _ j _ hij
    have h := hnc i j hij
    rw [r_eq_norm_sub] at h
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp h)
  -- (A) the derivative of the relative kinetic energy
  have hA0 := hasDerivAt_clusterInertia_curve (m := m) (k := k) (x := deriv x) (t := t) hd2
  rw [deriv_clusterInertia_curve (m := m) (k := k) (x := deriv x) (t := t) hd2] at hA0
  have hA : HasDerivAt (fun s : ℝ => clusterRelKinetic m k (deriv x s))
      (2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))) t :=
    hA0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => clusterRelKinetic_eq_clusterInertia m k (deriv x s))
  -- (B) the derivative of the cluster potential
  have hB : HasDerivAt (fun s : ℝ => clusterPotential m k (x s))
      ((fderiv ℝ (clusterPotential m k) (x t)) (deriv x t)) t := by
    have hF := hasFDerivAt_clusterPotential m k (x t) hkk
    have hd := hF.comp_hasDerivAt t hx.self_of_nhds
    rw [← hF.fderiv] at hd
    exact hd
  have hC : HasDerivAt
      (fun s : ℝ => clusterRelKinetic m k (deriv x s) / 2 - clusterPotential m k (x s))
      (2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)) / 2
        - (fderiv ℝ (clusterPotential m k) (x t)) (deriv x t)) t :=
    (hA.div_const 2).sub hB
  -- the two algebraic identifications
  have hK : 2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)) / 2
      = ∑ i ∈ k, inner ℝ (deriv x t i - clusterCM m k (deriv x t))
          ((gradient (U m) (x t)) i) := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
    rw [massInner_cmRel_cmRel_eq m k (deriv x t) (deriv (deriv x) t) hM]
    rw [hode, massInner_cmRel_eq' m k (deriv x t) (weightedGrad m (U m) (x t))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show m i * inner ℝ (deriv x t i - clusterCM m k (deriv x t))
          ((weightedGrad m (U m) (x t)) i)
        = inner ℝ (deriv x t i - clusterCM m k (deriv x t))
          ((gradient (U m) (x t)) i) by
      rw [weightedGrad, PiLp.toLp_apply, real_inner_smul_right, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (hm i)), one_mul]]
  have hfeq : (fderiv ℝ (clusterPotential m k) (x t)) (deriv x t)
      = (fderiv ℝ (clusterPotential m k) (x t)) (cmRel m k (deriv x t)) := by
    rw [fderiv_clusterPotential_apply m k (x t) (deriv x t) hkk,
      fderiv_clusterPotential_apply m k (x t) (cmRel m k (deriv x t)) hkk]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hp).2
    rw [cmRel_apply_of_mem h1, cmRel_apply_of_mem h2]
    rw [show (deriv x t p.1 - clusterCM m k (deriv x t))
        - (deriv x t p.2 - clusterCM m k (deriv x t)) = deriv x t p.1 - deriv x t p.2 by abel]
  have hW := sum_inner_gradient_cmRel m k (x t) (deriv x t) hnc
  have hval : 2 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)) / 2
      - (fderiv ℝ (clusterPotential m k) (x t)) (deriv x t)
      = crossWork m k (x t) (cmRel m k (deriv x t)) := by
    rw [hK, hW, hfeq]
    ring
  have hres := hval ▸ hC
  simpa only [clusterRelEnergy] using hres

/-- The `deriv` form of the derivative of the relative energy of a cluster. -/
theorem deriv_clusterRelEnergy {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {t : ℝ}
    (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hnc : WithoutCollisions (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ᶠ s in 𝓝 t, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hode : deriv (deriv x) t = ∇_[m] (U m) (x t)) :
    deriv (fun s : ℝ => clusterRelEnergy m k (x s) (deriv x s)) t
      = crossWork m k (x t) (cmRel m k (deriv x t)) :=
  (hasDerivAt_clusterRelEnergy hm hk hnc hx hd2 hode).deriv

/-- **The interaction work of a cluster, sharply.**  Under the one-sided separation of `k` from
its complement the interaction work is bounded by `ν⁻²` times the mass sum times
`√(m_k) · √(R_k)`, where `R_k` is the centre-of-mass-relative kinetic energy of the cluster. -/
theorem abs_crossWork_cmRel_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x v : EN E N} {ν : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hsep : ClusterSeparatedWeak k x ν) :
    |crossWork m k x (cmRel m k v)|
      ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
          * Real.sqrt (clusterRelKinetic m k v) := by
  classical
  have hν2 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
  have hfac : ∀ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖
      ≤ (ν⁻¹) ^ 2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hr2 : ∀ r : ℝ, ν ≤ r → 0 < r → (r ^ 2)⁻¹ ≤ (ν⁻¹) ^ 2 := by
      intro r hr hrpos
      rw [show (ν⁻¹) ^ 2 = (ν ^ 2)⁻¹ from inv_pow ν 2]
      exact (inv_le_inv₀ (pow_pos hrpos 2) (pow_pos hν 2)).mpr (pow_le_pow_left₀ hν.le hr 2)
    by_cases h1 : p.1 ∈ k
    · by_cases h2 : p.2 ∈ k
      · exact absurd ⟨h1, h2⟩ hp'
      · have hdist : ν ≤ ‖x p.1 - x p.2‖ := by
          rw [← r_eq_norm_sub]; exact hsep p.1 h1 p.2 h2
        have hq2 : (cmRel m k v) p.2 = 0 := cmRel_apply_of_notMem h2
        calc (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖
            = (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.1‖ := by rw [hq2, sub_zero]
          _ ≤ (ν⁻¹) ^ 2 * ‖(cmRel m k v) p.1‖ :=
              mul_le_mul_of_nonneg_right (hr2 _ hdist (lt_of_lt_of_le hν hdist)) (norm_nonneg _)
          _ = (ν⁻¹) ^ 2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖) := by
              rw [hq2, norm_zero, add_zero]
    · by_cases h2 : p.2 ∈ k
      · have hdist : ν ≤ ‖x p.1 - x p.2‖ := by
          rw [show ‖x p.1 - x p.2‖ = ‖x p.2 - x p.1‖ from norm_sub_rev _ _]
          rw [← r_eq_norm_sub]; exact hsep p.2 h2 p.1 h1
        have hq1 : (cmRel m k v) p.1 = 0 := cmRel_apply_of_notMem h1
        calc (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖
            = (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.2‖ := by rw [hq1, zero_sub, norm_neg]
          _ ≤ (ν⁻¹) ^ 2 * ‖(cmRel m k v) p.2‖ :=
              mul_le_mul_of_nonneg_right (hr2 _ hdist (lt_of_lt_of_le hν hdist)) (norm_nonneg _)
          _ = (ν⁻¹) ^ 2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖) := by
              rw [hq1, norm_zero, zero_add]
      · have hq1 : (cmRel m k v) p.1 = 0 := cmRel_apply_of_notMem h1
        have hq2 : (cmRel m k v) p.2 = 0 := cmRel_apply_of_notMem h2
        rw [hq1, hq2]
        simp
  have hterm : ∀ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      |m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
        ((cmRel m k v) p.1 - (cmRel m k v) p.2))|
      ≤ m p.1 * m p.2 * ((‖x p.1 - x p.2‖ ^ 2)⁻¹
          * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖) := by
    intro p hp
    have hmm : 0 ≤ m p.1 * m p.2 := mul_nonneg (hm p.1).le (hm p.2).le
    have hinv3 : 0 ≤ (‖x p.1 - x p.2‖ ^ 3)⁻¹ := by positivity
    have habs : |m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
          ((cmRel m k v) p.1 - (cmRel m k v) p.2))|
        = m p.1 * m p.2 * ((‖x p.1 - x p.2‖ ^ 3)⁻¹
            * |inner ℝ (x p.1 - x p.2) ((cmRel m k v) p.1 - (cmRel m k v) p.2)|) := by
      rw [abs_mul, abs_of_nonneg hmm, abs_mul, abs_neg, abs_of_nonneg hinv3]
    rw [habs]
    have hinner := abs_real_inner_le_norm (x p.1 - x p.2)
      ((cmRel m k v) p.1 - (cmRel m k v) p.2)
    have hle1 : (‖x p.1 - x p.2‖ ^ 3)⁻¹
          * |inner ℝ (x p.1 - x p.2) ((cmRel m k v) p.1 - (cmRel m k v) p.2)|
        ≤ (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖ := by
      rcases eq_or_ne ‖x p.1 - x p.2‖ 0 with hz | hz
      · rw [hz]; simp
      · have h3 : (‖x p.1 - x p.2‖ ^ 3)⁻¹ * ‖x p.1 - x p.2‖
            = (‖x p.1 - x p.2‖ ^ 2)⁻¹ := by
          field_simp
        calc (‖x p.1 - x p.2‖ ^ 3)⁻¹
              * |inner ℝ (x p.1 - x p.2) ((cmRel m k v) p.1 - (cmRel m k v) p.2)|
            ≤ (‖x p.1 - x p.2‖ ^ 3)⁻¹
              * (‖x p.1 - x p.2‖ * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖) :=
              mul_le_mul_of_nonneg_left hinner hinv3
          _ = ((‖x p.1 - x p.2‖ ^ 3)⁻¹ * ‖x p.1 - x p.2‖)
              * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖ := by ring
          _ = (‖x p.1 - x p.2‖ ^ 2)⁻¹ * ‖(cmRel m k v) p.1 - (cmRel m k v) p.2‖ := by
              rw [h3]
    exact mul_le_mul_of_nonneg_left hle1 hmm
  -- the symmetric-pair sum bound
  have hpair : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖))
      ≤ 2 * ((∑ j : Fin N, m j) * (∑ i ∈ k, m i * ‖(cmRel m k v) i‖)) := by
    have h1 : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖))
        ≤ ∑ p : Fin N × Fin N,
            m p.1 * m p.2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ =>
        mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le)
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    refine le_trans h1 ?_
    have hkey : (∑ p : Fin N × Fin N,
          m p.1 * m p.2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖))
        = 2 * ((∑ j : Fin N, m j) * (∑ i : Fin N, m i * ‖(cmRel m k v) i‖)) := by
      rw [Fintype.sum_prod_type]
      have hpt : ∀ i j : Fin N, m i * m j * (‖(cmRel m k v) i‖ + ‖(cmRel m k v) j‖)
          = (m i * ‖(cmRel m k v) i‖) * m j + m i * (m j * ‖(cmRel m k v) j‖) :=
        fun i j => by ring
      simp only [hpt]
      have hinner : ∀ i : Fin N,
          (∑ j : Fin N, ((m i * ‖(cmRel m k v) i‖) * m j
            + m i * (m j * ‖(cmRel m k v) j‖)))
          = (∑ j : Fin N, (m i * ‖(cmRel m k v) i‖) * m j)
            + (∑ j : Fin N, m i * (m j * ‖(cmRel m k v) j‖)) :=
        fun _ => Finset.sum_add_distrib
      rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_add_distrib]
      have e1 : (∑ i : Fin N, ∑ j : Fin N, (m i * ‖(cmRel m k v) i‖) * m j)
          = (∑ i : Fin N, m i * ‖(cmRel m k v) i‖) * (∑ j : Fin N, m j) :=
        (Finset.sum_mul_sum _ _ _ _).symm
      have e2 : (∑ i : Fin N, ∑ j : Fin N, m i * (m j * ‖(cmRel m k v) j‖))
          = (∑ i : Fin N, m i) * (∑ j : Fin N, m j * ‖(cmRel m k v) j‖) :=
        (Finset.sum_mul_sum _ _ _ _).symm
      rw [e1, e2]
      ring
    have hC : (∑ i : Fin N, m i * ‖(cmRel m k v) i‖)
        = ∑ i ∈ k, m i * ‖(cmRel m k v) i‖ :=
      (Finset.sum_subset (Finset.subset_univ k)
        (fun i _ hi => by rw [cmRel_apply_of_notMem hi, norm_zero, mul_zero])).symm
    rw [hkey, hC]
  have hcs := sum_mass_norm_le_sqrt (m := m) (k := k) (v := cmRel m k v) (fun i => (hm i).le)
  have hsqrt : Real.sqrt (clusterMass m k * clusterKineticSq m k (cmRel m k v))
      = Real.sqrt (clusterMass m k) * Real.sqrt (clusterRelKinetic m k v) := by
    rw [Real.sqrt_mul (clusterMass_nonneg (fun i => (hm i).le) k)]
    rfl
  have hpair' : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖))
      ≤ 2 * ((∑ j : Fin N, m j) * (Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterRelKinetic m k v))) := by
    refine le_trans hpair ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun j _ => (hm j).le)
    calc (∑ i ∈ k, m i * ‖(cmRel m k v) i‖)
        ≤ Real.sqrt (clusterMass m k * clusterKineticSq m k (cmRel m k v)) := hcs
      _ = Real.sqrt (clusterMass m k) * Real.sqrt (clusterRelKinetic m k v) := hsqrt
  rw [crossWork]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  refine le_trans (Finset.sum_le_sum fun p hp =>
      mul_le_mul_of_nonneg_left (hfac p hp) (mul_nonneg (hm p.1).le (hm p.2).le)) ?_
  have hsplit : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      m p.1 * m p.2 * ((ν⁻¹) ^ 2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖)))
      = (ν⁻¹) ^ 2 * (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2 * (‖(cmRel m k v) p.1‖ + ‖(cmRel m k v) p.2‖)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit]
  have hfin : (ν⁻¹) ^ 2 * (2 * ((∑ j : Fin N, m j)
        * (Real.sqrt (clusterMass m k) * Real.sqrt (clusterRelKinetic m k v))))
      = 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
        * Real.sqrt (clusterRelKinetic m k v) := by ring
  exact le_trans (mul_le_mul_of_nonneg_left hpair' hν2) hfin.le


/-- The increasing counterpart of
`Commons.Analysis.Calculus.rpow_neg_third_deriv_le_implies_lower_bound`: a lower bound
`-c x^{-1/3} ≤ g'` on the derivative gives an upper bound on the growth of `g`. -/
lemma le_add_rpow_third_of_neg_rpow_le_deriv {g : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcont : ContinuousOn g (Icc a b))
    (hdiff : DifferentiableOn ℝ g (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, -(c * x ^ (-(1:ℝ)/3)) ≤ deriv g x) :
    g a ≤ g b + (3 * c / 2) * b ^ ((2:ℝ)/3) := by
  have h := Commons.Analysis.Calculus.rpow_neg_third_deriv_le_implies_lower_bound
    (g := fun y : ℝ => -g y) ha hab hc hcont.neg hdiff.neg (fun x hx => ?_)
  · linarith
  · have hx' : deriv (fun y : ℝ => -g y) x = -deriv g x := by
      have hd : DifferentiableAt ℝ g x := (hdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      simpa using hd.hasDerivAt.neg.deriv
    rw [hx']
    have := hderiv x hx
    linarith

/-- **The relative energy of a colliding cluster is bounded.**  Integrating the identity
`Ė^{rel}_k = W_k` with the estimate `|W_k| ≤ c t^{-1/3}` (which uses the kinetic bound
`K ≤ Ck t^{-2/3}` of the sum-level Sundman analysis) shows that `E^{rel}_k` can only change by an
integrable amount: it is a bounded function of `t` (Ferrario–Terracini, `lemma:bounded_energy`). -/
theorem exists_clusterRelEnergy_bound {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε ν Ck : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hε : 0 < ε) (hν : 0 < ν) (hCk : 0 < Ck)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, deriv (deriv x) t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hkin : ∀ t ∈ Ioo (0:ℝ) ε, kinetic m (deriv x t) ≤ Ck * t ^ (-((2:ℝ)/3))) :
    ∃ C : ℝ, ∀ t ∈ Ioo (0:ℝ) (ε / 2),
      |clusterRelEnergy m k (x t) (deriv x t)| ≤ C := by
  set cst : ℝ := 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
      * Real.sqrt (2 * Ck) with hcst
  have hcst0 : 0 ≤ cst := by
    rw [hcst]
    have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt (2 * Ck) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h2) h3) h4
  set e : ℝ := ε / 2 with he
  have hepos : 0 < e := by rw [he]; linarith
  have hele : e < ε := by rw [he]; linarith
  have hemem : e ∈ Ioo (0:ℝ) ε := ⟨hepos, hele⟩
  refine ⟨|clusterRelEnergy m k (x e) (deriv x e)| + (3 * cst / 2) * e ^ ((2:ℝ)/3),
    fun t ht => ?_⟩
  have ht0 : 0 < t := ht.1
  have htle : t ≤ e := le_of_lt ht.2
  have hmem : ∀ s ∈ Icc t e, s ∈ Ioo (0:ℝ) ε := fun s hs =>
    ⟨lt_of_lt_of_le ht0 hs.1, lt_of_le_of_lt hs.2 hele⟩
  have hhas : ∀ s ∈ Ioo (0:ℝ) ε,
      HasDerivAt (fun u : ℝ => clusterRelEnergy m k (x u) (deriv x u))
        (crossWork m k (x s) (cmRel m k (deriv x s))) s := by
    intro s hs
    refine hasDerivAt_clusterRelEnergy (m := m) (k := k) (x := x) (t := s)
      hm hk (hnc s hs) ?_ ?_ (hode s hs)
    · filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      exact hx u hu
    · filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      exact hd2 u hu
  have hcont : ContinuousOn (fun u : ℝ => clusterRelEnergy m k (x u) (deriv x u)) (Icc t e) :=
    fun s hs => (hhas s (hmem s hs)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ
      (fun u : ℝ => clusterRelEnergy m k (x u) (deriv x u)) (Ioo t e) :=
    fun s hs => (hhas s (hmem s (Ioo_subset_Icc_self hs))).differentiableAt.differentiableWithinAt
  have hder : ∀ s ∈ Ioo t e,
      deriv (fun u : ℝ => clusterRelEnergy m k (x u) (deriv x u)) s ≤ cst * s ^ (-(1:ℝ)/3) := by
    intro s hs
    have hsε : s ∈ Ioo (0:ℝ) ε := hmem s (Ioo_subset_Icc_self hs)
    rw [(hhas s hsε).deriv]
    have h1 : |crossWork m k (x s) (cmRel m k (deriv x s))|
        ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterRelKinetic m k (deriv x s)) :=
      abs_crossWork_cmRel_le hm hν (hsep s hsε)
    have h2 : Real.sqrt (clusterRelKinetic m k (deriv x s))
        ≤ Real.sqrt (2 * Ck) * s ^ (-(1:ℝ)/3) := by
      have hkin' : kinetic m (deriv x s) ≤ Ck * s ^ (-(2:ℝ)/3) := by
        have h := hkin s hsε
        rwa [show -((2:ℝ)/3) = -(2:ℝ)/3 by norm_num] at h
      refine Commons.Analysis.Asymptotic.sqrt_le_sqrt_mul_rpow_neg_third
        (A := clusterRelKinetic m k (deriv x s)) (C := 2 * Ck) (t := s) ?_ ?_ hsε.1 ?_
      · exact clusterKineticSq_nonneg (fun i => (hm i).le) k (cmRel m k (deriv x s))
      · linarith
      · calc clusterRelKinetic m k (deriv x s) ≤ 2 * kinetic m (deriv x s) :=
              clusterRelKinetic_le_kinetic k (deriv x s) hm hk
          _ ≤ 2 * Ck * s ^ (-(2:ℝ)/3) := by linarith
    have h3 : 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
        * Real.sqrt (clusterRelKinetic m k (deriv x s))
        ≤ cst * s ^ (-(1:ℝ)/3) := by
      rw [hcst]
      have hnn : 0 ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by
        have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
        have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
        have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h1) h2) h3
      calc 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterRelKinetic m k (deriv x s))
          ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * (Real.sqrt (2 * Ck) * s ^ (-(1:ℝ)/3)) := mul_le_mul_of_nonneg_left h2 hnn
        _ = 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (2 * Ck) * s ^ (-(1:ℝ)/3) := by ring
    calc crossWork m k (x s) (cmRel m k (deriv x s))
        ≤ |crossWork m k (x s) (cmRel m k (deriv x s))| := le_abs_self _
      _ ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
          * Real.sqrt (clusterRelKinetic m k (deriv x s)) := h1
      _ ≤ cst * s ^ (-(1:ℝ)/3) := h3
  have hD := Commons.Analysis.Calculus.rpow_neg_third_deriv_le_implies_lower_bound
    (g := fun u : ℝ => clusterRelEnergy m k (x u) (deriv x u)) (a := t) (b := e) (c := cst)
    ht0 htle hcst0 hcont hdiff hder
  have hder' : ∀ s ∈ Ioo t e,
      -(cst * s ^ (-(1:ℝ)/3))
        ≤ deriv (fun u : ℝ => clusterRelEnergy m k (x u) (deriv x u)) s := by
    intro s hs
    have hsε : s ∈ Ioo (0:ℝ) ε := hmem s (Ioo_subset_Icc_self hs)
    rw [(hhas s hsε).deriv]
    have h1 : |crossWork m k (x s) (cmRel m k (deriv x s))|
        ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterRelKinetic m k (deriv x s)) :=
      abs_crossWork_cmRel_le hm hν (hsep s hsε)
    have hkin' : kinetic m (deriv x s) ≤ Ck * s ^ (-(2:ℝ)/3) := by
      have h := hkin s hsε
      rwa [show -((2:ℝ)/3) = -(2:ℝ)/3 by norm_num] at h
    have h2 : Real.sqrt (clusterRelKinetic m k (deriv x s))
        ≤ Real.sqrt (2 * Ck) * s ^ (-(1:ℝ)/3) := by
      refine Commons.Analysis.Asymptotic.sqrt_le_sqrt_mul_rpow_neg_third
        (A := clusterRelKinetic m k (deriv x s)) (C := 2 * Ck) (t := s) ?_ ?_ hsε.1 ?_
      · exact clusterKineticSq_nonneg (fun i => (hm i).le) k (cmRel m k (deriv x s))
      · linarith
      · calc clusterRelKinetic m k (deriv x s) ≤ 2 * kinetic m (deriv x s) :=
              clusterRelKinetic_le_kinetic k (deriv x s) hm hk
          _ ≤ 2 * Ck * s ^ (-(2:ℝ)/3) := by linarith
    have h3 : 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
        * Real.sqrt (clusterRelKinetic m k (deriv x s))
        ≤ cst * s ^ (-(1:ℝ)/3) := by
      rw [hcst]
      have hnn : 0 ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by
        have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
        have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
        have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h1) h2) h3
      calc 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterRelKinetic m k (deriv x s))
          ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * (Real.sqrt (2 * Ck) * s ^ (-(1:ℝ)/3)) := mul_le_mul_of_nonneg_left h2 hnn
        _ = 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (2 * Ck) * s ^ (-(1:ℝ)/3) := by ring
    calc -(cst * s ^ (-(1:ℝ)/3))
        ≤ -(2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k)
            * Real.sqrt (clusterRelKinetic m k (deriv x s))) := neg_le_neg h3
      _ ≤ -|crossWork m k (x s) (cmRel m k (deriv x s))| := neg_le_neg h1
      _ ≤ crossWork m k (x s) (cmRel m k (deriv x s)) := neg_abs_le _
  have hU := le_add_rpow_third_of_neg_rpow_le_deriv (g := fun u : ℝ =>
      clusterRelEnergy m k (x u) (deriv x u)) (a := t) (b := e) (c := cst)
    ht0 htle hcst0 hcont hdiff hder'
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    linarith [hD, hU, neg_abs_le (clusterRelEnergy m k (x e) (deriv x e)),
      le_abs_self (clusterRelEnergy m k (x e) (deriv x e))]

end Submission.NBody
