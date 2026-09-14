import Submission.NBody.ClusterGradSplit
import Submission.NBody.MarchalClusterShapeSecondDeriv

/-!
# The cluster potential of the normalised configuration

The cluster potential `U_k(s)` of the *normalised* configuration `s = I_k^{-1/2}(x - x_{cm,k})`
is `√(I_k(x)) · U_k(x)`.  Together with the asymptotic `I_k/t^{4/3} → κ` and
`U_k · t^{2/3} → (2/9)κ` this gives the finite positive limit

    `U_k(s(t)) → √κ · (2/9)κ = (2/9) κ^{3/2}`,

which is what makes the limiting configuration `s̄` collision-free: a collision of any pair inside
`k` would force `U_k(s(t)) → +∞`.

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

/-- The cluster potential only depends on the pairwise differences inside the cluster, hence is
invariant under passing to the centre-of-mass-relative configuration. -/
lemma clusterPotential_cmRel (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    clusterPotential m k (cmRel m k x) = clusterPotential m k x := by
  rw [clusterPotential, clusterPotential]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hmem := (Finset.mem_filter.mp hp).2
  congr 2
  rw [r_eq_norm_sub, r_eq_norm_sub, cmRel_apply_of_mem hmem.1, cmRel_apply_of_mem hmem.2]
  rw [show (x p.1 - clusterCM m k x) - (x p.2 - clusterCM m k x) = x p.1 - x p.2 by abel]

/-- **The cluster potential of the normalised configuration.** -/
lemma clusterPotential_clusterShape (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    clusterPotential m k (clusterShape m k x)
      = Real.sqrt (clusterInertia m k x) * clusterPotential m k x := by
  rw [clusterShape, clusterPotential_smul, clusterPotential_cmRel,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_inv]

/-- **The finite limit of the cluster potential of the normalised configuration.** -/
theorem tendsto_clusterPotential_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUn : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ))) :
    Tendsto (fun t : ℝ => clusterPotential m k (clusterShape m k (x t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ * ((2:ℝ)/9 * κ))) := by
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (clusterInertia m k (x t)) / t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    tendsto_sqrt_div_rpow_two_thirds hε hκ.le
      (fun t ht => clusterInertia_nonneg (fun j => (hm j).le) k (x t)) hIn
  have hprod := hsqrt.mul hUn
  refine Filter.Tendsto.congr' ?_ hprod
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  rw [clusterPotential_clusterShape]
  have ht0 : t ^ ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht.1 _)
  field_simp

/-- Every internal pair contributes at most the cluster potential (all terms are non-negative). -/
lemma mul_mul_inv_r_le_clusterPotential {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {k : Finset (Fin N)} {s : EN E N} {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    m i * m j * (r s i j)⁻¹ ≤ clusterPotential m k s := by
  have hterm_nonneg : ∀ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      0 ≤ m p.1 * m p.2 * (r s p.1 p.2)⁻¹ := by
    intro p _
    exact mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (inv_nonneg.mpr dist_nonneg)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hp : (i, j) ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k) := by
      simp only [Finset.mem_filter, pairFinset, Finset.mem_univ, true_and]
      exact ⟨hlt, hi, hj⟩
    exact Finset.single_le_sum hterm_nonneg hp
  · have hp : (j, i) ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k) := by
      simp only [Finset.mem_filter, pairFinset, Finset.mem_univ, true_and]
      exact ⟨hlt, hj, hi⟩
    have h := Finset.single_le_sum (f := fun p : Fin N × Fin N =>
      m p.1 * m p.2 * (r s p.1 p.2)⁻¹) hterm_nonneg hp
    have hr : r s j i = r s i j := by rw [r, r, dist_comm]
    rw [hr, mul_comm (m j) (m i)] at h
    exact h

/-- **The limiting configuration is collision-free inside the cluster.**  A collision of two bodies
of `k` would force the cluster potential of the normalised configuration to blow up, but that
potential converges to the finite positive limit `√κ · (2/9)κ`. -/
theorem withoutCollisions_of_tendsto_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUn : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar)) :
    ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j := by
  intro i hi j hj hij
  have hlim := tendsto_clusterPotential_clusterShape (m := m) (k := k) (x := x)
    hm hk2 hε hκ hnc hIn hUn
  set L : ℝ := Real.sqrt κ * ((2:ℝ)/9 * κ) with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (Real.sqrt_pos.mpr hκ) (by positivity)
  have hmij : 0 < m i * m j := mul_pos (hm i) (hm j)
  have hL1 : (0:ℝ) < L + 1 := by linarith
  have hcpos : 0 < m i * m j / (L + 1) := div_pos hmij hL1
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      m i * m j / (L + 1) ≤ ‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖ := by
    filter_upwards [hlim.eventually (isOpen_Iio.mem_nhds (show L < L + 1 by linarith)),
      Ioo_mem_nhdsGT hε] with t htU ht
    have hI : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
    have hsq : Real.sqrt (clusterInertia m k (x t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hI)
    have hne : (clusterShape m k (x t)) i ≠ (clusterShape m k (x t)) j := by
      intro hcon
      have h2 := congrArg (fun w : E => Real.sqrt (clusterInertia m k (x t)) • w) hcon
      simp only [clusterShape_apply, smul_smul, mul_inv_cancel₀ hsq, one_smul] at h2
      rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem hj] at h2
      have h3 : x t i = x t j := by
        have h4 := congrArg (fun w : E => w + clusterCM m k (x t)) h2
        simpa using h4
      exact hnc t ht i j hij (by rw [r_eq_norm_sub, h3, sub_self, norm_zero])
    have hd : 0 < ‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h1 := mul_mul_inv_r_le_clusterPotential (fun a => (hm a).le) hi hj hij
      (s := clusterShape m k (x t))
    rw [r_eq_norm_sub] at h1
    rw [div_le_iff₀ hL1]
    have h3 : m i * m j * (‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖)⁻¹
          * ‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖ < (L + 1)
        * ‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖ :=
      mul_lt_mul_of_pos_right (lt_of_le_of_lt h1 htU) hd
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hd), mul_one] at h3
    linarith
  have hci : Continuous (fun w : EN E N => w i) := PiLp.continuous_apply 2 (fun _ : Fin N => E) i
  have hcj : Continuous (fun w : EN E N => w j) := PiLp.continuous_apply 2 (fun _ : Fin N => E) j
  have hsi : Tendsto (fun t : ℝ => (clusterShape m k (x t)) i) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (sbar i)) := hci.continuousAt.tendsto.comp hs
  have hsj : Tendsto (fun t : ℝ => (clusterShape m k (x t)) j) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (sbar j)) := hcj.continuousAt.tendsto.comp hs
  have hcont : Tendsto
      (fun t : ℝ => ‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (‖sbar i - sbar j‖)) :=
    (hsi.sub hsj).norm
  have hge : m i * m j / (L + 1) ≤ ‖sbar i - sbar j‖ := by
    rw [← not_lt]
    intro hcon
    have hev2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
        ‖(clusterShape m k (x t)) i - (clusterShape m k (x t)) j‖ < m i * m j / (L + 1) :=
      hcont.eventually (isOpen_Iio.mem_nhds hcon)
    obtain ⟨t, ht1, ht2⟩ := (hev2.and hev).exists
    exact absurd ht2 (not_le.mpr ht1)
  intro hcon
  rw [hcon, sub_self, norm_zero] at hge
  linarith

end Submission.NBody
