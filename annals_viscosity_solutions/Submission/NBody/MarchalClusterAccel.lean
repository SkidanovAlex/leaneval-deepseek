import Submission.NBody.MarchalClusterBound
import Submission.Commons.Analysis.Sum.antisymm_double_sum_zero

/-!
# The centre of mass of the gradient, and the internal forces of a cluster

(RECOVERED — this file was accidentally overwritten and has been reconstructed.)

* `clusterCM_weightedGrad_eq`: the centre of mass of the weighted gradient is the average of the
  individual gradients;
* `sum_gradient_cluster_eq_cross`: at a collision-free configuration the internal forces cancel, so
  the sum over the cluster of the individual gradients is the interaction with the outside bodies;
* `norm_clusterCM_weightedGrad_le`: that interaction is bounded by
  `(∑_{i∈k}∑_{j∉k} mᵢmⱼ)·ν⁻²` when the cluster is `ν`-separated from the rest.
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

/-- The centre of mass of the weighted gradient is the average of the individual gradients. -/
theorem clusterCM_weightedGrad_eq {m : Fin N → ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, m i ≠ 0) (x : EN E N) :
    clusterCM m k (∇_[m] (U m) x) = (clusterMass m k)⁻¹ • ∑ i ∈ k, (gradient (U m) x) i := by
  rw [clusterCM]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (gradient_eq_smul_weightedGrad m hm x i).symm

/-- **Cancellation of the internal forces.**  At a collision-free configuration, the sum over the
cluster of the individual gradients is the interaction with the outside bodies. -/
theorem sum_gradient_cluster_eq_cross {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hnc : WithoutCollisions x) :
    ∑ i ∈ k, (gradient (U m) x) i
      = ∑ i ∈ k, ∑ j with j ∉ k, (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i) := by
  classical
  set F : Fin N → Fin N → E := fun i j => (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i) with hF
  have hcoord : ∀ i : Fin N, (gradient (U m) x) i = ∑ j ∈ Finset.univ.erase i, F i j := by
    intro i
    rw [gradient_U_coord m x hnc i]
  have hreset : ∀ i : Fin N, (Finset.univ.erase i).filter (fun j => j ∈ k) = k.erase i := by
    intro i
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    tauto
  have houter : ∀ i : Fin N, i ∈ k →
      (Finset.univ.erase i).filter (fun j => ¬ j ∈ k)
        = Finset.univ.filter (fun j => ¬ j ∈ k) := by
    intro i hi
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨-, hj⟩; exact hj
    · intro hj; exact ⟨fun (hh : j = i) => hj (hh.symm ▸ hi), hj⟩
  have hanti : ∀ i j : Fin N, F i j = - F j i := by
    intro i j
    simp only [hF]
    rw [norm_sub_rev (x j) (x i), show x j - x i = -(x i - x j) by abel, smul_neg,
      show m i * m j * (‖x i - x j‖ ^ 3)⁻¹ = m j * m i * (‖x i - x j‖ ^ 3)⁻¹ by ring]
  have hzero : ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j => j ∈ k), F i j = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => by rw [hreset i]) ?_
    exact Commons.Analysis.Sum.antisymm_double_sum_zero k F hanti
  calc ∑ i ∈ k, (gradient (U m) x) i
      = ∑ i ∈ k, ∑ j ∈ Finset.univ.erase i, F i j :=
        Finset.sum_congr rfl fun i _ => hcoord i
    _ = ∑ i ∈ k, ((∑ j ∈ (Finset.univ.erase i).filter (fun j => j ∈ k), F i j)
          + ∑ j ∈ (Finset.univ.erase i).filter (fun j => ¬ j ∈ k), F i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ.erase i) (p := fun j => j ∈ k)]
    _ = (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j => j ∈ k), F i j)
          + ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j => ¬ j ∈ k), F i j := by
        rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j => ¬ j ∈ k), F i j := by
        rw [hzero, zero_add]
    _ = ∑ i ∈ k, ∑ j with j ∉ k, F i j := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [houter i hi]

/-- **Bound on the centre of mass of the weighted gradient.**  For a cluster separated from the
rest of the system by `ν`, the centre of mass of the gradient is bounded. -/
theorem norm_clusterCM_weightedGrad_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hsep : ClusterSeparatedWeak k x ν)
    (hnc : WithoutCollisions x) :
    ‖clusterCM m k (∇_[m] (U m) x)‖
      ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) := by
  classical
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  have hcmnn : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
  have hterm : ∀ i ∈ k, ∀ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k),
      ‖(m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖ ≤ m i * m j * ν⁻¹ ^ 2 := by
    intro i hi j hj
    have hj' : j ∉ k := (Finset.mem_filter.mp hj).2
    have hij : i ≠ j := fun h => hj' (h ▸ hi)
    have hne : x j ≠ x i := fun h => (r_ne_zero_iff x i j).mp (hnc i j hij) h.symm
    have hpos : 0 < ‖x j - x i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hdist : ν ≤ ‖x j - x i‖ := by
      have h := hsep i hi j hj'
      rw [r_eq_norm_sub x i j, norm_sub_rev (x i) (x j)] at h
      exact h
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hm i), abs_of_pos (hm j),
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))]
    have hkey : (‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖ ≤ ν⁻¹ ^ 2 := by
      have h2 : ν ^ 2 ≤ ‖x j - x i‖ ^ 2 := by
        nlinarith [hν.le, hdist, norm_nonneg (x j - x i)]
      have h3 : (‖x j - x i‖ ^ 2)⁻¹ ≤ ν⁻¹ ^ 2 := by
        rw [inv_pow]
        exact inv_anti₀ (pow_pos hν 2) h2
      refine le_trans (le_of_eq ?_) h3
      rw [show (3:ℕ) = 2 + 1 by norm_num, pow_add, pow_one, mul_inv]
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
    calc m i * m j * (‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖
        = m i * m j * ((‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖) := by ring
      _ ≤ m i * m j * ν⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg (hm i).le (hm j).le)
  have hsum : ‖∑ i ∈ k, (gradient (U m) x) i‖
      ≤ (∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2 := by
    rw [sum_gradient_cluster_eq_cross (m := m) (k := k) hnc]
    calc ‖∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k),
            (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖
        ≤ ∑ i ∈ k, ‖∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k),
            (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k),
            m i * m j * ν⁻¹ ^ 2 := by
          refine Finset.sum_le_sum fun i hi => le_trans (norm_sum_le _ _)
            (Finset.sum_le_sum fun j hj => hterm i hi j hj)
      _ = (∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
  calc ‖clusterCM m k (∇_[m] (U m) x)‖
      = (clusterMass m k)⁻¹ * ‖∑ i ∈ k, (gradient (U m) x) i‖ := by
        rw [clusterCM_weightedGrad_eq hmne x, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg hcmnn]
    _ ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcmnn)

end Submission.NBody
