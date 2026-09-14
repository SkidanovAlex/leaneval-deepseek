import Submission.NBody.MarchalClusterFull

/-!
# The two-body inertia inequality of a cluster

For two bodies of a cluster the reduced-mass-weighted squared distance is bounded above by the
moment of inertia about the centre of mass:

    `mᵢ mⱼ/(mᵢ+mⱼ) ‖xᵢ - xⱼ‖² ≤ I_k(x)`.

Equivalently, `‖xᵢ - xⱼ‖ ≤ √(I_k(x) (mᵢ+mⱼ)/(mᵢmⱼ))`.  (The converse inequality — a *lower* bound
on a distance in terms of `√I_k` — is FALSE for three or more bodies: a pair may be much closer than
`√I_k` while the moment of inertia is carried by an outside body.)

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

/-- **The two-body inertia inequality.** -/
lemma inertia_pair_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {i j : Fin N}
    (hm : ∀ i, 0 < m i) (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    m i * m j / (m i + m j) * ‖x i - x j‖ ^ 2 ≤ clusterInertia m k x := by
  have hsum : m i * ‖x i - clusterCM m k x‖ ^ 2 + m j * ‖x j - clusterCM m k x‖ ^ 2
      ≤ clusterInertia m k x := by
    rw [clusterInertia]
    have hsub : ({i, j} : Finset (Fin N)) ⊆ k := by
      intro l hl
      rw [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hi
      · exact hj
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun l : Fin N => m l * ‖x l - clusterCM m k x‖ ^ 2) hsub
      (fun l _ _ => mul_nonneg (hm l).le (sq_nonneg _))
    rwa [Finset.sum_pair hij] at h
  have hkey : m i * m j * ‖x i - x j‖ ^ 2
      ≤ (m i + m j) * (m i * ‖x i - clusterCM m k x‖ ^ 2
          + m j * ‖x j - clusterCM m k x‖ ^ 2) := by
    have h1 : ‖x i - x j‖ ^ 2
        = ‖(x i - clusterCM m k x) - (x j - clusterCM m k x)‖ ^ 2 := by
      rw [show x i - x j = (x i - clusterCM m k x) - (x j - clusterCM m k x) by abel]
    have hA : ‖m i • (x i - clusterCM m k x) + m j • (x j - clusterCM m k x)‖ ^ 2
        = m i ^ 2 * ‖x i - clusterCM m k x‖ ^ 2
          + 2 * (m i * m j) * ⟪x i - clusterCM m k x, x j - clusterCM m k x⟫_ℝ
          + m j ^ 2 * ‖x j - clusterCM m k x‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
      ring
    have hB : ‖(x i - clusterCM m k x) - (x j - clusterCM m k x)‖ ^ 2
        = ‖x i - clusterCM m k x‖ ^ 2
          - 2 * ⟪x i - clusterCM m k x, x j - clusterCM m k x⟫_ℝ
          + ‖x j - clusterCM m k x‖ ^ 2 := by
      rw [norm_sub_sq_real]
    rw [h1, hB]
    nlinarith [hA, sq_nonneg ‖m i • (x i - clusterCM m k x)
      + m j • (x j - clusterCM m k x)‖]
  have hpos : 0 < m i + m j := add_pos (hm i) (hm j)
  have h3 : m i * m j * ‖x i - x j‖ ^ 2 ≤ (m i + m j) * clusterInertia m k x :=
    le_trans hkey (mul_le_mul_of_nonneg_left hsum hpos.le)
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  linarith [h3]

/-- **Upper bound of a distance inside the cluster.** -/
lemma dist_pair_upper {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {i j : Fin N}
    (hm : ∀ i, 0 < m i) (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    ‖x i - x j‖ ≤ Real.sqrt (clusterInertia m k x * (m i + m j) / (m i * m j)) := by
  have hmij : 0 < m i * m j := mul_pos (hm i) (hm j)
  have hposij : 0 < m i + m j := add_pos (hm i) (hm j)
  have h : m i * m j * ‖x i - x j‖ ^ 2 ≤ (m i + m j) * clusterInertia m k x := by
    have h0 : m i * m j / (m i + m j) * ‖x i - x j‖ ^ 2 ≤ clusterInertia m k x :=
      inertia_pair_le (E := E) hm hi hj hij
    rw [div_mul_eq_mul_div, div_le_iff₀ hposij] at h0
    linarith [h0]
  have h2 : ‖x i - x j‖ ^ 2 ≤ clusterInertia m k x * (m i + m j) / (m i * m j) := by
    rw [le_div_iff₀ hmij, mul_comm (‖x i - x j‖ ^ 2) (m i * m j),
      mul_comm (clusterInertia m k x) (m i + m j)]
    linarith [h]
  calc ‖x i - x j‖ = Real.sqrt (‖x i - x j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (clusterInertia m k x * (m i + m j) / (m i * m j)) := Real.sqrt_le_sqrt h2

end Submission.NBody
