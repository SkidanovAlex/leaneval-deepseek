import Submission.NBody.MarchalClusterBound
import Submission.NBody.MarchalForce
import Submission.NBody.Force

/-!
# Velocities outside a single colliding cluster are bounded

If a cluster `k` is `ν`-separated from all the other bodies along a motion (so that every body
outside `k` is at distance `≥ ν` from every other body), then the acceleration of every body outside
`k` is bounded by `(∑ m)·ν^{-2}`, whence its velocity is bounded on any bounded time interval.

This is the "single colliding group" step of the geometric reduction of the Marchal chapter
(`Submission/ROADMAP.md`, §4): it supplies the hypothesis `hv` of
`clusterInertia_asymptotic_of_isolated`.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The acceleration of a body outside the cluster is bounded** by `(∑ m)·ν^{-2}`, because all its
distances to the other bodies are `≥ ν`. -/
lemma norm_weightedGrad_outside_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {ν : ℝ} (hν : 0 < ν) {x : EN E N} (hsep : ClusterSeparated k x ν)
    (hnc : WithoutCollisions x) {j : Fin N} (hj : j ∉ k) :
    ‖(∇_[m] (U m) x) j‖ ≤ (∑ i, m i) * (ν⁻¹) ^ 2 := by
  rw [weightedGrad_U_coord m (fun i => (hm i).ne') x hnc j]
  have hterm : ∀ i ∈ Finset.univ.erase j, ‖(m i * (‖x i - x j‖ ^ 3)⁻¹) • (x i - x j)‖
      ≤ m i * (ν⁻¹) ^ 2 := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hdist : ν ≤ ‖x i - x j‖ := by
      have h := hsep i j hij (fun hcon => hj hcon.2)
      rwa [r_eq_norm_sub] at h
    have hpos : 0 < ‖x i - x j‖ := lt_of_lt_of_le hν hdist
    have h3 : (‖x i - x j‖ ^ 3)⁻¹ * ‖x i - x j‖ = ((‖x i - x j‖)⁻¹) ^ 2 := by
      rw [inv_mul_eq_div, pow_succ]
      field_simp
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hm i).le (by positivity)),
      mul_assoc, h3]
    refine mul_le_mul_of_nonneg_left ?_ (hm i).le
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) ((inv_le_inv₀ hpos hν).mpr hdist) 2
  calc ‖∑ i ∈ Finset.univ.erase j, (m i * (‖x i - x j‖ ^ 3)⁻¹) • (x i - x j)‖
      ≤ ∑ i ∈ Finset.univ.erase j, ‖(m i * (‖x i - x j‖ ^ 3)⁻¹) • (x i - x j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.erase j, m i * (ν⁻¹) ^ 2 := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.univ.erase j, m i) * (ν⁻¹) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (∑ i, m i) * (ν⁻¹) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun i _ _ => (hm i).le)

/-- **Velocities outside the cluster are bounded** on `(0,ε)`, given that the cluster is
`ν`-separated from the rest and the curve solves Newton's equations there. -/
theorem exists_bound_deriv_outside {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {ε ν : ℝ} (hε : 0 < ε) (hν : 0 < ν) {x : ℝ → EN E N}
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparated k (x t) ν)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k, ‖deriv x t j‖ ≤ Cv := by
  have hmnn : 0 ≤ (∑ i, m i) := Finset.sum_nonneg fun i _ => (hm i).le
  have hC : 0 ≤ (∑ i, m i) * (ν⁻¹) ^ 2 := by positivity
  have hEnn : 0 ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), ‖deriv x (ε / 2) j‖) :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨(∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), ‖deriv x (ε / 2) j‖)
    + ((∑ i, m i) * (ν⁻¹) ^ 2) * ε, by positivity, ?_⟩
  intro t ht j hj
  have hmid : ε / 2 ∈ Ioo (0:ℝ) ε := ⟨by linarith, by linarith⟩
  have hmem' : ∀ u ∈ Set.Icc (min (t:ℝ) (ε / 2)) (max (t:ℝ) (ε / 2)), u ∈ Ioo (0:ℝ) ε := by
    intro u hu
    rw [Set.mem_Icc] at hu
    refine ⟨lt_of_lt_of_le (lt_min ht.1 hmid.1) hu.1, lt_of_le_of_lt hu.2 (max_lt ht.2 hmid.2)⟩
  have hmvt : ‖deriv x t j - deriv x (ε / 2) j‖
      ≤ ((∑ i, m i) * (ν⁻¹) ^ 2) * ‖t - ε / 2‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u : ℝ => deriv x u j)
      (s := Set.Icc (min (t:ℝ) (ε / 2)) (max (t:ℝ) (ε / 2))) (x := ε / 2) (y := t)
      (fun u hu => (hasDerivAt_apply (hd2 u (hmem' u hu)) j).differentiableAt)
      (fun u hu => ?_) (convex_Icc _ _)
      (by rw [Set.mem_Icc]; exact ⟨min_le_right _ _, le_max_right _ _⟩)
      (by rw [Set.mem_Icc]; exact ⟨min_le_left _ _, le_max_left _ _⟩)
    rw [(hasDerivAt_apply (hd2 u (hmem' u hu)) j).deriv, hode u (hmem' u hu)]
    exact norm_weightedGrad_outside_le hm hν (hsep u (hmem' u hu)) (hnc u (hmem' u hu)) hj
  have h2 : ‖t - ε / 2‖ ≤ ε := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  calc ‖deriv x t j‖ ≤ ‖deriv x (ε / 2) j‖ + ‖deriv x t j - deriv x (ε / 2) j‖ := by
        have hh := norm_add_le (deriv x t j - deriv x (ε / 2) j) (deriv x (ε / 2) j)
        rw [sub_add_cancel] at hh
        linarith [hh]
    _ ≤ ‖deriv x (ε / 2) j‖ + ((∑ i, m i) * (ν⁻¹) ^ 2) * ε := by
        refine add_le_add le_rfl ?_
        exact hmvt.trans (mul_le_mul_of_nonneg_left h2 hC)
    _ ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), ‖deriv x (ε / 2) j‖)
          + ((∑ i, m i) * (ν⁻¹) ^ 2) * ε := by
        have hsingle : ‖deriv x (ε / 2) j‖ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k),
            ‖deriv x (ε / 2) j‖ :=
          Finset.single_le_sum (fun i _ => norm_nonneg _)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
        linarith

end Submission.NBody
