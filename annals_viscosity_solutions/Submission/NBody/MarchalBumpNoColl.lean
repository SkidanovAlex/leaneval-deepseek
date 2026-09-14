import Submission.NBody.MarchalBumpFinite

/-!
# Collision-freeness of the bumped curve on the window

The bumped curve `γ̃ = bumpCurve m k i₀ δ T λ t₀ γ` is inside the window `γ` plus the perturbation
`λ^{2/3}·stdVarVec`.  If `γ` is collision free there, if the cluster `k` is `ν`-separated from its
complement and if the *rescaled* bumped configuration is collision free inside `k` (which is what
`seq_bumped_noColl` provides), then `γ̃` is collision free.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- `ClusterNoColl` is invariant under subtracting the centre of mass of the cluster. -/
lemma clusterNoColl_of_clusterNoColl_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {v : EN E N}
    (h : ClusterNoColl k (cmRel m k v)) : ClusterNoColl k v := by
  intro i hi j hj hij hEq
  refine h i hi j hj hij ?_
  have h2 : cmRel m k v i - cmRel m k v j = v i - v j := cmRel_sub_of_mem v hi hj
  rw [hEq, sub_self] at h2
  exact sub_eq_zero.mp h2

/-- `ClusterNoColl` is invariant under a nonzero scaling. -/
lemma clusterNoColl_of_smul {c : ℝ} {k : Finset (Fin N)} {v : EN E N} (hc : c ≠ 0)
    (h : ClusterNoColl k (c • v)) : ClusterNoColl k v := by
  intro i hi j hj hij hEq
  exact h i hi j hj hij (by rw [PiLp.smul_apply, PiLp.smul_apply, hEq])

/-- **The bumped curve is collision free on the window** (right side). -/
lemma withoutCollisions_bumpCurve_shift {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ ν s : ℝ} (hlam : 0 < lam)
    (hs : 0 ≤ s)
    {γ : ℝ → EN E N} (hν : 0 < ν)
    (hsep : ClusterSeparatedWeak k (γ (t₀ + lam * s)) ν)
    (hρ : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν)
    (hγ : WithoutCollisions (γ (t₀ + lam * s)))
    (hnn : ClusterNoColl k (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)) :
    WithoutCollisions (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hρ0 : 0 ≤ lam ^ ((2:ℝ)/3) * ‖δ‖ :=
    mul_nonneg (Real.rpow_nonneg hlam.le _) (norm_nonneg δ)
  set rhoP : ℝ := lam ^ ((2:ℝ)/3) * ‖δ‖ with hrhoP
  have hpert : ∀ j : Fin N,
      ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j‖ ≤ rhoP := by
    intro j
    by_cases hj : j ∈ k
    · rw [hrhoP]
      exact bumpCurve_pert_le hm hi₀ hlam hs hj
    · rw [bumpCurve_eq_of_notMem (m := m) (k := k) hlam hs hj, sub_self, norm_zero, hrhoP]
      exact hρ0
  -- inside `k`
  have hin : ClusterNoColl k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) := by
    have h1 : bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s
        = lam ^ (-(2:ℝ)/3) •
            cmRel m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) :=
      (bumpRescaled_shift hm hi₀ hlam hs).symm
    rw [h1] at hnn
    exact clusterNoColl_of_clusterNoColl_cmRel
      (clusterNoColl_of_smul (Real.rpow_pos_of_pos hlam (-(2:ℝ)/3)).ne' hnn)
  intro i j hij
  rw [r_ne_zero_iff]
  by_cases hi : i ∈ k
  · by_cases hj : j ∈ k
    · -- both in the cluster
      exact hin i hi j hj hij
    · -- `i` inside, `j` outside
      have hbase : ν ≤ ‖γ (t₀ + lam * s) i - γ (t₀ + lam * s) j‖ := by
        have h1 := hsep i hi j hj
        rwa [r_eq_norm_sub] at h1
      have hb : ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i‖ ≤ rhoP :=
        hpert i
      have hb2 : bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j = γ (t₀ + lam * s) j :=
        bumpCurve_eq_of_notMem hlam hs hj
      intro hEq
      have h3 : ‖γ (t₀ + lam * s) i - γ (t₀ + lam * s) j‖
          ≤ ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
              - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j‖
            + ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i‖
            + ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j‖ := by
        have he : γ (t₀ + lam * s) i - γ (t₀ + lam * s) j
            = (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
                - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j)
              - ((bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i)
                - (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j)) := by
          abel
        rw [he]
        have h4 := norm_sub_le
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
            - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j)
          ((bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i)
            - (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j))
        have h5 := norm_sub_le
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i)
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j)
        linarith
      have hzero : ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
          - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j‖ = 0 := by
        rw [hEq, sub_self, norm_zero]
      have hzero2 : ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j‖ = 0 := by
        rw [hb2, sub_self, norm_zero]
      linarith [hbase, h3, hb, hzero, hzero2, hρ, hν]
  · by_cases hj : j ∈ k
    · -- `j` inside, `i` outside
      have hbase : ν ≤ ‖γ (t₀ + lam * s) i - γ (t₀ + lam * s) j‖ := by
        have h1 := hsep j hj i hi
        rw [r_eq_norm_sub, norm_sub_rev] at h1
        exact h1
      have hb : ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j‖ ≤ rhoP :=
        hpert j
      have hb2 : bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i = γ (t₀ + lam * s) i :=
        bumpCurve_eq_of_notMem hlam hs hi
      intro hEq
      have h3 : ‖γ (t₀ + lam * s) i - γ (t₀ + lam * s) j‖
          ≤ ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
              - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j‖
            + ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i‖
            + ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j‖ := by
        have he : γ (t₀ + lam * s) i - γ (t₀ + lam * s) j
            = (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
                - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j)
              - ((bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i)
                - (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j)) := by
          abel
        rw [he]
        have h4 := norm_sub_le
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
            - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j)
          ((bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i)
            - (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j))
        have h5 := norm_sub_le
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i)
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j)
        linarith
      have hzero : ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i
          - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j‖ = 0 := by
        rw [hEq, sub_self, norm_zero]
      have hzero2 : ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i - γ (t₀ + lam * s) i‖ = 0 := by
        rw [hb2, sub_self, norm_zero]
      linarith [hbase, h3, hb, hzero, hzero2, hρ, hν]
    · -- both outside: the perturbation vanishes
      have h1 : bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) i = γ (t₀ + lam * s) i :=
        bumpCurve_eq_of_notMem hlam hs hi
      have h2 : bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j = γ (t₀ + lam * s) j :=
        bumpCurve_eq_of_notMem hlam hs hj
      intro hEq
      exact ne_of_r_ne_zero (hγ i j hij) (by rw [← h1, ← h2, hEq])


end Submission.NBody
