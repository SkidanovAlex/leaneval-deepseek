import Submission.NBody.MarchalMultiBound

/-!
# Boundedness of the outside and centre-of-mass kinetic energies

The geometry of the Marchal chapter (F1), sixth layer.  The sum-level Sundman analysis
(`multiInertia_kinetic_bound`) takes as hypotheses the boundedness of the kinetic energy of the
bodies *outside* the union of the colliding clusters (`hKout`) and of the kinetic energy of the
centres of mass (`hKcm`).  Both follow from the fact that those bodies never collide with the
collapsing clusters: the corresponding accelerations are bounded, and the mean value inequality
bounds the velocities.

These are the sum-level analogues of the estimates already used inside
`MarchalMultiBound.exists_multiRelEnergy_bound`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The kinetic energy of the bodies outside the union of the clusters is bounded.** -/
theorem exists_multiOutsideKineticSq_bound {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε ν : ℝ} (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hν : 0 < ν)
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparated (multiUnion ks) (x t) ν)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t) :
    ∃ Cout : ℝ, 0 ≤ Cout ∧ ∀ t ∈ Ioo (0:ℝ) ε, multiOutsideKineticSq m ks (deriv x t) ≤ Cout := by
  classical
  obtain ⟨Cv, hCv0, hv⟩ := exists_bound_deriv_outside (m := m) (k := multiUnion ks)
    hm hε hν hsep hnc hode hd2
  refine ⟨(∑ i, m i) * Cv ^ 2, mul_nonneg (Finset.sum_nonneg fun i _ => (hm i).le) (sq_nonneg _),
    fun t ht => ?_⟩
  have h1 : multiOutsideKineticSq m ks (deriv x t)
      = ∑ i ∈ (multiUnion ks)ᶜ, m i * ‖deriv x t i‖ ^ 2 := rfl
  rw [h1]
  calc ∑ i ∈ (multiUnion ks)ᶜ, m i * ‖deriv x t i‖ ^ 2
      ≤ ∑ i ∈ (multiUnion ks)ᶜ, m i * Cv ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ∉ multiUnion ks := Finset.mem_compl.mp hi
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hv t ht i hi') 2)
          (hm i).le
    _ ≤ ∑ i, m i * Cv ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => mul_nonneg (hm i).le (sq_nonneg _))
    _ = (∑ i, m i) * Cv ^ 2 := (Finset.sum_mul (Finset.univ) m (Cv ^ 2)).symm

/-- **The kinetic energy of the centres of mass of the clusters is bounded.** -/
theorem exists_multiCMKineticSq_bound {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε ν : ℝ} (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hν : 0 < ν)
    (hne : ∀ k ∈ ks, k.Nonempty)
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t) :
    ∃ Ccm : ℝ, 0 ≤ Ccm ∧ ∀ t ∈ Ioo (0:ℝ) (ε / 4), multiCMKineticSq m ks (deriv x t) ≤ Ccm := by
  classical
  have hacc0 : ∀ k ∈ ks, ∀ t ∈ Ioo (0:ℝ) ε,
      ‖clusterCM m k (iteratedDeriv 2 x t)‖
        ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) := by
    intro k hk t ht
    rw [hode t ht]
    exact norm_clusterCM_weightedGrad_le_weak (m := m) (k := k) (x := x t) (ν := ν)
      hm hν (hsep t ht k hk) (hnc t ht)
  have hA0 : ∀ k ∈ ks, 0 ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) := by
    intro k _
    have h1 : 0 ≤ (clusterMass m k)⁻¹ := inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k)
    have h2 : 0 ≤ (∑ i ∈ k, ∑ j with j ∉ k, m i * m j) :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => mul_nonneg (hm i).le (hm j).le
    exact mul_nonneg h1 (mul_nonneg h2 (sq_nonneg _))
  set Ccm : ℝ := ∑ k ∈ ks, clusterMass m k * ((clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) * (ε / 4)
        + ‖clusterCM m k (deriv x (ε / 4))‖) ^ 2 with hCcm
  have hCcmnn : 0 ≤ Ccm := by
    rw [hCcm]
    refine Finset.sum_nonneg fun k _ =>
      mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)
  refine ⟨Ccm, hCcmnn, fun t ht => ?_⟩
  have hbound : ∀ k ∈ ks, ‖clusterCM m k (deriv x t)‖
      ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) * (ε / 4)
        + ‖clusterCM m k (deriv x (ε / 4))‖ :=
    fun k hk => exists_bound_clusterCM_deriv (m := m) (k := k) (x := x) hε (hA0 k hk) hd2
      (fun s hs => hacc0 k hk s hs) t ht
  rw [multiCMKineticSq, hCcm]
  exact Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound k hk) 2)
      (clusterMass_nonneg (fun i => (hm i).le) k)

end Submission.NBody
