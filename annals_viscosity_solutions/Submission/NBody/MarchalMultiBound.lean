import Submission.NBody.MarchalMultiEnergyBound
import Submission.NBody.MarchalOutsideVelocity
import Submission.NBody.MarchalClusterAccel
import Submission.NBody.MarchalMultiEnergy

/-!
# The sum-level energy bound for a family of colliding clusters

This module assembles the hypothesis `hE` of `multiInertia_asymptotic` (the sum-level Sundman
analysis) from the geometry of a simultaneous collision of several clusters `C₁, …, C_r`:

* the outside bodies and the centres of mass of the clusters move with **bounded** velocity on
  `(0, ε)` (their accelerations are bounded because everything is `ν`-separated);
* the total energy is conserved;
* the interaction potentials are bounded because everything is `ν`-separated.

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

/-- The union of the clusters is separated from its complement as soon as each cluster is
one-sidedly separated and the bodies outside the union are pairwise separated. -/
lemma clusterSeparated_multiUnion {ks : Finset (Finset (Fin N))} {x : EN E N} {ν : ℝ}
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k x ν)
    (hsepT : ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks, i ≠ j → ν ≤ r x i j) :
    ClusterSeparated (multiUnion ks) x ν := by
  refine ClusterSeparated.of_weak ?_ hsepT
  intro i hi j hj
  obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
  exact hsep k hk i hik j (fun hjk => hj (Finset.mem_biUnion.mpr ⟨k, hk, hjk⟩))

/-- **The centre-of-mass acceleration of a cluster is bounded.**  One-sided separation suffices:
the internal forces cancel and the interaction forces are bounded by `ν⁻²`. -/
lemma norm_clusterCM_weightedGrad_le_weak {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    {ν : ℝ} (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hsep : ClusterSeparatedWeak k x ν)
    (hnc : WithoutCollisions x) :
    ‖clusterCM m k (∇_[m] (U m) x)‖
      ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) := by
  classical
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
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
  have hcm : ∑ i ∈ k, m i • (∇_[m] (U m) x) i = ∑ i ∈ k, (gradient (U m) x) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gradient_eq_smul_weightedGrad m hmne x i]
  calc ‖clusterCM m k (∇_[m] (U m) x)‖
      = (clusterMass m k)⁻¹ * ‖∑ i ∈ k, (gradient (U m) x) i‖ := by
        rw [clusterCM, hcm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))]
    _ ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))

/-- **The sum of the relative energies of a simultaneously colliding family of clusters is
bounded.**  Ferrario–Terracini, `nr:next`. -/
theorem exists_multiRelEnergy_bound {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε ν : ℝ} (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hν : 0 < ν)
    (hne : ∀ k ∈ ks, k.Nonempty) (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, deriv (deriv x) t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hsepT : ∀ t ∈ Ioo (0:ℝ) ε, ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks, i ≠ j →
      ν ≤ r (x t) i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0:ℝ) (ε / 4),
      |multiRelEnergy m ks (x t) (deriv x t)| ≤ C := by
  classical
  have hq : 0 < ε / 4 := by linarith
  have hquarter : ε / 4 ∈ Ioo (0:ℝ) ε := ⟨by linarith, by linarith⟩
  -- (1) the union is separated
  have hsepU : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparated (multiUnion ks) (x t) ν := fun t ht =>
    clusterSeparated_multiUnion (fun k hk => hsep t ht k hk)
      (fun i hi j hj hij => hsepT t ht i hi j hj hij)
  -- (2) the outside velocities are bounded
  have hd2' : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t := fun t ht =>
    (hd2 t ht).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t).symm
  have hode' : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t) := by
    intro t ht
    rw [iteratedDeriv_two_eq_deriv_deriv]
    exact hode t ht
  obtain ⟨CvT, hCvT0, hvT⟩ := exists_bound_deriv_outside (m := m) (k := multiUnion ks)
    hm hε hν hsepU hnc hode' hd2'
  -- (3) the centre-of-mass velocities are bounded
  have hA0 : ∀ k ∈ ks, 0 ≤ (clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) := by
    intro k _
    have h1 : 0 ≤ (clusterMass m k)⁻¹ := inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k)
    have h2 : 0 ≤ (∑ i ∈ k, ∑ j with j ∉ k, m i * m j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le
    have h3 : 0 ≤ ν⁻¹ ^ 2 := sq_nonneg _
    exact mul_nonneg h1 (mul_nonneg h2 h3)
  have hacc : ∀ k ∈ ks, ∀ t ∈ Ioo (0:ℝ) ε,
      ‖clusterCM m k (iteratedDeriv 2 x t)‖
        ≤ (clusterMass m k)⁻¹ * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) := by
    intro k hk t ht
    rw [hode' t ht]
    exact norm_clusterCM_weightedGrad_le_weak (m := m) (k := k) (x := x t) (ν := ν)
      hm hν (hsep t ht k hk) (hnc t ht)
  set Ccm : ℝ := ∑ k ∈ ks, ((clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j with j ∉ k, m i * m j) * ν⁻¹ ^ 2) * (ε / 4)
        + ‖clusterCM m k (deriv x (ε / 4))‖) with hCcm
  have hCcm0 : 0 ≤ Ccm := by
    rw [hCcm]
    refine Finset.sum_nonneg fun k hk => ?_
    have h2 : 0 ≤ ‖clusterCM m k (deriv x (ε / 4))‖ := norm_nonneg _
    have h3 : 0 ≤ ε / 4 := by linarith
    nlinarith [hA0 k hk, h2, h3]
  refine ⟨|energy m x ((ε / 4) / 2)| + (∑ j ∈ (multiUnion ks)ᶜ, m j) * CvT ^ 2 / 2
      + (∑ k ∈ ks, clusterMass m k) * Ccm ^ 2 / 2
      + (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν, ?_, ?_⟩
  · have h1 : 0 ≤ |energy m x ((ε / 4) / 2)| := abs_nonneg _
    have h2 : 0 ≤ (∑ j ∈ (multiUnion ks)ᶜ, m j) * CvT ^ 2 / 2 :=
      div_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (sq_nonneg _)) (by norm_num)
    have h3 : 0 ≤ (∑ k ∈ ks, clusterMass m k) :=
      Finset.sum_nonneg fun k _ => clusterMass_nonneg (fun i => (hm i).le) k
    have h4 : 0 ≤ Ccm ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
    have h5 : 0 ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν :=
      div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le) hν.le
    nlinarith [h1, h2, h3, h4, h5]
  · intro t ht
    have hmem : ∀ u ∈ Ioo (0:ℝ) (ε / 4), u ∈ Ioo (0:ℝ) ε :=
      fun u hu => ⟨hu.1, lt_trans hu.2 (by linarith)⟩
    have hcm : ∀ u ∈ Ioo (0:ℝ) (ε / 4), ∀ k ∈ ks, ‖clusterCM m k (deriv x u)‖ ≤ Ccm := by
      intro u hu k hk
      have hb := exists_bound_clusterCM_deriv (m := m) (k := k) (x := x) hε (hA0 k hk) hd2'
        (fun s hs => hacc k hk s hs) u hu
      have hs := Finset.single_le_sum
        (f := fun k' => (clusterMass m k')⁻¹
          * ((∑ i ∈ k', ∑ j with j ∉ k', m i * m j) * ν⁻¹ ^ 2) * (ε / 4)
            + ‖clusterCM m k' (deriv x (ε / 4))‖)
        (fun k' hk' => by
          have h2 : 0 ≤ ‖clusterCM m k' (deriv x (ε / 4))‖ := norm_nonneg _
          have h3 : 0 ≤ ε / 4 := by linarith
          nlinarith [hA0 k' hk', h2, h3]) hk
      rw [hCcm]
      linarith
    have hH : ∀ u ∈ Ioo (0:ℝ) (ε / 4), energy m x u = energy m x ((ε / 4) / 2) := by
      intro u hu
      exact energy_eq_of_mem_Ioo (ε := ε) (fun i => (hm i).ne') (fun s hs => hx s hs)
        (fun s hs => hd2' s hs) (fun s hs => hode' s hs) (fun s hs => hnc s hs)
        (hmem u hu) ⟨by linarith, by linarith⟩
    exact multiRelEnergy_le (m := m) (ks := ks) (x := x) (ε := ε / 4) (ν := ν)
      hm hq hν hCvT0 hCcm0 hne hedj
      (fun u hu k hk => hsep u (hmem u hu) k hk)
      (fun u hu i hi j hj hij => hsepT u (hmem u hu) i hi j hj hij)
      (fun u hu j hj => hvT u (hmem u hu) j hj)
      hcm hH t ht

/-- A single coordinate of the centre-of-mass-relative configuration, squared, is bounded by the
cluster's moment of inertia. -/
lemma norm_cmRel_apply_sq_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) (k : Finset (Fin N))
    (y : EN E N) (p : Fin N) :
    ‖(cmRel m k y) p‖ ^ 2 ≤ (m p)⁻¹ * clusterInertia m k y := by
  have hmp : 0 < m p := hm p
  by_cases hp : p ∈ k
  · have h1 : m p * ‖(cmRel m k y) p‖ ^ 2 ≤ clusterInertia m k y := by
      rw [clusterInertia, cmRel_apply_of_mem hp]
      exact Finset.single_le_sum (f := fun i => m i * ‖y i - clusterCM m k y‖ ^ 2)
        (fun i _ => mul_nonneg (hm i).le (sq_nonneg _)) hp
    calc ‖(cmRel m k y) p‖ ^ 2 = (m p)⁻¹ * (m p * ‖(cmRel m k y) p‖ ^ 2) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmp), one_mul]
      _ ≤ (m p)⁻¹ * clusterInertia m k y :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hmp))
  · rw [cmRel_apply_of_notMem hp, norm_zero]
    have h0 : 0 ≤ clusterInertia m k y :=
      clusterInertia_nonneg (fun i => (hm i).le) k y
    simpa using mul_nonneg (le_of_lt (inv_pos.mpr hmp)) h0

/-- **The interaction work of a family of clusters is bounded**, once all the clusters are small. -/
theorem exists_multiCrossWork_bound {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε ν γ : ℝ} (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hν : 0 < ν) (hγ0 : 0 ≤ γ)
    (hγm : ∀ p : Fin N, γ ≤ m p)
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hI : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, clusterInertia m k (x t) ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0:ℝ) ε, |multiCrossWork m ks (x t)| ≤ C := by
  classical
  have hpair0 : 0 ≤ ∑ p ∈ pairFinset N, m p.1 * m p.2 * (2 * 1 : ℝ) :=
    Finset.sum_nonneg fun p _ => by
      have h1 : 0 ≤ m p.1 * m p.2 := mul_nonneg (hm p.1).le (hm p.2).le
      nlinarith [h1]
  refine ⟨(ks.card : ℝ) * ((∑ p ∈ pairFinset N, m p.1 * m p.2 * (2 * 1 : ℝ)) * (ν⁻¹) ^ 2),
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hpair0 (sq_nonneg _)), fun t ht => ?_⟩
  refine multiCrossWork_le (m := m) (ks := ks) (x := x t) (ν := ν) (R := 1)
    (fun i => (hm i).le) hν (by norm_num) (fun k hk => hsep t ht k hk) (fun k hk p => ?_)
  have h2 := norm_cmRel_apply_sq_le hm k (x t) p
  have h3 : clusterInertia m k (x t) ≤ γ := hI t ht k hk
  have hp : 0 < m p := hm p
  have h4 : (m p)⁻¹ * clusterInertia m k (x t) ≤ 1 := by
    rw [inv_mul_le_iff₀ hp]
    linarith [h3, hγm p]
  have h5 : ‖(cmRel m k (x t)) p‖ ^ 2 ≤ 1 := le_trans h2 h4
  have h6 : 0 ≤ ‖(cmRel m k (x t)) p‖ := norm_nonneg _
  nlinarith [h5, h6]

end Submission.NBody