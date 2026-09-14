import Submission.NBody.MarchalMultiOstrogradsky
import Submission.NBody.MarchalClusterBound

/-!
# The energy of a family of simultaneously colliding clusters

At a collision time with several collision classes `C₁, …, C_r`, the single-cluster energy bound of
`MarchalClusterBound` (which needs the *velocities of all bodies outside the cluster* to be bounded)
is not available: the bodies of the other classes blow up as well.  What *is* bounded is the
**sum** of the relative energies, because the total energy is conserved and the only unbounded
contributions cancel:

    `∑_l E^{rel}_{C_l} = H - K_T + (U - ∑_l U_{C_l}) - ∑_l m_{C_l}‖v_{cm,C_l}‖²/2`,

where `T = (⋃_l C_l)ᶜ` is the set of bodies not involved in the collision at all.  Every term on the
right is bounded: `H` is conserved, `K_T` is bounded since the `T`-bodies are separated from
everything, the potential remainder is bounded by the separation, and the centre-of-mass velocities
are bounded because the centres of mass move smoothly.

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

/-- The one-sided separation together with the separation of the complement gives the two-sided
`ClusterSeparated`. -/
lemma ClusterSeparated.of_weak {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (h1 : ClusterSeparatedWeak k x ν)
    (h2 : ∀ i ∉ k, ∀ j ∉ k, i ≠ j → ν ≤ r x i j) : ClusterSeparated k x ν := by
  intro i j hij hk
  by_cases hi : i ∈ k
  · exact h1 i hi j fun hj => hk ⟨hi, hj⟩
  · by_cases hj : j ∈ k
    · have h2' : ν ≤ r x j i := h1 j hj i hi
      have hgoal : r x j i = r x i j := by
        rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]
      rwa [hgoal] at h2'
    · exact h2 i hi j hj hij

/-- The union of a finite family of clusters. -/
noncomputable def multiUnion (ks : Finset (Finset (Fin N))) : Finset (Fin N) := ks.biUnion id

/-- The potential of the pairs which are not internal to any one of the clusters. -/
noncomputable def multiRestPotential (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (x : EN E N) : ℝ := U m x - multiPotential m ks x

/-- Twice the total kinetic energy of the centres of mass of the clusters. -/
noncomputable def multiCMKineticSq (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (v : EN E N) : ℝ := ∑ k ∈ ks, clusterMass m k * ‖clusterCM m k v‖ ^ 2

/-- Twice the kinetic energy of the bodies outside the union of the clusters. -/
noncomputable def multiOutsideKineticSq (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (v : EN E N) : ℝ :=
  ∑ i ∈ (multiUnion ks)ᶜ, m i * ‖v i‖ ^ 2

/-- **The sum of the relative energies of a family of clusters.** -/
theorem multiRelEnergy_eq (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k') (x : ℝ → EN E N) (t : ℝ) :
    multiRelEnergy m ks (x t) (deriv x t)
      = energy m x t - multiOutsideKineticSq m ks (deriv x t) / 2
        - multiCMKineticSq m ks (deriv x t) / 2 + multiRestPotential m ks (x t) := by
  classical
  have hbij : ∑ k ∈ ks, ∑ i ∈ k, m i * ‖deriv x t i‖ ^ 2
      = ∑ i ∈ multiUnion ks, m i * ‖deriv x t i‖ ^ 2 := by
    rw [multiUnion]
    exact (Finset.sum_biUnion (f := fun i => m i * ‖deriv x t i‖ ^ 2) hedj).symm
  have hsplit : (∑ i, m i * ‖deriv x t i‖ ^ 2)
      = (∑ i ∈ multiUnion ks, m i * ‖deriv x t i‖ ^ 2)
        + ∑ i ∈ (multiUnion ks)ᶜ, m i * ‖deriv x t i‖ ^ 2 :=
    (Finset.sum_add_sum_compl (multiUnion ks) (fun i => m i * ‖deriv x t i‖ ^ 2)).symm
  have hK : ∑ k ∈ ks, clusterKineticSq m k (deriv x t)
      = ∑ i ∈ multiUnion ks, m i * ‖deriv x t i‖ ^ 2 := by
    rw [← hbij]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hrel : ∀ k ∈ ks, clusterRelEnergy m k (x t) (deriv x t)
      = clusterKineticSq m k (deriv x t) / 2
        - clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2
        - clusterPotential m k (x t) := by
    intro k hk
    unfold clusterRelEnergy clusterRelKinetic
    rw [clusterKineticSq_cmRel k (deriv x t) hm (hne k hk)]
    ring
  have hmain : multiRelEnergy m ks (x t) (deriv x t)
      = kinetic m (deriv x t) - multiOutsideKineticSq m ks (deriv x t) / 2
        - multiCMKineticSq m ks (deriv x t) / 2 - multiPotential m ks (x t) := by
    rw [multiRelEnergy, Finset.sum_congr rfl hrel, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.sum_div]
    rw [hK, multiCMKineticSq, multiOutsideKineticSq, multiPotential]
    rw [kinetic, hsplit]
    ring
  have hkin : kinetic m (deriv x t) = energy m x t + U m (x t) := by
    unfold kinetic energy
    ring
  rw [hmain, hkin, multiRestPotential, multiPotential]
  ring

/-- Summing a function over the internal pairs of each cluster is the same as summing it over the
pairs which are internal to (at least) one of the clusters. -/
theorem sum_internal_pairs_eq {f : Fin N × Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k') :
    (∑ k ∈ ks, ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k), f p)
      = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N =>
          ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k), f p := by
  classical
  have hpt : ∀ p : Fin N × Fin N,
      (∑ k ∈ ks, (if p.1 ∈ k ∧ p.2 ∈ k then f p else 0))
        = (if ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k then f p else 0) := by
    intro p
    by_cases hp : ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k
    · rw [if_pos hp]
      obtain ⟨k, hk, hp1, hp2⟩ := hp
      have hzero : ∀ b, b ∈ ks → b ≠ k → (if p.1 ∈ b ∧ p.2 ∈ b then f p else 0) = 0 := by
        intro b hb hbk
        rw [if_neg]
        intro hcon
        exact ((Finset.disjoint_left.mp (hedj b hb k hk hbk)) hcon.1 hp1).elim
      rw [Finset.sum_eq_single k hzero (fun hknot => absurd hk hknot)]
      rw [if_pos ⟨hp1, hp2⟩]
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [if_neg]
      intro hcon
      exact hp ⟨k, hk, hcon⟩
  calc (∑ k ∈ ks, ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k), f p)
      = ∑ k ∈ ks, ∑ p ∈ pairFinset N, (if p.1 ∈ k ∧ p.2 ∈ k then f p else 0) :=
        Finset.sum_congr rfl fun k _ =>
          Finset.sum_filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k) f
    _ = ∑ p ∈ pairFinset N, ∑ k ∈ ks, (if p.1 ∈ k ∧ p.2 ∈ k then f p else 0) :=
        Finset.sum_comm
    _ = ∑ p ∈ pairFinset N, (if ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k then f p else 0) :=
        Finset.sum_congr rfl fun p _ => hpt p
    _ = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N =>
          ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k), f p :=
        (Finset.sum_filter (fun p : Fin N × Fin N => ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k) f).symm

/-- **The potential of the pairs which are not internal to any one of the clusters.** -/
theorem multiRestPotential_eq {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k') (x : EN E N) :
    multiRestPotential m ks x
      = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N =>
          ¬ (∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := by
  classical
  have h1 := sum_internal_pairs_eq (ks := ks)
    (f := fun p : Fin N × Fin N => m p.1 * m p.2 * (r x p.1 p.2)⁻¹) hedj
  simp only [multiRestPotential, multiPotential, clusterPotential] at *
  rw [h1, U_eq_pairFinset]
  have h := Finset.sum_filter_add_sum_filter_not (pairFinset N)
    (fun p : Fin N × Fin N => ∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k)
    (fun p : Fin N × Fin N => m p.1 * m p.2 * (r x p.1 p.2)⁻¹)
  linarith [h]

/-- The per-term bound of the potential of the pairs which are not internal to any cluster. -/
lemma multiRestPotential_term_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {ks : Finset (Finset (Fin N))} {x : EN E N} {ν : ℝ} (hν : 0 < ν)
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k x ν)
    (hsepT : ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks, i ≠ j → ν ≤ r x i j)
    {p : Fin N × Fin N} (hp : p ∈ (pairFinset N).filter
      (fun p : Fin N × Fin N => ¬ (∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k))) :
    m p.1 * m p.2 * (r x p.1 p.2)⁻¹ ≤ m p.1 * m p.2 / ν := by
  have hp' := (Finset.mem_filter.mp hp).2
  have hlt : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact ne_of_lt this
  have hdist : ν ≤ r x p.1 p.2 := by
    by_cases h1 : p.1 ∈ multiUnion ks
    · obtain ⟨k, hk, hp1⟩ := Finset.mem_biUnion.mp h1
      exact hsep k hk p.1 hp1 p.2 fun h2 => hp' ⟨k, hk, hp1, h2⟩
    · by_cases h2 : p.2 ∈ multiUnion ks
      · obtain ⟨k, hk, hp2⟩ := Finset.mem_biUnion.mp h2
        have hh : ν ≤ r x p.2 p.1 :=
          hsep k hk p.2 hp2 p.1 fun h1' => hp' ⟨k, hk, h1', hp2⟩
        rwa [show r x p.2 p.1 = r x p.1 p.2 from by
          rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]] at hh
      · exact hsepT p.1 h1 p.2 h2 hlt
  have hpos : 0 < r x p.1 p.2 := lt_of_lt_of_le hν hdist
  have hinv : (r x p.1 p.2)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hpos hν).mpr hdist
  calc m p.1 * m p.2 * (r x p.1 p.2)⁻¹ ≤ m p.1 * m p.2 * ν⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg (hm p.1) (hm p.2))
    _ = m p.1 * m p.2 / ν := by rw [div_eq_mul_inv]

/-- **The potential of the pairs which are not internal to any cluster is bounded.** -/
theorem multiRestPotential_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {ks : Finset (Finset (Fin N))} {x : EN E N} {ν : ℝ} (hν : 0 < ν)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k x ν)
    (hsepT : ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks, i ≠ j → ν ≤ r x i j) :
    multiRestPotential m ks x ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν := by
  classical
  rw [multiRestPotential_eq hedj]
  calc ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N =>
          ¬ (∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2 * (r x p.1 p.2)⁻¹
      ≤ ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N =>
          ¬ (∃ k ∈ ks, p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2 / ν :=
        Finset.sum_le_sum fun p hp =>
          multiRestPotential_term_le hm hν hsep hsepT hp
    _ ≤ ∑ p ∈ pairFinset N, m p.1 * m p.2 / ν :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).1)
          (fun p _ _ => div_nonneg (mul_nonneg (hm p.1) (hm p.2)) hν.le)
    _ = (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν := (Finset.sum_div ..).symm

/-- **The interaction work of a cluster with one-sided separation.** -/
theorem abs_crossWork_le_weak {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν R : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hR : 0 ≤ R) (hsep : ClusterSeparatedWeak k x ν)
    (hd : ∀ p : Fin N, ‖(cmRel m k x) p‖ ≤ R) :
    |crossWork m k x (cmRel m k x)|
      ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2 * (2 * R)) * (ν⁻¹) ^ 2 := by
  classical
  rw [crossWork]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := (Finset.mem_filter.mp hp).2
  have hlt : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact ne_of_lt this
  have hd' : ‖(cmRel m k x) p.1 - (cmRel m k x) p.2‖ ≤ 2 * R := by
    calc ‖(cmRel m k x) p.1 - (cmRel m k x) p.2‖
        ≤ ‖(cmRel m k x) p.1‖ + ‖(cmRel m k x) p.2‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hd p.1) (hd p.2)
      _ = 2 * R := by ring
  by_cases hpq : p.1 ∈ k ∧ p.2 ∈ k
  · exact absurd hpq hp'
  · by_cases h1 : p.1 ∈ k
    · have hdist : ν ≤ ‖x p.1 - x p.2‖ := by
        rw [← r_eq_norm_sub]
        exact hsep p.1 h1 p.2 fun h2 => hpq ⟨h1, h2⟩
      exact abs_crossWork_term hm hν hR hlt hdist hd'
    · by_cases h2 : p.2 ∈ k
      · have hh : ν ≤ r x p.2 p.1 := hsep p.2 h2 p.1 h1
        have hdist : ν ≤ ‖x p.1 - x p.2‖ := by
          rw [← r_eq_norm_sub]
          rwa [show r x p.1 p.2 = r x p.2 p.1 from by
            rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]]
        exact abs_crossWork_term hm hν hR hlt hdist hd'
      · rw [cmRel_apply_of_notMem h1, cmRel_apply_of_notMem h2]
        simp only [sub_zero, inner_zero_right, mul_zero, abs_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (by linarith)) (sq_nonneg _)

/-- **The interaction work of a family of clusters.** -/
theorem multiCrossWork_le {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))} {x : EN E N} {ν R : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hR : 0 ≤ R)
    (hsep : ∀ k ∈ ks, ClusterSeparatedWeak k x ν)
    (hd : ∀ k ∈ ks, ∀ p : Fin N, ‖(cmRel m k x) p‖ ≤ R) :
    |multiCrossWork m ks x| ≤
      (ks.card : ℝ) * ((∑ p ∈ pairFinset N, m p.1 * m p.2 * (2 * R)) * (ν⁻¹) ^ 2) := by
  classical
  have hsum : ∀ p ∈ pairFinset N, 0 ≤ m p.1 * m p.2 * (2 * R) := fun p _ =>
    mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (by linarith)
  have hub : ∀ k ∈ ks, |crossWork m k x (cmRel m k x)|
      ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2 * (2 * R)) * (ν⁻¹) ^ 2 := by
    intro k hk
    refine le_trans (abs_crossWork_le_weak (m := m) (k := k) (x := x) (ν := ν) (R := R)
      hm hν hR (hsep k hk) (hd k hk)) ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).1)
      (fun p hp _ => hsum p hp)
  calc |multiCrossWork m ks x|
      = |∑ k ∈ ks, crossWork m k x (cmRel m k x)| := rfl
    _ ≤ ∑ k ∈ ks, |crossWork m k x (cmRel m k x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ ks, (∑ p ∈ pairFinset N, m p.1 * m p.2 * (2 * R)) * (ν⁻¹) ^ 2 :=
        Finset.sum_le_sum hub
    _ = (ks.card : ℝ) * ((∑ p ∈ pairFinset N, m p.1 * m p.2 * (2 * R)) * (ν⁻¹) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The sum of the relative energies of a family of clusters is bounded.** -/
theorem multiRelEnergy_le {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))} {x : ℝ → EN E N}
    {ε ν CvT Ccm : ℝ} (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hν : 0 < ν) (hCvT : 0 ≤ CvT)
    (hCcm : 0 ≤ Ccm) (hne : ∀ k ∈ ks, k.Nonempty)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x t) ν)
    (hsepT : ∀ t ∈ Ioo (0:ℝ) ε, ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks, i ≠ j →
      ν ≤ r (x t) i j)
    (hvT : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ multiUnion ks, ‖deriv x t j‖ ≤ CvT)
    (hcm : ∀ t ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ‖clusterCM m k (deriv x t)‖ ≤ Ccm)
    (hH : ∀ t ∈ Ioo (0:ℝ) ε, energy m x t = energy m x (ε / 2)) :
    ∀ t ∈ Ioo (0:ℝ) ε, |multiRelEnergy m ks (x t) (deriv x t)|
      ≤ |energy m x (ε / 2)|
        + (∑ j ∈ (multiUnion ks)ᶜ, m j) * CvT ^ 2 / 2
        + (∑ k ∈ ks, clusterMass m k) * Ccm ^ 2 / 2
        + (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν := by
  intro t ht
  have hid := multiRelEnergy_eq m ks hm hne hedj x t
  -- bounds on the individual terms
  have hout : multiOutsideKineticSq m ks (deriv x t) / 2
      ≤ (∑ j ∈ (multiUnion ks)ᶜ, m j) * CvT ^ 2 / 2 := by
    rw [multiOutsideKineticSq]
    rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc (∑ i ∈ (multiUnion ks)ᶜ, m i * ‖deriv x t i‖ ^ 2)
        ≤ ∑ i ∈ (multiUnion ks)ᶜ, m i * CvT ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ∉ multiUnion ks := by simpa using hi
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hvT t ht i hi') 2) (hm i).le
      _ = (∑ i ∈ (multiUnion ks)ᶜ, m i) * CvT ^ 2 := by rw [Finset.sum_mul]
  have hcm' : multiCMKineticSq m ks (deriv x t) / 2
      ≤ (∑ k ∈ ks, clusterMass m k) * Ccm ^ 2 / 2 := by
    rw [multiCMKineticSq]
    rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc (∑ k ∈ ks, clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2)
        ≤ ∑ k ∈ ks, clusterMass m k * Ccm ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hcm t ht k hk) 2)
            (clusterMass_nonneg (fun i => (hm i).le) k)
      _ = (∑ k ∈ ks, clusterMass m k) * Ccm ^ 2 := by rw [Finset.sum_mul]
  have hrest : multiRestPotential m ks (x t)
      ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν :=
    multiRestPotential_le (fun i => (hm i).le) hν hedj (hsep t ht) (hsepT t ht)
  have hrest_nn : 0 ≤ multiRestPotential m ks (x t) := by
    rw [multiRestPotential_eq hedj]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hout_nn : 0 ≤ multiOutsideKineticSq m ks (deriv x t) / 2 := by
    rw [multiOutsideKineticSq]
    exact div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)) (by norm_num)
  have hcm_nn : 0 ≤ multiCMKineticSq m ks (deriv x t) / 2 := by
    rw [multiCMKineticSq]
    exact div_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)) (by norm_num)
  have hen : energy m x t = energy m x (ε / 2) := hH t ht
  have hC2nn : 0 ≤ (∑ j ∈ (multiUnion ks)ᶜ, m j) * CvT ^ 2 / 2 :=
    div_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (sq_nonneg _)) (by norm_num)
  have hC3nn : 0 ≤ (∑ k ∈ ks, clusterMass m k) * Ccm ^ 2 / 2 :=
    div_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ =>
      clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)) (by norm_num)
  have hC4nn : 0 ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν :=
    div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le) hν.le
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [hid, hen]
    linarith [neg_abs_le (energy m x (ε / 2)), hout, hcm', hrest_nn, hC2nn, hC3nn, hC4nn]
  · rw [hid, hen]
    linarith [le_abs_self (energy m x (ε / 2)), hout_nn, hcm_nn, hrest, hC2nn, hC3nn, hC4nn]


/-- **The kinetic energy is controlled by the sum of the internal potentials.**  This is
`multiRelEnergy_eq` rearranged; it is the algebraic identity which replaces the (unavailable)
boundedness of the velocities of the other colliding clusters. -/
theorem kinetic_le_multi {m : Fin N → ℝ} (ks : Finset (Finset (Fin N)))
    (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k') (x : ℝ → EN E N) (t : ℝ) :
    kinetic m (deriv x t)
      = multiRelEnergy m ks (x t) (deriv x t)
        + multiOutsideKineticSq m ks (deriv x t) / 2
        + multiCMKineticSq m ks (deriv x t) / 2 + multiPotential m ks (x t) := by
  have h := multiRelEnergy_eq m ks hm hne hedj x t
  rw [multiRestPotential] at h
  have hkin : kinetic m (deriv x t) = energy m x t + U m (x t) := by
    unfold kinetic energy
    ring
  linarith [h, hkin]


end Submission.NBody
