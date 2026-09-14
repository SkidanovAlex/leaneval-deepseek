import Submission.NBody.MarchalClusterAccel
import Submission.NBody.MarchalClusterAsymptotic

/-!
# Sundman's law for an isolated colliding cluster

Combining the boundedness of the relative energy and of the interaction work (which hold for an
*isolated* colliding cluster: the bodies of `k` collapse at `t = 0` while all the other pairs stay
separated with bounded velocities) with the analytic machinery of `MarchalClusterAsymptotic`, we
obtain the classical asymptotic law: there is `κ > 0` with

    `I_k(x(t)) / t^{4/3} → κ`   as `t → 0⁺`.

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

/-- **Sundman's asymptotic law for an isolated colliding cluster.** -/
theorem clusterInertia_asymptotic_of_isolated {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hν : 0 < ν) (hCv : 0 ≤ Cv)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparated k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k, ‖deriv x t j‖ ≤ Cv)
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  -- the acceleration of the centre of mass is bounded
  have hA : 0 ≤ (clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) * (ν⁻¹) ^ 2) :=
    mul_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))
      (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le) (sq_nonneg _))
  have hacc : ∀ t ∈ Ioo (0:ℝ) ε,
      ‖clusterCM m k (iteratedDeriv 2 x t)‖
        ≤ (clusterMass m k)⁻¹
          * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
              * (ν⁻¹) ^ 2) := by
    intro t ht
    rw [hode t ht]
    exact norm_clusterCM_weightedGrad_le hm hν (hsep t ht).weak (hnc t ht)
  -- the velocity of the centre of mass is bounded
  have hcm : ∀ t ∈ Ioo (0:ℝ) (ε / 4), ‖clusterCM m k (deriv x t)‖
      ≤ (clusterMass m k)⁻¹
          * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
              * (ν⁻¹) ^ 2) * (ε / 4)
        + ‖clusterCM m k (deriv x (ε / 4))‖ := by
    refine exists_bound_clusterCM_deriv hε hA (fun t ht => hd2 t ?_) (fun t ht => hacc t ?_)
    · exact ⟨ht.1, by linarith [ht.2, hε]⟩
    · exact ⟨ht.1, by linarith [ht.2, hε]⟩
  obtain ⟨ε', C, hε'pos, hε'le, hCpos, hbound⟩ :=
    exists_clusterRelEnergy_crossWork_bound (m := m) (k := k) (x := x) (ε := ε / 4)
      hm (by linarith) hkne
      (fun t ht => hnc t ⟨ht.1, by linarith [ht.2, hε]⟩)
      (fun t ht => hx t ⟨ht.1, by linarith [ht.2, hε]⟩)
      (fun t ht => hd2 t ⟨ht.1, by linarith [ht.2, hε]⟩)
      (fun t ht => hode t ⟨ht.1, by linarith [ht.2, hε]⟩)
      hν (fun t ht => hsep t ⟨ht.1, by linarith [ht.2, hε]⟩) hCv
      (fun t ht j hj => hv t ⟨ht.1, by linarith [ht.2, hε]⟩ j hj)
      (le_trans (norm_nonneg _) (hcm (ε/8) ⟨by linarith, by linarith⟩))
      hcm hI
  obtain ⟨κ, hκpos, hκ⟩ := clusterInertia_asymptotic (m := m) (k := k) (x := x) (ε := ε')
    (C := C) hm hk2 hε'pos hCpos
    (fun t ht => hnc t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans hε'le (by linarith))⟩)
    (fun t ht => (hbound t ht).1)
    (fun t ht => (hbound t ht).2)
    (fun t ht => hx t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans hε'le (by linarith))⟩)
    (fun t ht => hd2 t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans hε'le (by linarith))⟩)
    (fun t ht => hode t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans hε'le (by linarith))⟩)
    hI
  exact ⟨κ, hκpos, hκ⟩

end Submission.NBody
