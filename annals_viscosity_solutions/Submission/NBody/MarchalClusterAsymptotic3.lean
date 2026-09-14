import Submission.NBody.MarchalClusterAsymptotic2

/-!
# The potential and kinetic asymptotics of a colliding cluster

Continuing `Submission.NBody.MarchalClusterAsymptotic2`, this file extracts from the
Lagrange–Jacobi identity `Ï_k = 4E_k^{rel} + 2U_k + 2W_k` the asymptotics of the potential and of
the centre-of-mass-relative kinetic energy:

* `U_k(x t) t^{2/3} → (2/9) κ`;
* `R_k(ẋ t) t^{2/3} → (4/9) κ`,

where `κ` is the constant of `I_k(x t) = κ t^{4/3} + o(t^{4/3})`.  The point is that the two
"small" terms `E_k^{rel}` and `W_k` are bounded, so multiplied by `t^{2/3}` they vanish.

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

/-- `t^{2/3} → 0` as `t → 0⁺`. -/
lemma tendsto_rpow_two_thirds_nhdsWithin_zero :
    Tendsto (fun t : ℝ => t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
  Filter.Tendsto.rpow_const_nhds_zero (tendsto_id.mono_left nhdsWithin_le_nhds) (by norm_num)

/-- A function bounded on `(0, ε)` times `t^{2/3}` tends to `0` as `t → 0⁺`. -/
lemma tendsto_mul_rpow_two_thirds_zero_of_bounded {g : ℝ → ℝ} {C ε : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hg : ∀ t ∈ Ioo (0:ℝ) ε, |g t| ≤ C) :
    Tendsto (fun t : ℝ => g t * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  refine squeeze_zero_norm' (a := fun t : ℝ => C * t ^ ((2:ℝ)/3)) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _)]
    exact mul_le_mul_of_nonneg_right (hg t ht) (Real.rpow_nonneg (le_of_lt ht.1) _)
  · simpa using (tendsto_const_nhds.mul tendsto_rpow_two_thirds_nhdsWithin_zero :
        Tendsto (fun t : ℝ => C * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (C * 0)))

/-- **The potential and kinetc asymptotics of a colliding cluster.** -/
theorem clusterPotential_asymptotic_of_isolated {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) ∧
      Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / t ^ ((1:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)) ∧
      Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)) ∧
      Tendsto (fun t : ℝ => clusterRelKinetic m k (deriv x t) * t ^ ((2:ℝ)/3))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) := by
  classical
  obtain ⟨κ, hκpos, hIn, hDer, hSec, _hSecSqrt⟩ :=
    clusterInertia_asymptotics_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  obtain ⟨i0, hi0⟩ : k.Nonempty := Finset.card_pos.mp (by omega)
  -- the Lagrange–Jacobi identity at each `t`
  have hLJ : ∀ t ∈ Ioo (0:ℝ) ε,
      deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
          + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
    intro t ht
    refine deriv_deriv_clusterInertia_curve_eq hm ⟨i0, hi0⟩ (hnc t ht) ?_ (hd2 t ht) (hode t ht)
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  -- the two bounded terms
  have hEbound : ∀ t ∈ Ioo (0:ℝ) ε,
      |4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * crossWork m k (x t) (cmRel m k (x t))|
        ≤ 6 * C := by
    intro t ht
    have h1 := abs_le.mp (hE t ht)
    have h2 := abs_le.mp (hW t ht)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hEbound2 : ∀ t ∈ Ioo (0:ℝ) ε,
      |2 * clusterRelEnergy m k (x t) (deriv x t) + 2 * crossWork m k (x t) (cmRel m k (x t))|
        ≤ 4 * C := by
    intro t ht
    have h1 := abs_le.mp (hE t ht)
    have h2 := abs_le.mp (hW t ht)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hz1 : Tendsto
      (fun t : ℝ => (4 * clusterRelEnergy m k (x t) (deriv x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t))) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_mul_rpow_two_thirds_zero_of_bounded hε (by positivity) hEbound
  have hz2 : Tendsto
      (fun t : ℝ => (2 * clusterRelEnergy m k (x t) (deriv x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t))) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_mul_rpow_two_thirds_zero_of_bounded hε (by positivity) hEbound2
  -- `2 U_k t^{2/3} → (4/9) κ`
  have h2U : Tendsto (fun t : ℝ => 2 * clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) := by
    have hsub := hSec.sub hz1
    rw [sub_zero] at hsub
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    rw [hLJ t ht]; ring
  have hU : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)) := by
    have hhalf := h2U.mul_const (1/2)
    rw [show ((4:ℝ)/9 * κ) * (1/2) = (2:ℝ)/9 * κ by ring] at hhalf
    refine Filter.Tendsto.congr' ?_ hhalf
    filter_upwards with t
    ring
  -- `R_k t^{2/3} → (4/9) κ`
  have hR : Tendsto (fun t : ℝ => clusterRelKinetic m k (deriv x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) := by
    have hsub := hSec.sub hz2
    rw [sub_zero] at hsub
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    rw [hLJ t ht]
    simp only [clusterRelEnergy]
    ring
  exact ⟨κ, hκpos, hIn, hDer, hSec, hU, hR⟩

end Submission.NBody
