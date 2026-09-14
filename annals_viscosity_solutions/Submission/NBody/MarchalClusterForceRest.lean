import Submission.NBody.MarchalClusterShapeSecondDeriv
import Submission.NBody.ClusterShapePotential

/-!
# The remainder in the identity `cmRel (∇U x) = I_k⁻¹ • clusterGrad s + B`

For `i ∈ k` the (mass-weighted) gradient of the full potential splits as

    `(∇_[m]U x)ᵢ = (clusterGrad m k x)ᵢ + clusterExtForce m k x i`

(`ClusterGradSplit`), and the internal part is `I_k⁻¹` times the mass-gradient of the *normalised*
configuration `s = I_k^{-1/2} (x - x_{cm})` (`ClusterCentralConfig`).  Hence

    `cmRel m k (∇_[m]U x) = I_k⁻¹ • clusterGrad m k s + R`,

where the remainder `R` collects the exterior forces and the centre-of-mass motion of the
gradient — both of which are bounded on a cluster which is `ν`-separated from the outside bodies.
The boundedness of `R` is what makes the equation of motion of the normalised configuration
survive the blow-up limit `t → 0⁺` (Ferrario–Terracini, `propo:cent_conf`).

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

/-- The remainder in the identity `cmRel (∇U x) = I⁻¹ • clusterGrad s + R`. -/
noncomputable def clusterForceRest (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : EN E N :=
  cmRel m k (∇_[m] (U m) x) - (clusterInertia m k x)⁻¹ • clusterGrad m k (clusterShape m k x)

/-- Collision-freeness inside the cluster is inherited by `cmRel`. -/
lemma cmRel_pair_ne {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) :
    ∀ i ∈ k, ∀ j ∈ k, i ≠ j → (cmRel m k x) i ≠ (cmRel m k x) j := by
  intro a ha b hb hab hcon
  rw [cmRel_apply_of_mem ha, cmRel_apply_of_mem hb] at hcon
  exact hkk a ha b hb hab (by
    have h2 := congrArg (fun w : E => w + clusterCM m k x) hcon
    simpa using h2)

/-- **The mass-gradient of the cluster potential in terms of the normalised configuration.** -/
lemma clusterGrad_eq_inv_smul_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j)
    (hI : 0 < clusterInertia m k x) :
    clusterGrad m k x = (clusterInertia m k x)⁻¹ • clusterGrad m k (clusterShape m k x) := by
  have hφpos : 0 < Real.sqrt (clusterInertia m k x) := Real.sqrt_pos.mpr hI
  have hcm : cmRel m k x = Real.sqrt (clusterInertia m k x) • clusterShape m k x :=
    cmRel_eq_sqrt_smul_clusterShape hI
  have hkk' := cmRel_pair_ne (m := m) (k := k) hkk
  have hkk'' : ∀ i ∈ k, ∀ j ∈ k, i ≠ j →
      (clusterShape m k x) i ≠ (clusterShape m k x) j := by
    intro a ha b hb hab hcon
    have h3 : (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x) a
        = (Real.sqrt (clusterInertia m k x))⁻¹ • (cmRel m k x) b := by
      rw [← clusterShape_apply, ← clusterShape_apply]
      exact hcon
    have h4 : (cmRel m k x) a = (cmRel m k x) b := by
      have := congrArg (fun w : E => Real.sqrt (clusterInertia m k x) • w) h3
      simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hφpos)] using this
    exact hkk' a ha b hb hab h4
  rw [← clusterGrad_cmRel (m := m) (k := k) hm hkk, hcm,
    clusterGrad_smul hφpos hm (clusterShape m k x) hkk'']
  congr 1
  rw [Real.sq_sqrt hI.le]

/-- **The mass-gradient of the cluster potential at the normalised configuration.** -/
lemma clusterGrad_clusterShape_eq_smul {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j)
    (hI : 0 < clusterInertia m k x) :
    clusterGrad m k (clusterShape m k x) = clusterInertia m k x • clusterGrad m k x := by
  have h := clusterGrad_eq_inv_smul_clusterShape (m := m) (k := k) (x := x) hm hkk hI
  rw [h, smul_smul, mul_inv_cancel₀ (ne_of_gt hI), one_smul]

lemma clusterForceRest_apply_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hnc : WithoutCollisions x) (hI : 0 < clusterInertia m k x)
    {i : Fin N} (hi : i ∈ k) :
    clusterForceRest m k x i = clusterExtForce m k x i - clusterCM m k (∇_[m] (U m) x) := by
  have hkk : ∀ a ∈ k, ∀ b ∈ k, a ≠ b → x a ≠ x b := fun a _ b _ hab hcon =>
    hnc a b hab (by rw [r_eq_norm_sub, hcon, sub_self, norm_zero])
  have hgrads := clusterGrad_clusterShape_eq_smul (m := m) (k := k) (x := x) hm hkk hI
  show (cmRel m k (∇_[m] (U m) x)) i
      - ((clusterInertia m k x)⁻¹ • clusterGrad m k (clusterShape m k x)) i = _
  rw [cmRel_apply_of_mem hi, hgrads]
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hI), one_smul]
  rw [weightedGrad_U_eq_clusterGrad_add_ext hm hnc hi]
  abel

lemma clusterForceRest_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j)
    (hI : 0 < clusterInertia m k x) {i : Fin N} (hi : i ∉ k) :
    clusterForceRest m k x i = 0 := by
  have hgrads := clusterGrad_clusterShape_eq_smul (m := m) (k := k) (x := x) hm hkk hI
  show (cmRel m k (∇_[m] (U m) x)) i
      - ((clusterInertia m k x)⁻¹ • clusterGrad m k (clusterShape m k x)) i = _
  rw [cmRel_apply_of_notMem hi, hgrads]
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hI), one_smul,
    clusterGrad_apply_of_notMem hkk hi, sub_zero]

/-- **The remainder is bounded.**  For a cluster which is `ν`-separated from the outside bodies and
collision-free, the remainder of the force identity is bounded by the exterior-force bound plus the
bound on the centre-of-mass motion of the gradient. -/
lemma norm_clusterForceRest_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hk2 : 2 ≤ k.card) (hsep : ClusterSeparatedWeak k x ν)
    (hnc : WithoutCollisions x) :
    ‖clusterForceRest m k x‖
      ≤ Real.sqrt (k.card : ℝ) * ((∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m j) / ν ^ 2
        + (clusterMass m k)⁻¹
            * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m i * m j) * (ν⁻¹) ^ 2)) := by
  have hI : 0 < clusterInertia m k x := clusterInertia_pos hm hk2 hnc
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  have hkk : ∀ a ∈ k, ∀ b ∈ k, a ≠ b → x a ≠ x b := fun a _ b _ hab hcon =>
    hnc a b hab (by rw [r_eq_norm_sub, hcon, sub_self, norm_zero])
  set Ce : ℝ := (∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m j) / ν ^ 2 with hCe
  set Cc : ℝ := (clusterMass m k)⁻¹
    * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m i * m j) * (ν⁻¹) ^ 2) with hCc
  have hCe0 : 0 ≤ Ce := by
    rw [hCe]
    exact div_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (by positivity)
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]
    exact mul_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))
      (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le) (by positivity))
  have hpt : ∀ i : Fin N, ‖(clusterForceRest m k x) i‖ ≤ Ce + Cc := by
    intro i
    by_cases hi : i ∈ k
    · rw [clusterForceRest_apply_of_mem hmne hnc hI hi]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
      · rw [hCe]; exact norm_clusterExtForce_le (fun i => (hm i).le) hν hsep hi
      · rw [hCc]
        exact norm_clusterCM_weightedGrad_le hm hν hsep hnc
    · rw [clusterForceRest_apply_of_notMem hmne hkk hI hi, norm_zero]
      linarith [hCe0, hCc0]
  have hsum : ∑ i : Fin N, ‖(clusterForceRest m k x) i‖ ^ 2 ≤ (k.card : ℝ) * (Ce + Cc) ^ 2 := by
    have hsplit : ∑ i : Fin N, ‖(clusterForceRest m k x) i‖ ^ 2
        = ∑ i ∈ k, ‖(clusterForceRest m k x) i‖ ^ 2 := by
      refine (Finset.sum_subset (Finset.subset_univ k) ?_).symm
      intro i _ hi
      rw [clusterForceRest_apply_of_notMem hmne hkk hI hi, norm_zero]
      ring
    rw [hsplit]
    calc ∑ i ∈ k, ‖(clusterForceRest m k x) i‖ ^ 2
        ≤ ∑ i ∈ k, (Ce + Cc) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (hpt i) 2
      _ = (k.card : ℝ) * (Ce + Cc) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : ‖clusterForceRest m k x‖ ≤ Real.sqrt ((k.card : ℝ) * (Ce + Cc) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (clusterForceRest m k x))]
    exact Real.sqrt_le_sqrt (by rw [PiLp.norm_sq_eq_of_L2]; exact hsum)
  rw [Real.sqrt_mul (Nat.cast_nonneg k.card)] at h1
  rw [Real.sqrt_sq (by linarith [hCe0, hCc0])] at h1
  rw [hCe, hCc] at h1
  exact h1

/-- **The remainder vanishes in the blow-up limit.**  `t^{4/3} • R → 0`. -/
theorem tendsto_rpow_four_thirds_clusterForceRest {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε ν : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hν : 0 < ν)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν) :
    Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3) • clusterForceRest m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  set Cf : ℝ := Real.sqrt (k.card : ℝ) * ((∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m j) / ν ^ 2
    + (clusterMass m k)⁻¹
        * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m i * m j) * (ν⁻¹) ^ 2)) with hCf
  have hCf0 : 0 ≤ Cf := by
    rw [hCf]
    refine mul_nonneg (Real.sqrt_nonneg _) (add_nonneg ?_ ?_)
    · exact div_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (by positivity)
    · exact mul_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))
        (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hm i).le (hm j).le) (by positivity))
  have hb : ∀ t ∈ Ioo (0:ℝ) ε, ‖clusterForceRest m k (x t)‖ ≤ Cf := by
    intro t ht
    rw [hCf]
    exact norm_clusterForceRest_le hm hν hk2 (hsep t ht) (hnc t ht)
  have hlim : Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    Filter.Tendsto.rpow_const_nhds_zero (tendsto_id.mono_left nhdsWithin_le_nhds) (by norm_num)
  have h2 : Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3) * ‖clusterForceRest m k (x t)‖)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    squeeze_zero_norm' (a := fun t : ℝ => t ^ ((4:ℝ)/3) * Cf) (by
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _),
        abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hb t ht) (Real.rpow_nonneg (le_of_lt ht.1) _)) (by
      simpa using hlim.mul_const Cf)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _)]

end Submission.NBody
