import Submission.NBody.MarchalSeqShape
import Submission.NBody.MarchalSeqBlowUp
import Submission.NBody.MarchalSeqDeriv
import Submission.NBody.MarchalPairRatio
import Submission.NBody.MarchalBumpSign
import Submission.NBody.MarchalStdVarGeometry
import Submission.NBody.MarchalGeometricData
import Submission.NBody.MarchalClusterAsymptotic3

/-!
# The data of the sequential blow-up

Uniform-in-`t` two-sided bounds for the rescaled pair separations `‖q^{λ_n}_i(t) - q^{λ_n}_j(t)‖`,
the direction control (the rescaled pair differences are eventually not parallel to the good
displacement `δ`), and the pair lower bound for the *bumped* configuration
`q^{λ_n} + stdVar δ T t`.

Two structural remarks make this chapter cheaper than the filter version of the same statements:

* the **lower** bound on each pair separation follows from the *upper* bound on the cluster
  potential `U_k(q^{λ_n}(t)) ≤ Cp t^{-2/3}`, which is a *genuine* asymptotic
  (`clusterPotential_asymptotic_of_isolated`) and therefore available along every sequence;
* the **upper** bound follows from the compactness of the shape sphere.

Hence no limit of the normalised configuration is needed for the two-sided pair bounds; only the
direction control uses the uniform (in `t`) form of Ferrario--Terracini's `propo:srcblowup`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]

/-! ## The potential bound and the pair lower bound -/

/-- **The potential bound along the sequence.** -/
theorem seq_potential_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    (hUlim : Tendsto (fun s : ℝ => clusterPotential m k (x s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0))) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t)
        ≤ ((2:ℝ)/9 * κ + 1) * t ^ (-(2:ℝ)/3) := by
  have h := eventually_potential_bound_of_asymptotics (m := m) (k := k) (x := x) (κ := κ)
    (T := T) hκ hT hUlim
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff_ball.mp h
  filter_upwards [eventually_mem_Ioo_of_tendsto_nhdsWithin hηpos hlam] with n hn
  have hmem : lam n ∈ Metric.ball (0:ℝ) η := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hn.1]
    exact hn.2
  intro t ht
  have h2 := hη (lam n) hmem hn.1 t ht
  simpa only [bumpRescaled_zero m k x (lam n)] using h2

/-- The rescaled pair differences are the parabolic rescaling of the centred pair differences. -/
lemma rescaledCentered_sub {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {lam t : ℝ}
    {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) :
    rescaledCentered m k x lam t i - rescaledCentered m k x lam t j
      = lam ^ (-(2:ℝ)/3) • (x (t * lam) i - x (t * lam) j) := by
  have h1 : ∀ i : Fin N, rescaledCentered m k x lam t i
      = lam ^ (-(2:ℝ)/3) • (cmRel m k (x (t * lam)) i) := by
    intro i
    rw [rescaledCentered, PiLp.smul_apply (fun _ : Fin N => E)]
  rw [h1, h1, ← smul_sub, cmRel_sub_of_mem _ hi hj]

/-- **The pair lower bound**, one pair at a time, from the potential bound. -/
theorem seq_pair_lower_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε T Cp : ℝ} (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hT : 0 < T) (hCp : 0 < Cp)
    (hwc : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u))
    {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) {lam : ℕ → ℝ}
    (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hU : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t) ≤ Cp * t ^ (-(2:ℝ)/3)) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      (m i * m j / Cp) * t ^ ((2:ℝ)/3)
        ≤ ‖rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j‖ := by
  filter_upwards [hU, eventually_mem_Ioo_of_tendsto_nhdsWithin
    (show 0 < ε / T from div_pos hε hT) hlam] with n hn hlamn
  intro t ht
  set A : E := rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j with hA
  have hAA : A = rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j := hA
  have ht0 : 0 < t := ht.1
  have hlam0 : 0 < lam n := hlamn.1
  have hlt : t * lam n < ε := by
    have h1 : t * lam n ≤ T * lam n := mul_le_mul_of_nonneg_right ht.2 hlam0.le
    have h2 : T * lam n < T * (ε / T) := mul_lt_mul_of_pos_left hlamn.2 hT
    have h3 : T * (ε / T) = ε := by field_simp
    linarith
  have hu : t * lam n ∈ Ioo (0:ℝ) ε := ⟨mul_pos ht0 hlam0, hlt⟩
  have hne : x (t * lam n) i ≠ x (t * lam n) j :=
    ne_of_r_ne_zero (hwc (t * lam n) hu i j hij)
  have hsub : x (t * lam n) i - x (t * lam n) j ≠ 0 := sub_ne_zero.mpr hne
  have hAne : A ≠ 0 := by
    rw [hA, rescaledCentered_sub hi hj]
    exact smul_ne_zero (by
      rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hlam0.le]
      exact inv_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hlam0 _))) hsub
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hAne
  have hinv : (‖A‖)⁻¹ = 1 / ‖A‖ := inv_eq_one_div _
  have h1 : m i * m j * (‖A‖)⁻¹ ≤ clusterPotential m k (rescaledCentered m k x (lam n) t) := by
    have h := mul_mul_inv_r_le_clusterPotential (fun a => (hm a).le) (s :=
      rescaledCentered m k x (lam n) t) hi hj hij
    rw [r_eq_norm_sub] at h
    simpa only [hAA] using h
  have h2 := hn t ht
  have h3 : (0:ℝ) < Cp * t ^ (-(2:ℝ)/3) := mul_pos hCp (Real.rpow_pos_of_pos ht0 _)
  have h4 : m i * m j / ‖A‖ ≤ Cp * t ^ (-(2:ℝ)/3) := by
    rw [div_eq_mul_inv]
    exact h1.trans h2
  have h5 : m i * m j ≤ (Cp * t ^ (-(2:ℝ)/3)) * ‖A‖ := by
    rw [div_le_iff₀ hAnorm] at h4
    linarith
  have h6 : t ^ (-(2:ℝ)/3) = (t ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg ht0.le]
  have hkey : (m i * m j / Cp) * t ^ ((2:ℝ)/3) = m i * m j / (Cp * t ^ (-(2:ℝ)/3)) := by
    rw [h6, inv_eq_one_div]
    field_simp
  rw [hkey, div_le_iff₀ h3]
  linarith [h5]

/-! ## The pair upper bound -/

/-- **The pair upper bound**, from the compactness of the shape sphere. -/
theorem seq_pair_upper_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {κ ε T : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hκ : 0 < κ) (hε : 0 < ε) (hT : 0 < T)
    (hnc : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, ∀ i ∈ k, ∀ j ∈ k,
      ‖rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j‖
        ≤ C * t ^ ((2:ℝ)/3) := by
  classical
  have hK : k.Nonempty := Finset.card_pos.mp (by omega)
  have hmk : clusterMass m k ≠ 0 := ne_of_gt (clusterMass_pos hm hK)
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hδ₀⟩ : ∃ δ > 0, δ ≤ ε ∧ ∀ u ∈ Ioo (0:ℝ) δ,
      Real.sqrt (clusterInertia m k (x u) / u ^ ((4:ℝ)/3)) ≤ Real.sqrt κ + 1 := by
    have hc : Tendsto (fun s : ℝ => Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hIn
    have h := hc.eventually (eventually_lt_nhds
      (show Real.sqrt κ < Real.sqrt κ + 1 by linarith [Real.sqrt_nonneg κ]))
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp h
    refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, fun u hu => ?_⟩
    have hb : u ∈ Metric.ball (0:ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
      exact lt_of_lt_of_le hu.2 (min_le_left _ _)
    exact (hδ u hb hu.1).le
  set Cm : ℝ := ∑ i ∈ k, Real.sqrt ((m i)⁻¹) with hCm
  have hCmpos : 0 < Cm := Finset.sum_pos (fun i _ => Real.sqrt_pos.mpr (inv_pos.mpr (hm i))) hK
  refine ⟨(Real.sqrt κ + 1) * (2 * Cm), by positivity, ?_⟩
  filter_upwards [eventually_mem_Ioo_of_tendsto_nhdsWithin
    (show 0 < δ₀ / T from div_pos hδ₀pos hT) hlam] with n hn
  intro t ht i hi j hj
  have hlam0 : 0 < lam n := hn.1
  have hlt : t * lam n < δ₀ := by
    have h1 : t * lam n ≤ T * lam n := mul_le_mul_of_nonneg_right ht.2 hlam0.le
    have h2 : T * lam n < T * (δ₀ / T) := mul_lt_mul_of_pos_left hn.2 hT
    have h3 : T * (δ₀ / T) = δ₀ := by field_simp
    linarith
  have hltε : t * lam n < ε := lt_of_lt_of_le hlt hδ₀le
  have hu : t * lam n ∈ Ioo (0:ℝ) δ₀ := ⟨mul_pos ht.1 hlam0, hlt⟩
  have hI : 0 < clusterInertia m k (x (t * lam n)) :=
    clusterInertia_pos hm hk2 (hnc _ ⟨hu.1, hltε⟩)
  have hshapeI : clusterInertia m k (clusterShape m k (x (t * lam n))) = 1 :=
    clusterInertia_clusterShape hmk hI
  have hcm : clusterCM m k (clusterShape m k (x (t * lam n))) = 0 :=
    clusterCM_clusterShape hmk
  have hnorm_s : ∀ a : Fin N, ‖clusterShape m k (x (t * lam n)) a
      - clusterCM m k (clusterShape m k (x (t * lam n)))‖ ^ 2 ≤ (m a)⁻¹ := by
    intro a
    by_cases ha : a ∈ k
    · have hle : m a * ‖clusterShape m k (x (t * lam n)) a
          - clusterCM m k (clusterShape m k (x (t * lam n)))‖ ^ 2
          ≤ ∑ l ∈ k, m l * ‖clusterShape m k (x (t * lam n)) l
              - clusterCM m k (clusterShape m k (x (t * lam n)))‖ ^ 2 :=
        Finset.single_le_sum (f := fun l => m l * ‖clusterShape m k (x (t * lam n)) l
          - clusterCM m k (clusterShape m k (x (t * lam n)))‖ ^ 2)
          (fun l _ => mul_nonneg (hm l).le (sq_nonneg _)) ha
      rw [← clusterInertia, hshapeI] at hle
      rw [inv_eq_one_div, le_div_iff₀ (hm a)]
      linarith [hle]
    · have h0 : clusterShape m k (x (t * lam n)) a = 0 := clusterShape_apply_of_notMem ha
      rw [h0, zero_sub, norm_neg, hcm, norm_zero]
      simpa using inv_nonneg.mpr (hm a).le
  have hs_bound : ‖clusterShape m k (x (t * lam n)) i
      - clusterShape m k (x (t * lam n)) j‖ ≤ 2 * Cm := by
    have h1 : clusterShape m k (x (t * lam n)) i - clusterShape m k (x (t * lam n)) j
        = (clusterShape m k (x (t * lam n)) i
            - clusterCM m k (clusterShape m k (x (t * lam n))))
          - (clusterShape m k (x (t * lam n)) j
              - clusterCM m k (clusterShape m k (x (t * lam n)))) := by
      rw [hcm]; abel
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    have hi' : Real.sqrt ((m i)⁻¹) ≤ Cm :=
      Finset.single_le_sum (f := fun l => Real.sqrt ((m l)⁻¹))
        (fun l _ => Real.sqrt_nonneg _) hi
    have hj' : Real.sqrt ((m j)⁻¹) ≤ Cm :=
      Finset.single_le_sum (f := fun l => Real.sqrt ((m l)⁻¹))
        (fun l _ => Real.sqrt_nonneg _) hj
    have hni : ‖clusterShape m k (x (t * lam n)) i
        - clusterCM m k (clusterShape m k (x (t * lam n)))‖ ≤ Real.sqrt ((m i)⁻¹) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hnorm_s i)
    have hnj : ‖clusterShape m k (x (t * lam n)) j
        - clusterCM m k (clusterShape m k (x (t * lam n)))‖ ≤ Real.sqrt ((m j)⁻¹) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hnorm_s j)
    linarith
  have hroot : Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3))
      ≤ Real.sqrt κ + 1 := hδ₀ (t * lam n) hu
  have hcm_rel : x (t * lam n) i - x (t * lam n) j
      = Real.sqrt (clusterInertia m k (x (t * lam n)))
        • (clusterShape m k (x (t * lam n)) i - clusterShape m k (x (t * lam n)) j) := by
    rw [← cmRel_sub_of_mem (x (t * lam n)) hi hj]
    rw [cmRel_eq_sqrt_smul_clusterShape hI]
    simp only [PiLp.smul_apply, smul_sub]
  have hsqu : Real.sqrt (clusterInertia m k (x (t * lam n)))
      = Real.sqrt ((t * lam n) ^ ((4:ℝ)/3))
        * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)) := by
    have hne : (t * lam n) ^ ((4:ℝ)/3) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (mul_pos ht.1 hlam0) _)
    rw [← Real.sqrt_mul (Real.rpow_nonneg (mul_pos ht.1 hlam0).le _)]
    congr 1
    field_simp
  have hroot4 : Real.sqrt ((t * lam n) ^ ((4:ℝ)/3))
      = lam n ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
    have h3 : Real.sqrt ((t * lam n) ^ ((4:ℝ)/3)) = (t * lam n) ^ ((2:ℝ)/3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt (mul_pos ht.1 hlam0))]
      norm_num
    rw [h3, Real.mul_rpow ht.1.le hlam0.le, mul_comm]
  have hneg : lam n ^ (-(2:ℝ)/3) = (lam n ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hlam0.le]
  have hscal : lam n ^ (-(2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n)))
      = t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n))
          / (t * lam n) ^ ((4:ℝ)/3)) := by
    rw [hsqu, hroot4, hneg]
    have hne : lam n ^ ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam0 _)
    field_simp
  have hnorm : ‖rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j‖
      = t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3))
        * ‖clusterShape m k (x (t * lam n)) i - clusterShape m k (x (t * lam n)) j‖ := by
    rw [rescaledCentered_sub hi hj, hcm_rel, smul_smul, norm_smul, Real.norm_eq_abs]
    have hpos : 0 < lam n ^ (-(2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n))) :=
      mul_pos (Real.rpow_pos_of_pos hlam0 _) (Real.sqrt_pos.mpr hI)
    rw [abs_of_pos hpos, hscal]
  rw [hnorm]
  have ht3 : 0 ≤ t ^ ((2:ℝ)/3) := Real.rpow_nonneg ht.1.le _
  have hrootnn : 0 ≤ Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)) :=
    Real.sqrt_nonneg _
  calc t ^ ((2:ℝ)/3)
        * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3))
        * ‖clusterShape m k (x (t * lam n)) i - clusterShape m k (x (t * lam n)) j‖
      ≤ t ^ ((2:ℝ)/3) * (Real.sqrt κ + 1) * (2 * Cm) := by
        refine mul_le_mul ?_ hs_bound (norm_nonneg _) ?_
        · exact mul_le_mul_of_nonneg_left hroot ht3
        · positivity
    _ = (Real.sqrt κ + 1) * (2 * Cm) * t ^ ((2:ℝ)/3) := by ring

/-! ## Direction control -/

/-- The orthogonal component of `u` to `δ` is positive when `u` is not parallel to `δ`. -/
lemma norm_sub_proj_pos {u δ : E} (hδ : δ ≠ 0)
    (hgood : (inner ℝ u δ) ^ 2 < ‖u‖ ^ 2 * ‖δ‖ ^ 2) :
    0 < ‖u - (inner ℝ u ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ := by
  have hd : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hunit : ‖(‖δ‖)⁻¹ • δ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ (ne_of_gt hd)]
  have hsq : ‖u - (inner ℝ u ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ ^ 2
      = ‖u‖ ^ 2 - (inner ℝ u ((‖δ‖)⁻¹ • δ)) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hunit, mul_one,
      Real.norm_eq_abs, sq_abs]
    ring
  have hinner : inner ℝ u ((‖δ‖)⁻¹ • δ) = (‖δ‖)⁻¹ * inner ℝ u δ :=
    real_inner_smul_right u δ (‖δ‖)⁻¹
  have hkey : ‖u‖ ^ 2 - (inner ℝ u ((‖δ‖)⁻¹ • δ)) ^ 2
      = (‖u‖ ^ 2 * ‖δ‖ ^ 2 - (inner ℝ u δ) ^ 2) / ‖δ‖ ^ 2 := by
    rw [hinner]
    field_simp
  have hpos : 0 < (‖u‖ ^ 2 * ‖δ‖ ^ 2 - (inner ℝ u δ) ^ 2) / ‖δ‖ ^ 2 := by
    refine div_pos ?_ (by positivity)
    linarith [hgood]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, hkey]
  exact Real.sqrt_pos.mpr hpos

/-- **Direction control for the blown-up pair differences, uniform on `[t₁,T]`.** -/
theorem seq_shape_orthogonal_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {T t₁ : ℝ} {sbar : EN E N} {i₀ j : Fin N} {δ : E} (hδ : δ ≠ 0)
    (ht₁ : 0 < t₁) (ht₁T : t₁ ≤ T) (hi₀ : i₀ ∈ k) (hj : j ∈ k) (hji : j ≠ i₀)
    {lam : ℕ → ℝ}
    (hG : ∀ η > (0:ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (x (t * lam n)) - sbar‖ < η)
    (hgood : (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      a ≤ ‖(clusterShape m k (x (t * lam n)) i₀ - clusterShape m k (x (t * lam n)) j)
        - (inner ℝ (clusterShape m k (x (t * lam n)) i₀ - clusterShape m k (x (t * lam n)) j)
              ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ := by
  classical
  set u₀ : E := sbar i₀ - sbar j with hu₀
  set δ' : E := (‖δ‖)⁻¹ • δ with hδ'
  have hd : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hunit : ‖δ'‖ = 1 := by
    rw [hδ', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd),
      inv_mul_cancel₀ (ne_of_gt hd)]
  have ha₀pos : 0 < ‖u₀ - (inner ℝ u₀ δ') • δ'‖ := by
    refine norm_sub_proj_pos (u := u₀) hδ ?_
    exact hgood
  refine ⟨‖u₀ - (inner ℝ u₀ δ') • δ'‖ / 2, by positivity, ?_⟩
  have hGn := hG (‖u₀ - (inner ℝ u₀ δ') • δ'‖ / 8) (by positivity)
  filter_upwards [hGn] with n hn
  intro t ht
  set u : E := clusterShape m k (x (t * lam n)) i₀ - clusterShape m k (x (t * lam n)) j with hu
  set w : E := (clusterShape m k (x (t * lam n)) - sbar) i₀
    - (clusterShape m k (x (t * lam n)) - sbar) j with hw
  have hu_eq : u = u₀ + w := by
    rw [hu, hu₀, hw]
    simp only [PiLp.sub_apply]
    abel
  have hwnorm : ‖w‖ < 2 * (‖u₀ - (inner ℝ u₀ δ') • δ'‖ / 8) := by
    have h1 : ‖(clusterShape m k (x (t * lam n)) - sbar) i₀‖
        < ‖u₀ - (inner ℝ u₀ δ') • δ'‖ / 8 :=
      (norm_apply_le_norm (clusterShape m k (x (t * lam n)) - sbar) i₀).trans_lt (hn t ht)
    have h2 : ‖(clusterShape m k (x (t * lam n)) - sbar) j‖
        < ‖u₀ - (inner ℝ u₀ δ') • δ'‖ / 8 :=
      (norm_apply_le_norm (clusterShape m k (x (t * lam n)) - sbar) j).trans_lt (hn t ht)
    rw [hw]
    refine (norm_sub_le _ _).trans_lt ?_
    linarith
  have hproj_le : ‖(inner ℝ w δ') • δ'‖ ≤ ‖w‖ := by
    rw [norm_smul, hunit, mul_one, Real.norm_eq_abs]
    simpa only [hunit, mul_one] using abs_real_inner_le_norm w δ'
  have hsplit : u - (inner ℝ u δ') • δ'
      = (u₀ - (inner ℝ u₀ δ') • δ') + (w - (inner ℝ w δ') • δ') := by
    rw [hu_eq]
    simp only [inner_add_left, add_smul]
    abel
  have hmain : ‖u₀ - (inner ℝ u₀ δ') • δ'‖
      - (‖w‖ + ‖w‖) ≤ ‖u - (inner ℝ u δ') • δ'‖ := by
    have h3 : ‖w - (inner ℝ w δ') • δ'‖ ≤ ‖w‖ + ‖w‖ := by
      refine (norm_sub_le _ _).trans ?_
      linarith [hproj_le]
    have h5 : ‖u₀ - (inner ℝ u₀ δ') • δ'‖
        ≤ ‖(u₀ - (inner ℝ u₀ δ') • δ') + (w - (inner ℝ w δ') • δ')‖
          + ‖w - (inner ℝ w δ') • δ'‖ := by
      have h := norm_sub_le ((u₀ - (inner ℝ u₀ δ') • δ') + (w - (inner ℝ w δ') • δ'))
        (w - (inner ℝ w δ') • δ')
      rwa [add_sub_cancel_right] at h
    rw [hsplit]
    linarith [h5, h3]
  have hδ'ne : δ' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hunit
    exact one_ne_zero hunit.symm
  rw [hu, hδ'] at hmain ⊢
  refine le_trans ?_ hmain
  linarith [ha₀pos, hwnorm]

/-- The rescaled pair difference is a positive multiple of the normalised pair difference. -/
lemma rescaledCentered_sub_eq_smul_shape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {lam t : ℝ} {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (ht : 0 < t) (hlam : 0 < lam)
    (hI : 0 < clusterInertia m k (x (t * lam))) :
    rescaledCentered m k x lam t i - rescaledCentered m k x lam t j
      = (t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)))
        • (clusterShape m k (x (t * lam)) i - clusterShape m k (x (t * lam)) j) := by
  have hcm_rel : x (t * lam) i - x (t * lam) j
      = Real.sqrt (clusterInertia m k (x (t * lam)))
        • (clusterShape m k (x (t * lam)) i - clusterShape m k (x (t * lam)) j) := by
    rw [← cmRel_sub_of_mem (x (t * lam)) hi hj]
    rw [cmRel_eq_sqrt_smul_clusterShape hI]
    simp only [PiLp.smul_apply, smul_sub]
  have hsqu : Real.sqrt (clusterInertia m k (x (t * lam)))
      = Real.sqrt ((t * lam) ^ ((4:ℝ)/3))
        * Real.sqrt (clusterInertia m k (x (t * lam)) / (t * lam) ^ ((4:ℝ)/3)) := by
    have hne : (t * lam) ^ ((4:ℝ)/3) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (mul_pos ht hlam) _)
    rw [← Real.sqrt_mul (Real.rpow_nonneg (mul_pos ht hlam).le _)]
    congr 1
    field_simp
  have hroot4 : Real.sqrt ((t * lam) ^ ((4:ℝ)/3)) = lam ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
    have h3 : Real.sqrt ((t * lam) ^ ((4:ℝ)/3)) = (t * lam) ^ ((2:ℝ)/3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt (mul_pos ht hlam))]
      norm_num
    rw [h3, Real.mul_rpow ht.le hlam.le, mul_comm]
  have hneg : lam ^ (-(2:ℝ)/3) = (lam ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hlam.le]
  have hscal : lam ^ (-(2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam)))
      = t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam))
          / (t * lam) ^ ((4:ℝ)/3)) := by
    rw [hsqu, hroot4, hneg]
    field_simp
  rw [rescaledCentered_sub hi hj, hcm_rel, smul_smul, hscal]

/-- **The rescaled pair difference is quantitatively non-parallel to `δ` on `[t₁,T]`.** -/
theorem seq_pair_orthogonal_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {κ ε T t₁ : ℝ} {sbar : EN E N} {i₀ j : Fin N} {δ : E} (hδ : δ ≠ 0) (hκ : 0 < κ)
    (hε : 0 < ε) (hT : 0 < T) (ht₁ : 0 < t₁) (ht₁T : t₁ ≤ T)
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (hi₀ : i₀ ∈ k) (hj : j ∈ k) (hji : j ≠ i₀)
    (hnc : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hG : ∀ η > (0:ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (x (t * lam n)) - sbar‖ < η)
    (hgood : (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      c * t ^ ((2:ℝ)/3) ≤ ‖(rescaledCentered m k x (lam n) t i₀
          - rescaledCentered m k x (lam n) t j)
        - (inner ℝ (rescaledCentered m k x (lam n) t i₀
              - rescaledCentered m k x (lam n) t j) ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ := by
  obtain ⟨a, hapos, ha⟩ := seq_shape_orthogonal_bound (m := m) (k := k) (x := x) (T := T)
    (t₁ := t₁) (sbar := sbar) (i₀ := i₀) (j := j) (δ := δ) hδ ht₁ ht₁T hi₀ hj hji hG hgood
  -- the root bound `√κ/2 ≤ √(I/(t λ)^{4/3})`
  have hrootlim : Tendsto (fun s : ℝ => Real.sqrt (clusterInertia m k (x s) / s ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hIn
  obtain ⟨η, hηpos, hηle, hη⟩ : ∃ η > 0, η ≤ ε ∧ ∀ u ∈ Ioo (0:ℝ) η,
      Real.sqrt κ / 2 ≤ Real.sqrt (clusterInertia m k (x u) / u ^ ((4:ℝ)/3)) := by
    have h := hrootlim.eventually (eventually_gt_nhds
      (show Real.sqrt κ / 2 < Real.sqrt κ by linarith [Real.sqrt_pos.mpr hκ]))
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff_ball.mp h
    refine ⟨min δ₁ ε, lt_min hδ₁pos hε, min_le_right _ _, fun u hu => ?_⟩
    have hb : u ∈ Metric.ball (0:ℝ) δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
      exact lt_of_lt_of_le hu.2 (min_le_left _ _)
    exact (hδ₁ u hb hu.1).le
  refine ⟨Real.sqrt κ / 2 * a, by positivity, ?_⟩
  filter_upwards [eventually_mem_Ioo_of_tendsto_nhdsWithin
      (show 0 < η / T from div_pos hηpos hT) hlam, ha] with n hlamn hn1
  intro t ht
  have hlam0 : 0 < lam n := hlamn.1
  have hlt : t * lam n < η := by
    have h1 : t * lam n ≤ T * lam n := mul_le_mul_of_nonneg_right ht.2 hlam0.le
    have h2 : T * lam n < T * (η / T) := mul_lt_mul_of_pos_left hlamn.2 hT
    have h3 : T * (η / T) = η := by field_simp
    linarith
  have ht0 : 0 < t := lt_trans ht₁ ht.1
  have hltε : t * lam n < ε := lt_of_lt_of_le hlt hηle
  have hmulpos : 0 < t * lam n := mul_pos ht0 hlam0
  have hI : 0 < clusterInertia m k (x (t * lam n)) :=
    clusterInertia_pos hm hk2 (hnc (t * lam n) ⟨hmulpos, hltε⟩)
  set α : ℝ := t ^ ((2:ℝ)/3)
    * Real.sqrt (clusterInertia m k (x (t * lam n)) / (t * lam n) ^ ((4:ℝ)/3)) with hα
  set u : E := clusterShape m k (x (t * lam n)) i₀ - clusterShape m k (x (t * lam n)) j with hu
  have hαpos : 0 < α := by
    rw [hα]
    exact mul_pos (Real.rpow_pos_of_pos ht0 _)
      (Real.sqrt_pos.mpr (div_pos hI (Real.rpow_pos_of_pos hmulpos _)))
  have hroot : Real.sqrt κ / 2 ≤ Real.sqrt (clusterInertia m k (x (t * lam n))
      / (t * lam n) ^ ((4:ℝ)/3)) := hη (t * lam n) ⟨hmulpos, hlt⟩
  have hscal := rescaledCentered_sub_eq_smul_shape (m := m) (k := k) (x := x)
    (lam := lam n) (t := t) hi₀ hj ht0 hlam0 hI
  have hproj : (inner ℝ (α • u) ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)
      = α • ((inner ℝ u ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)) := by
    rw [real_inner_smul_left]
    simp only [smul_smul, mul_assoc]
  have hgoal : ‖(α • u) - (inner ℝ (α • u) ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖
      = α * ‖u - (inner ℝ u ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ := by
    rw [hproj, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
  have hα' : t ^ ((2:ℝ)/3) * (Real.sqrt κ / 2)
      ≤ t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n))
          / (t * lam n) ^ ((4:ℝ)/3)) :=
    mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg ht0.le _)
  rw [show rescaledCentered m k x (lam n) t i₀ - rescaledCentered m k x (lam n) t j
      = α • u from hscal, hgoal]
  have h1 : Real.sqrt κ / 2 * a * t ^ ((2:ℝ)/3) ≤ α * a := by
    rw [hα]
    have h2 := mul_le_mul_of_nonneg_right hα' hapos.le
    calc Real.sqrt κ / 2 * a * t ^ ((2:ℝ)/3)
        = t ^ ((2:ℝ)/3) * (Real.sqrt κ / 2) * a := by ring
      _ ≤ t ^ ((2:ℝ)/3) * Real.sqrt (clusterInertia m k (x (t * lam n))
            / (t * lam n) ^ ((4:ℝ)/3)) * a := h2
  exact h1.trans (mul_le_mul_of_nonneg_left (hn1 t ht) hαpos.le)

/-- **The pair lower bound with a single constant.**  Derived from `seq_pair_lower_bound` by
bounding `m_i m_j` below by `((∑_{l∈k} (m_l)⁻¹)⁻¹)²`. -/
theorem seq_pair_lower_bound_uniform {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε T Cp : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hT : 0 < T)
    (hCp : 0 < Cp)
    (hwc : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hU : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t) ≤ Cp * t ^ (-(2:ℝ)/3)) :
    ∀ᶠ n in atTop, ∀ i ∈ k, ∀ j ∈ k, i ≠ j → ∀ t ∈ Ioc (0:ℝ) T,
      (((∑ l ∈ k, (m l)⁻¹)⁻¹) ^ 2 / Cp) * t ^ ((2:ℝ)/3)
        ≤ ‖rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j‖ := by
  classical
  have hkn : k.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hk2)
  set c₀ : ℝ := (∑ l ∈ k, (m l)⁻¹)⁻¹ with hc₀
  have hsumpos : (0:ℝ) < ∑ l ∈ k, (m l)⁻¹ :=
    Finset.sum_pos (fun l _ => inv_pos.mpr (hm l)) hkn
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]; exact inv_pos.mpr hsumpos
  have hc₀le : ∀ i ∈ k, c₀ ≤ m i := by
    intro i hi
    have h1 : (m i)⁻¹ ≤ ∑ l ∈ k, (m l)⁻¹ :=
      Finset.single_le_sum (f := fun l => (m l)⁻¹) (fun l _ => (inv_pos.mpr (hm l)).le) hi
    rw [hc₀, inv_le_comm₀ hsumpos (hm i)]
    exact h1
  refine (Finset.eventually_all k).mpr fun i hi => (Finset.eventually_all k).mpr fun j hj => ?_
  by_cases hij : i = j
  · filter_upwards with n hne
    exact absurd hij hne
  · have h := seq_pair_lower_bound (m := m) (k := k) (x := x) (ε := ε) (T := T) (Cp := Cp)
      hm hε hT hCp hwc hi hj hij hlam hU
    filter_upwards [h] with n hn hne t ht
    refine le_trans ?_ (hn t ht)
    have hmul : c₀ ^ 2 ≤ m i * m j := by
      calc c₀ ^ 2 = c₀ * c₀ := sq c₀
        _ ≤ m i * m j := mul_le_mul (hc₀le i hi) (hc₀le j hj) hc₀pos.le (hm i).le
    exact mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hCp).mpr hmul)
      (Real.rpow_nonneg ht.1.le _)

/-- **The velocity bound `hd` along the sequence**, from `eventually_vel_bound_of_asymptotics`. -/
theorem seq_vel_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε C ν Cv T : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hT : 0 < T)
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0))) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (rescaledCentered m k x (lam n)) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := eventually_vel_bound_of_asymptotics (m := m) (k := k) (x := x)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) (T := T) hm hk2 hε hC hν hCv hT hnc hE hW hx hd2 hd3
    hode hsep hv hI
  rw [eventually_nhdsWithin_iff] at hCd
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff_ball.mp hCd
  refine ⟨Cd + 1, by linarith, ?_⟩
  filter_upwards [eventually_mem_Ioo_of_tendsto_nhdsWithin hηpos hlam] with n hn
  have hmem : lam n ∈ Metric.ball (0:ℝ) η := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hn.1]
    exact hn.2
  intro t ht
  have h : ‖deriv (rescaledCentered m k x (lam n)) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3) := by
    simpa only [bumpRescaled_zero m k x (lam n)] using hη (lam n) hmem hn.1 t ht
  have ht3 : 0 ≤ t ^ (-(1:ℝ)/3) := Real.rpow_nonneg ht.1.le _
  calc ‖deriv (rescaledCentered m k x (lam n)) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3) := h
    _ ≤ (Cd + 1) * t ^ (-(1:ℝ)/3) := mul_le_mul_of_nonneg_right (by linarith) ht3

end Submission.NBody
