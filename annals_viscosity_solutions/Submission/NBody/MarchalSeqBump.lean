import Submission.NBody.MarchalSeqData
import Submission.NBody.MarchalBumpedCollision

/-!
# The bumped configuration along the blow-up sequence

The direction `δ` produced by the circle average (`exists_model_dir_two_sided_of_blowup`) is *not*
parallel to any pair separation of either limit shape.  This file proves that under this condition
(and without any sign condition) the bumped configuration `q^{λ_n} + stdVarVec m k i₀ δ T` keeps
every pair of the cluster quantitatively apart,

  `c · t^{2/3} ≤ ‖(q^{λ_n}(t) + f(t))ᵢ - (q^{λ_n}(t) + f(t))ⱼ‖`     (`seq_bumped_pair_lower`),

whence both the potential bound `hp2` of the sequential transfer (`seq_bumped_potential_bound`) and
the absence of collisions inside the cluster (`seq_bumped_noColl`).

The two-region argument: for `t` below the threshold `t₁ = min (T/2) ((‖δ‖/(2Cu))^{3/2})` the
standard variation is *constant* equal to `δ`, so the perturbation dominates the (small) rescaled
separation; above `t₁` the orthogonal component of the rescaled pair separation to `δ` survives,
which is exactly the direction control `seq_pair_orthogonal_bound`.
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

/-! ## Pure algebra -/

/-- The norm of the component of `A` orthogonal to `δ` is `√(‖A‖² - ⟪A,δ⟫²/‖δ‖²)`. -/
lemma norm_sub_proj_eq_sqrt (A : E) {δ : E} (hδ : δ ≠ 0) :
    ‖A - (inner ℝ A ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖
      = Real.sqrt (‖A‖ ^ 2 - (inner ℝ A δ) ^ 2 / ‖δ‖ ^ 2) := by
  have hd : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hunit : ‖(‖δ‖)⁻¹ • δ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ (ne_of_gt hd)]
  have hinner : inner ℝ A ((‖δ‖)⁻¹ • δ) = (‖δ‖)⁻¹ * inner ℝ A δ :=
    real_inner_smul_right A δ (‖δ‖)⁻¹
  have hsq : ‖A - (inner ℝ A ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ ^ 2
      = ‖A‖ ^ 2 - (inner ℝ A δ) ^ 2 / ‖δ‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hunit, mul_one, Real.norm_eq_abs,
      sq_abs, hinner]
    field_simp
    ring
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-- The difference of the bumped configuration through `i₀` is the difference of the configuration
plus the standard variation. -/
lemma stdVarVec_sub_i₀ {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ j : Fin N} {δ : E} (T t : ℝ)
    (hi₀ : i₀ ∈ k) (hj : j ∈ k) (hjne : j ≠ i₀) :
    stdVarVec m k i₀ δ T t i₀ - stdVarVec m k i₀ δ T t j = stdVar δ T t := by
  rw [stdVarVec, PiLp.smul_apply (fun _ : Fin N => E), PiLp.smul_apply (fun _ : Fin N => E),
    ← smul_sub, stdPertVec_sub_i₀ hi₀ hj hjne, stdVar]

/-- The bumped cluster separation through `i₀`. -/
lemma add_stdVarVec_sub_i₀ {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ j : Fin N} {δ : E} (T t : ℝ)
    (hi₀ : i₀ ∈ k) (hj : j ∈ k) (hjne : j ≠ i₀) (q : EN E N) :
    (q + stdVarVec m k i₀ δ T t) i₀ - (q + stdVarVec m k i₀ δ T t) j
      = (q i₀ - q j) + stdVar δ T t := by
  have h := stdVarVec_sub_i₀ (m := m) (k := k) (i₀ := i₀) (j := j) (δ := δ) T t hi₀ hj hjne
  rw [PiLp.add_apply, PiLp.add_apply,
    show q i₀ + (stdVarVec m k i₀ δ T t) i₀ - (q j + (stdVarVec m k i₀ δ T t) j)
      = (q i₀ - q j) + ((stdVarVec m k i₀ δ T t) i₀ - (stdVarVec m k i₀ δ T t) j) from by abel, h]

/-! ## The potential in terms of the pair lower bounds -/

/-- If every pair of a cluster is at distance at least `c t^{2/3}`, the cluster potential is at most
`(∑ mᵢmⱼ/c) t^{-2/3}`. -/
lemma clusterPotential_le_of_pair_lower {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {k : Finset (Fin N)} (y : EN E N) {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hlow : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → c * t ^ ((2:ℝ)/3) ≤ ‖y i - y j‖) :
    clusterPotential m k y ≤ (∑ p ∈ (pairFinset N).filter
        (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k), m p.1 * m p.2 / c)
      * t ^ (-(2:ℝ)/3) := by
  rw [clusterPotential, Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  have hpp : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp1).2
  have hmm : 0 ≤ m p.1 * m p.2 := mul_nonneg (hm _) (hm _)
  have hpos : 0 < c * t ^ ((2:ℝ)/3) := mul_pos hc (Real.rpow_pos_of_pos ht _)
  have hl := hlow p.1 hp2.1 p.2 hp2.2 hpp
  have hlt : 0 < ‖y p.1 - y p.2‖ := lt_of_lt_of_le hpos hl
  rw [r_eq_norm_sub]
  have hstep : m p.1 * m p.2 * (‖y p.1 - y p.2‖)⁻¹
      ≤ m p.1 * m p.2 * (c * t ^ ((2:ℝ)/3))⁻¹ :=
    mul_le_mul_of_nonneg_left ((inv_le_inv₀ hlt hpos).mpr hl) hmm
  refine hstep.trans (le_of_eq ?_)
  rw [mul_inv, show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg ht.le, inv_eq_one_div]
  field_simp

/-- The difference of the bumped configuration, for a pair not involving `i₀`. -/
lemma stdVarVec_sub_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ i j : Fin N} {δ : E}
    (T t : ℝ) (hi : i ∈ k) (hj : j ∈ k) (hii : i ≠ i₀) (hjj : j ≠ i₀) :
    stdVarVec m k i₀ δ T t i - stdVarVec m k i₀ δ T t j = 0 := by
  have h0 := stdPertVec_sub_of_notMem (m := m) (i₀ := i₀) (i := i) (j := j) (v := δ) hi hj hii hjj
  have h : stdPertVec m k i₀ δ i - stdPertVec m k i₀ δ j = 0 := sub_eq_zero.mpr h0
  rw [stdVarVec, PiLp.smul_apply (fun _ : Fin N => E), PiLp.smul_apply (fun _ : Fin N => E),
    ← smul_sub, h, smul_zero]

/-- A configuration all of whose cluster pairs are bounded below is collision free inside the
cluster. -/
lemma clusterNoColl_of_pair_lower {k : Finset (Fin N)} {y : EN E N} {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t)
    (hlow : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → c * t ^ ((2:ℝ)/3) ≤ ‖y i - y j‖) :
    ClusterNoColl k y := by
  intro i hi j hj hij hEq
  have hl := hlow i hi j hj hij
  rw [hEq, sub_self, norm_zero] at hl
  have : (0:ℝ) < c * t ^ ((2:ℝ)/3) := mul_pos hc (Real.rpow_pos_of_pos ht _)
  linarith


/-! ## The bumped pair lower bound -/

/-- **The bumped pair lower bound**, one pair at a time.  For a direction `δ ≠ 0` not parallel to
the limit separation `s̄ i₀ - s̄ j`, the pair `(i₀,j)` of the bumped rescaled configuration is bounded
below by `c t^{2/3}`. -/
theorem seq_bumped_pair_lower_pair {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {κ ε T Cu t₁ : ℝ} {sbar : EN E N} {i₀ j : Fin N} {δ : E}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hδ : δ ≠ 0)
    (hκ : 0 < κ) (hε : 0 < ε) (hT : 0 < T) (hδT : 2 * ‖δ‖ ≤ T)
    (hi₀ : i₀ ∈ k) (hj : j ∈ k) (hji : j ≠ i₀)
    (hnc : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    {Cp : ℝ} (hCp : 0 < Cp) (hCu : 0 < Cu)
    (ht₁ : 0 < t₁) (ht₁T : t₁ ≤ T / 2) (hd₁ : Cu * t₁ ^ ((2:ℝ)/3) ≤ ‖δ‖ / 2)
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hU : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hUp : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, ∀ i ∈ k, ∀ jj ∈ k,
      ‖rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t jj‖
        ≤ Cu * t ^ ((2:ℝ)/3))
    (hG : ∀ η > (0:ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (x (t * lam n)) - sbar‖ < η)
    (hgood : (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      c * t ^ ((2:ℝ)/3)
        ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i₀
            - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖ := by
  have hA := seq_pair_lower_bound_uniform (m := m) (k := k) (x := x)
    (ε := ε) (T := T) (Cp := Cp) hm hk2 hε hT hCp hnc hlam hU
  set cA : ℝ := ((∑ l ∈ k, (m l)⁻¹)⁻¹) ^ 2 / Cp with hcA
  have hkn : k.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hk2)
  have hsumpos : (0:ℝ) < ∑ l ∈ k, (m l)⁻¹ :=
    Finset.sum_pos (fun l _ => inv_pos.mpr (hm l)) hkn
  have hcApos : 0 < cA := by
    rw [hcA]
    exact div_pos (pow_pos (inv_pos.mpr hsumpos) 2) hCp
  obtain ⟨cO, hcOpos, hO⟩ := seq_pair_orthogonal_bound (m := m) (k := k) (x := x)
    (κ := κ) (ε := ε) (T := T) (t₁ := t₁) (sbar := sbar) (i₀ := i₀) (j := j) (δ := δ)
    hδ hκ hε hT ht₁ (by linarith : t₁ ≤ T) hm hk2 hi₀ hj hji hnc hIn hlam hG hgood
  refine ⟨min (min cA cO) Cu, lt_min (lt_min hcApos hcOpos) hCu, ?_⟩
  filter_upwards [hA, hO, hUp] with n hAn hOn hUpn
  intro t ht
  set q : EN E N := rescaledCentered m k x (lam n) t with hq
  set f : EN E N := stdVarVec m k i₀ δ T t with hf
  have hqf : (q + f) i₀ - (q + f) j = (q i₀ - q j) + stdVar δ T t :=
    add_stdVarVec_sub_i₀ T t hi₀ hj hji q
  have hcm : min (min cA cO) Cu ≤ Cu := min_le_right _ _
  have hcmO : min (min cA cO) Cu ≤ cO :=
    le_trans (min_le_left (min cA cO) Cu) (min_le_right cA cO)
  by_cases htle : t ≤ t₁
  · have hAub : ‖q i₀ - q j‖ ≤ Cu * t ^ ((2:ℝ)/3) := hUpn t ht i₀ hi₀ j hj
    have hAub1 : ‖q i₀ - q j‖ ≤ ‖δ‖ / 2 := by
      refine hAub.trans ?_
      calc Cu * t ^ ((2:ℝ)/3) ≤ Cu * t₁ ^ ((2:ℝ)/3) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le htle (by norm_num)) hCu.le
        _ ≤ ‖δ‖ / 2 := hd₁
    have hstd : stdVar δ T t = δ := by
      refine stdVar_of_le hδ ?_
      have h2 : ‖δ‖ ≤ T / 2 := by linarith
      linarith
    have htri : ‖δ‖ ≤ ‖(q i₀ - q j) + δ‖ + ‖q i₀ - q j‖ := by
      have h := norm_sub_le ((q i₀ - q j) + δ) (q i₀ - q j)
      rwa [add_sub_cancel_left] at h
    rw [hqf, hstd]
    calc min (min cA cO) Cu * t ^ ((2:ℝ)/3) ≤ Cu * t ^ ((2:ℝ)/3) :=
          mul_le_mul_of_nonneg_right hcm (Real.rpow_nonneg ht.1.le _)
      _ ≤ Cu * t₁ ^ ((2:ℝ)/3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le htle (by norm_num)) hCu.le
      _ ≤ ‖δ‖ / 2 := hd₁
      _ ≤ ‖(q i₀ - q j) + δ‖ := by linarith
  · have htlt : t₁ < t := not_le.mp htle
    have hOn' := hOn t ⟨htlt, ht.2⟩
    rw [hqf]
    have hsq := sqrt_gap_le_norm_add_smul (a := (q i₀ - q j)) hδ (stdCoef δ T t)
    have heq := norm_sub_proj_eq_sqrt (q i₀ - q j) hδ
    calc min (min cA cO) Cu * t ^ ((2:ℝ)/3) ≤ cO * t ^ ((2:ℝ)/3) :=
          mul_le_mul_of_nonneg_right hcmO (Real.rpow_nonneg ht.1.le _)
      _ ≤ ‖(q i₀ - q j) - (inner ℝ (q i₀ - q j) ((‖δ‖)⁻¹ • δ)) • ((‖δ‖)⁻¹ • δ)‖ := hOn'
      _ = Real.sqrt (‖q i₀ - q j‖ ^ 2 - (inner ℝ (q i₀ - q j) δ) ^ 2 / ‖δ‖ ^ 2) := heq
      _ ≤ ‖(q i₀ - q j) + stdCoef δ T t • δ‖ := hsq


/-- **The bumped pair lower bound**, all pairs at once. -/
theorem seq_bumped_pair_lower {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {κ ε T Cu t₁ : ℝ} {sbar : EN E N} {i₀ : Fin N} {δ : E}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hδ : δ ≠ 0)
    (hκ : 0 < κ) (hε : 0 < ε) (hT : 0 < T) (hδT : 2 * ‖δ‖ ≤ T)
    (hi₀ : i₀ ∈ k)
    (hnc : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    {Cp : ℝ} (hCp : 0 < Cp) (hCu : 0 < Cu)
    (ht₁ : 0 < t₁) (ht₁T : t₁ ≤ T / 2) (hd₁ : Cu * t₁ ^ ((2:ℝ)/3) ≤ ‖δ‖ / 2)
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hU : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hUp : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, ∀ i ∈ k, ∀ jj ∈ k,
      ‖rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t jj‖
        ≤ Cu * t ^ ((2:ℝ)/3))
    (hG : ∀ η > (0:ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (x (t * lam n)) - sbar‖ < η)
    (hgood : ∀ j ∈ k.erase i₀, (inner ℝ (sbar i₀ - sbar j) δ) ^ 2
      < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, ∀ i ∈ k, ∀ j ∈ k, i ≠ j →
      c * t ^ ((2:ℝ)/3)
        ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i
            - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖ := by
  classical
  have hsne : (k.erase i₀).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_erase_of_mem hi₀]
    omega
  have hpair : ∀ j ∈ k.erase i₀, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      c * t ^ ((2:ℝ)/3)
        ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i₀
            - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖ := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
    exact seq_bumped_pair_lower_pair (m := m) (k := k) (x := x) (κ := κ) (ε := ε) (T := T)
      (Cu := Cu) (t₁ := t₁) (sbar := sbar) (i₀ := i₀) (j := j) (δ := δ)
      hm hk2 hδ hκ hε hT hδT hi₀ hj2 hj1 hnc hIn hCp hCu ht₁ ht₁T hd₁ hlam hU hUp hG
      (hgood j hj)
  let cB : Fin N → ℝ := fun j =>
    if hj : j ∈ k.erase i₀ then Classical.choose (hpair j hj) else 1
  have hcB : ∀ j (hj : j ∈ k.erase i₀),
      0 < cB j ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
        cB j * t ^ ((2:ℝ)/3)
          ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i₀
              - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖ := by
    intro j hj
    have h : cB j = Classical.choose (hpair j hj) := dif_pos hj
    rw [h]
    exact Classical.choose_spec (hpair j hj)
  set c0 : ℝ := (∑ j ∈ k.erase i₀, (cB j)⁻¹)⁻¹ with hc0
  have hcBpos : ∀ j (hj : j ∈ k.erase i₀), 0 < cB j := fun j hj => (hcB j hj).1
  have hsumpos : (0:ℝ) < ∑ j ∈ k.erase i₀, (cB j)⁻¹ :=
    Finset.sum_pos (fun j hj => inv_pos.mpr (hcBpos j hj)) hsne
  have hc0pos : 0 < c0 := by rw [hc0]; exact inv_pos.mpr hsumpos
  have hc0le : ∀ j ∈ k.erase i₀, c0 ≤ cB j := by
    intro j hj
    have h1 : (cB j)⁻¹ ≤ ∑ l ∈ k.erase i₀, (cB l)⁻¹ :=
      Finset.single_le_sum (fun l hl => (inv_pos.mpr (hcBpos l hl)).le) hj
    rw [hc0, inv_le_comm₀ hsumpos (hcBpos j hj)]
    exact h1
  have hBev : ∀ᶠ n in atTop, ∀ j ∈ k.erase i₀, ∀ t ∈ Ioc (0:ℝ) T,
      c0 * t ^ ((2:ℝ)/3)
        ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i₀
            - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖ := by
    refine (Finset.eventually_all (k.erase i₀)).mpr fun j hj => ?_
    filter_upwards [(hcB j hj).2] with n hn
    intro t ht
    exact le_trans (mul_le_mul_of_nonneg_right (hc0le j hj) (Real.rpow_nonneg ht.1.le _))
      (hn t ht)
  have hA := seq_pair_lower_bound_uniform (m := m) (k := k) (x := x)
    (ε := ε) (T := T) (Cp := Cp) hm hk2 hε hT hCp hnc hlam hU
  set cA : ℝ := ((∑ l ∈ k, (m l)⁻¹)⁻¹) ^ 2 / Cp with hcA
  have hsumpos' : (0:ℝ) < ∑ l ∈ k, (m l)⁻¹ :=
    Finset.sum_pos (fun l _ => inv_pos.mpr (hm l)) (Finset.card_pos.mp (by omega))
  have hcApos : 0 < cA := by
    rw [hcA]; exact div_pos (pow_pos (inv_pos.mpr hsumpos') 2) hCp
  refine ⟨min cA c0, lt_min hcApos hc0pos, ?_⟩
  filter_upwards [hA, hBev] with n hAn hBn
  intro t ht i hi j hj hij
  have hrp : 0 ≤ t ^ ((2:ℝ)/3) := Real.rpow_nonneg ht.1.le _
  by_cases hii : i = i₀
  · have hji : j ≠ i₀ := fun h => hij (hii.trans h.symm)
    rw [hii]
    have hmem : j ∈ k.erase i₀ := Finset.mem_erase.mpr ⟨hji, hj⟩
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hrp) (hBn j hmem t ht)
  · by_cases hjj : j = i₀
    · rw [hjj, ← norm_neg, neg_sub]
      have hmem : i ∈ k.erase i₀ := Finset.mem_erase.mpr ⟨hii, hi⟩
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hrp) (hBn i hmem t ht)
    · have hsub : (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i
          - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j
          = rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j := by
        rw [PiLp.add_apply, PiLp.add_apply,
          show rescaledCentered m k x (lam n) t i + stdVarVec m k i₀ δ T t i
              - (rescaledCentered m k x (lam n) t j + stdVarVec m k i₀ δ T t j)
            = (rescaledCentered m k x (lam n) t i - rescaledCentered m k x (lam n) t j)
              + (stdVarVec m k i₀ δ T t i - stdVarVec m k i₀ δ T t j) from by abel,
          stdVarVec_sub_of_notMem (m := m) (k := k) (i₀ := i₀) (i := i) (j := j) T t hi hj hii hjj,
          add_zero]
      rw [hsub]
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hrp) (hAn i hi j hj hij t ht)

/-- **The bumped potential bound** (`hp2` of the sequential transfer) and the absence of
collisions inside the cluster, both from the bumped pair lower bound. -/
theorem seq_bumped_potential_bound {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {i₀ : Fin N} {δ : E} {T c : ℝ} (hm : ∀ i, 0 ≤ m i) (hT : 0 < T) (hc : 0 < c)
    {lam : ℕ → ℝ}
    (hLow : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, ∀ i ∈ k, ∀ j ∈ k, i ≠ j →
      c * t ^ ((2:ℝ)/3)
        ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i
            - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t)
        ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
            m p.1 * m p.2 / c) * t ^ (-(2:ℝ)/3) := by
  filter_upwards [hLow] with n hn t ht
  exact clusterPotential_le_of_pair_lower hm _ hc ht.1 (fun i hi j hj hij => hn t ht i hi j hj hij)

/-- The bumped configuration is collision free inside the cluster. -/
theorem seq_bumped_noColl {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {i₀ : Fin N} {δ : E} {T c : ℝ} (hT : 0 < T) (hc : 0 < c) {lam : ℕ → ℝ}
    (hLow : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, ∀ i ∈ k, ∀ j ∈ k, i ≠ j →
      c * t ^ ((2:ℝ)/3)
        ≤ ‖(rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) i
            - (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) j‖) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioo (0:ℝ) T,
      ClusterNoColl k (rescaledCentered m k x (lam n) t + stdVarVec m k i₀ δ T t) :=
  hLow.mono fun n hn t ht => clusterNoColl_of_pair_lower hc ht.1 (fun i hi j hj hij =>
    hn t ⟨ht.1, le_of_lt ht.2⟩ i hi j hj hij)

end Submission.NBody
