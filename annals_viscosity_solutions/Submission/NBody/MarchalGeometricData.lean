import Submission.NBody.MarchalBumpScalar
import Submission.NBody.MarchalOutsideVelocity

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The velocity bound `hvel` of the blow-up data**, from the cluster asymptotics. -/
theorem eventually_vel_bound_of_asymptotics {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv T : ℝ}
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k x 0 lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := exists_norm_deriv_rescaledCentered_le (m := m) (k := k) (x := x)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) (T := T) hm hk2 hε hC hν hCv hT hnc hE hW hx hd2 hd3
    hode hsep hv hI
  refine ⟨Cd, hCdpos.le, ?_⟩
  filter_upwards [hCd] with lam h
  intro t ht
  simpa only [bumpRescaled_zero] using h t ht

/-- **The potential bound `hUpot` of the blow-up data**, from the cluster asymptotics. -/
theorem eventually_potential_bound_of_asymptotics {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    (hUlim : Tendsto (fun s : ℝ => clusterPotential m k (x s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ))) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k x 0 lam t)
        ≤ ((2:ℝ)/9 * κ + 1) * t ^ (-(2:ℝ)/3) := by
  obtain ⟨ε', hε'pos, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ∀ s ∈ Ioo (0:ℝ) ε',
      clusterPotential m k (x s) * s ^ ((2:ℝ)/3) ≤ (2:ℝ)/9 * κ + 1 := by
    have h := hUlim.eventually (eventually_lt_nhds (by linarith : (2:ℝ)/9 * κ < (2:ℝ)/9 * κ + 1))
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp h
    refine ⟨min δ 1, lt_min hδpos one_pos, fun s hs => le_of_lt ?_⟩
    have hs' : s ∈ Metric.ball (0:ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.1]
      exact lt_of_lt_of_le hs.2 (min_le_left _ _)
    exact hδ s hs' hs.1
  refine (eventually_nhdsWithin_iff).mpr (Metric.eventually_nhds_iff_ball.mpr
    ⟨ε' / T, div_pos hε'pos hT, ?_⟩)
  intro lam hlam hlampos
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlampos] at hlam
  intro t ht
  have ht0 : 0 < t := ht.1
  have hlt : lam * t < ε' := by
    have h1 : t * lam ≤ T * lam := mul_le_mul_of_nonneg_right ht.2 hlampos.le
    have h2 : T * lam < T * (ε' / T) := mul_lt_mul_of_pos_left hlam hT
    have h3 : T * (ε' / T) = ε' := by field_simp
    linarith [mul_comm t lam]
  have hspos : 0 < lam * t := mul_pos hlampos ht0
  have hmem : lam * t ∈ Ioo (0:ℝ) ε' := ⟨hspos, hlt⟩
  have hbound := hε' (lam * t) hmem
  have hkey : clusterPotential m k (bumpRescaled m k x 0 lam t)
      = lam ^ ((2:ℝ)/3) * clusterPotential m k (x (t * lam)) := by
    have h1 : bumpRescaled m k x 0 lam t = lam ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam)) := by
      simp [bumpRescaled, rescaledCentered, shiftCurve]
    rw [h1]
    have hs := clusterPotential_scaled (m := m) (k := k) (x := x (t * lam)) hlampos
    rw [hs, ← mul_assoc,
      show lam ^ ((2:ℝ)/3) * lam ^ (-(2:ℝ)/3) = 1 by
        rw [← Real.rpow_add hlampos]; norm_num,
      one_mul]
  have hspos' : 0 < t * lam := mul_pos ht0 hlampos
  have h3 : clusterPotential m k (x (t * lam)) * (t * lam) ^ ((2:ℝ)/3)
      ≤ (2:ℝ)/9 * κ + 1 := hε' (t * lam) ⟨hspos', by linarith [hlt]⟩
  have h4 : (0:ℝ) < (t * lam) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hspos' _
  have h5 : clusterPotential m k (x (t * lam))
      ≤ ((2:ℝ)/9 * κ + 1) / (t * lam) ^ ((2:ℝ)/3) := by
    rw [le_div_iff₀ h4]; linarith [h3]
  have h6 : lam ^ ((2:ℝ)/3) * (((2:ℝ)/9 * κ + 1) / (t * lam) ^ ((2:ℝ)/3))
      = ((2:ℝ)/9 * κ + 1) * t ^ (-(2:ℝ)/3) := by
    have ht3 : (0:ℝ) < t ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
    have hl3 : (0:ℝ) < lam ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hlampos _
    have htinv : (t ^ ((2:ℝ)/3))⁻¹ = t ^ (-(2:ℝ)/3) := by
      rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg ht0.le]
    rw [Real.mul_rpow ht0.le hlampos.le]
    simp only [div_eq_mul_inv, mul_inv]
    calc lam ^ ((2:ℝ)/3) * (((2:ℝ)/9 * κ + 1) * ((t ^ ((2:ℝ)/3))⁻¹ * (lam ^ ((2:ℝ)/3))⁻¹))
        = ((2:ℝ)/9 * κ + 1) * (t ^ ((2:ℝ)/3))⁻¹
            * (lam ^ ((2:ℝ)/3) * (lam ^ ((2:ℝ)/3))⁻¹) := by ring
      _ = ((2:ℝ)/9 * κ + 1) * t ^ (-(2:ℝ)/3) := by
          rw [mul_inv_cancel₀ hl3.ne', mul_one, htinv]
  calc clusterPotential m k (bumpRescaled m k x 0 lam t)
      = lam ^ ((2:ℝ)/3) * clusterPotential m k (x (t * lam)) := hkey
    _ ≤ lam ^ ((2:ℝ)/3) * (((2:ℝ)/9 * κ + 1) / (t * lam) ^ ((2:ℝ)/3)) :=
        mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hlampos.le _)
    _ = ((2:ℝ)/9 * κ + 1) * t ^ (-(2:ℝ)/3) := h6

/-! ## The remaining eventual hypotheses of `exists_bump_competitor_window` -/

/-- Restricting an absolutely continuous curve to a smaller interval, eventually in `λ`. -/
theorem eventually_acOn_of_acOn {γ : ℝ → EN E N} {t₀ ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + ε)) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T) := by
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hT)] with lam hlam
  have hlampos : 0 < lam := hlam.1
  have hlt : lam * T < ε := by
    have h1 : T * lam < T * (ε / T) := mul_lt_mul_of_pos_left hlam.2 hT
    have h2 : T * (ε / T) = ε := by field_simp
    nlinarith [mul_comm lam T]
  refine hac.mono ?_
  rw [Set.uIcc_of_le (le_add_of_nonneg_right (mul_nonneg hlampos.le hT.le)),
    Set.uIcc_of_le (le_add_of_nonneg_right hε.le)]
  exact Set.Icc_subset_Icc_right (by linarith)

/-- Collision freeness transfers to the window, eventually in `λ`. -/
theorem eventually_withoutCollisions_of_withoutCollisions {γ : ℝ → EN E N} {t₀ ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T)
    (hnc : ∀ u ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ u)) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∀ u ∈ Ioo t₀ (t₀ + lam * T), WithoutCollisions (γ u) := by
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hT)] with lam hlam
  have hlt : lam * T < ε := by
    have h1 : T * lam < T * (ε / T) := mul_lt_mul_of_pos_left hlam.2 hT
    have h2 : T * (ε / T) = ε := by field_simp
    nlinarith [mul_comm lam T]
  intro u hu
  exact hnc u ⟨hu.1, by linarith [hu.2]⟩

/-- The cluster separation transfers to the window, eventually in `λ`. -/
theorem eventually_clusterSeparated_of_clusterSeparated {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε ν T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hsep : ∀ s ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x s) ν) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ClusterSeparatedWeak k (x (0 + lam * t)) ν := by
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hT)] with lam hlam
  have hlampos : 0 < lam := hlam.1
  have hlt : lam * T < ε := by
    have h1 : T * lam < T * (ε / T) := mul_lt_mul_of_pos_left hlam.2 hT
    have h2 : T * (ε / T) = ε := by field_simp
    nlinarith [mul_comm lam T]
  intro t ht
  rw [zero_add]
  refine hsep (lam * t) ⟨mul_pos hlampos ht.1, ?_⟩
  calc lam * t ≤ lam * T := mul_le_mul_of_nonneg_left ht.2 hlampos.le
    _ < ε := hlt

/-- The outward sign condition of the blow-up data, from the limit shape. -/
theorem eventually_inner_sign_of_asymptotics {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    {x : ℝ → EN E N} {ε κ T : ℝ} {sbar : EN E N} {δ : E}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ) (hT : 0 < T)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    (hpos : ∀ j ∈ k.erase i₀, 0 < inner ℝ (sbar i₀ - sbar j) δ) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (bumpRescaled m k x 0 lam t i₀ - bumpRescaled m k x 0 lam t j) δ := by
  have hper : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ j ∈ k.erase i₀,
      ∀ t ∈ Ioc (0:ℝ) T,
        0 ≤ inner ℝ (bumpRescaled m k x 0 lam t i₀ - bumpRescaled m k x 0 lam t j) δ := by
    rw [Finset.eventually_all]
    intro j hj
    have h := eventually_pair_inner_sign (m := m) (k := k) (x := x) (ε := ε) (κ := κ) (T := T)
      (sbar := sbar) (i₀ := i₀) (j := j) δ hε hκ hT hnc hIn hs hm hk2 (hpos j hj)
    filter_upwards [h] with lam h t ht
    have h2 := h t ht
    rwa [← bumpRescaled_zero] at h2
  exact hper.mono fun lam h t ht j hj => h j hj t ht

/-- **The potential gain `hpot` of the blow-up data**, from the two-sided pair bounds. -/
theorem eventually_potential_gain_of_asymptotics {m : Fin N → ℝ} {k : Finset (Fin N)}
    {i₀ : Fin N} {x : ℝ → EN E N} {ε κ T : ℝ} {sbar : EN E N} {δ : E}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hκ : 0 < κ) (hT : 0 < T)
    (hi₀ : i₀ ∈ k) (hδ : δ ≠ 0) (hδT : ‖δ‖ ≤ T / 4)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (x s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hs : Tendsto (fun s : ℝ => clusterShape m k (x s))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    (hsbar : ∀ j ∈ k.erase i₀, sbar i₀ ≠ sbar j)
    (hpos : ∀ j ∈ k.erase i₀, 0 < inner ℝ (sbar i₀ - sbar j) δ)
    {c C : ℝ} (hc : 0 < c) (hCc : c < C)
    (hev : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      c * t ^ ((2:ℝ)/3) ≤ ‖rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j‖ ∧
      ‖rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j‖ ≤ C * t ^ ((2:ℝ)/3))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hac : AbsolutelyContinuousOnInterval x 0 ε₀)
    (htA : (‖δ‖ / C) ^ ((3:ℝ)/2) ≤ T / 2) (htB : (‖δ‖ / c) ^ ((3:ℝ)/2) ≤ T / 2) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∫ t in (0:ℝ)..T,
      (clusterPotential m k (bumpRescaled m k x 0 lam t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (bumpRescaled m k x 0 lam t))
      ≤ -(∑ j ∈ k.erase i₀, m i₀ * m j)
            * (‖δ‖ ^ ((1:ℝ)/2) * (1 - c ^ 2 / C ^ 2) / (2 * C ^ ((3:ℝ)/2)))
          + (∑ j ∈ k.erase i₀, m i₀ * m j)
            * (2 * ‖δ‖ / (c * (T / 2) ^ ((2:ℝ)/3))) := by
  have hqmeas : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ j ∈ k.erase i₀,
      MeasureTheory.AEStronglyMeasurable
        (fun t => rescaledCentered m k x lam t i₀ - rescaledCentered m k x lam t j)
        (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)) := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hε₀ hT)] with lam hlam
    have hlt : lam * T ≤ ε₀ := by
      have h1 : T * lam < T * (ε₀ / T) := mul_lt_mul_of_pos_left hlam.2 hT
      have h2 : T * (ε₀ / T) = ε₀ := by field_simp
      nlinarith [mul_comm lam T]
    have hcont : ContinuousOn (fun t : ℝ => x (t * lam)) (Set.Icc (0:ℝ) T) := by
      have h := hac.continuousOn
      rw [Set.uIcc_of_le (le_of_lt hε₀)] at h
      have h2 : ContinuousOn (fun t : ℝ => t * lam) (Set.Icc (0:ℝ) T) := by fun_prop
      refine h.comp h2 ?_
      intro t ht
      exact ⟨mul_nonneg ht.1 hlam.1.le,
        (mul_le_mul_of_nonneg_right ht.2 hlam.1.le).trans (by linarith [hlt, mul_comm T lam])⟩
    intro j hj
    have h3 : ContinuousOn (fun t : ℝ => rescaledCentered m k x lam t i₀
        - rescaledCentered m k x lam t j) (Set.Icc (0:ℝ) T) := by
      have h4 : ContinuousOn (fun t : ℝ => cmRel m k (x (t * lam))) (Set.Icc (0:ℝ) T) :=
        (cmRelL m k).continuous.comp_continuousOn hcont
      have h5 : ContinuousOn (fun t : ℝ =>
          (lam ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam))) i₀
            - (lam ^ (-(2:ℝ)/3) • cmRel m k (x (t * lam))) j) (Set.Icc (0:ℝ) T) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin N => E) i₀).comp_continuousOn h4).const_smul
            (lam ^ (-(2:ℝ)/3))).sub
          (((PiLp.continuous_apply 2 (fun _ : Fin N => E) j).comp_continuousOn h4).const_smul
            (lam ^ (-(2:ℝ)/3)))
      refine h5.congr fun t _ => ?_
      simp only [rescaledCentered, PiLp.smul_apply]
    exact (h3.mono (Set.Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  have h := bump_potential_bound_eventually (m := m) (k := k) (x := x) (ε := ε) (κ := κ)
    (T := T) (c := c) (C := C) (sbar := sbar) (i₀ := i₀) δ hm hk2 hε hκ hT hc hCc hi₀ hδ hδT
    htA htB hnc hIn hs hsbar hpos hqmeas hev
  simpa only [bumpRescaled_zero, stdVarVec_eq_stdPert] using h

end Submission.NBody


