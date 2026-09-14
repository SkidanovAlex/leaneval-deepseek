import Submission.NBody.MarchalBumpTwoSided

/-!
# The scalar endgame of the symmetric-bump argument

Once the two window bounds are available, the negativity of their sum is a purely scalar statement:
writing `x = ‖δ‖^{1/2}` and `W = T·(∑_{cross} mᵢmⱼ)·2‖δ‖·(ν_R^{-2} + ν_L^{-2})`, the sum is

  `λ^{1/3} (K_R + K_L - (A_R + A_L) x + (B_R + B_L)‖δ‖) + λ^{5/3} W`,

which is `< 0` once `‖δ‖` is small enough (so that the `Θ(‖δ‖)` terms are dominated by
`-Θ(‖δ‖^{1/2})`) and then `λ` small enough (so that `λ^{4/3}W` is dominated by the same).

All results in this file are fully proved.
-/

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

/-- `λ^p W` is eventually below any positive constant, as `λ → 0⁺`. -/
lemma eventually_rpow_mul_lt {p W X : ℝ} (hp : 0 < p) (hX : 0 < X) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), lam ^ p * W < X := by
  rcases le_or_gt W 0 with hW | hW
  · filter_upwards [self_mem_nhdsWithin] with lam hlam
    have h1 : lam ^ p * W ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hlam.le _) hW
    linarith
  · have ht : Tendsto (fun lam : ℝ => lam ^ p) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
      Filter.Tendsto.rpow_const_nhds_zero (tendsto_id.mono_left nhdsWithin_le_nhds) hp
    have h2 : Tendsto (fun lam : ℝ => lam ^ p * W) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      have h3 := ht.mul (tendsto_const_nhds (x := W))
      simpa only [zero_mul] using h3
    exact h2.eventually (eventually_lt_nhds hX)

/-- `lam * lam^{2/3} = lam^{1/3} * lam^{4/3}` for `lam > 0`. -/
lemma mul_rpow_two_thirds (lam : ℝ) (hlam : 0 < lam) :
    lam * lam ^ ((2:ℝ)/3) = lam ^ ((1:ℝ)/3) * lam ^ ((4:ℝ)/3) := by
  nth_rewrite 1 [← Real.rpow_one lam]
  rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]
  norm_num

/-- **The scalar endgame.**  If the `Θ(‖δ‖)`-terms of the two window bounds are dominated by
`(A_R + A_L)/2 · ‖δ‖^{1/2}`, then for small `λ` the sum of the two window bounds is negative. -/
theorem eventually_two_window_bounds_negative {T : ℝ} (hT : 0 < T) {δ : E} (hδ : δ ≠ 0)
    {u₀ : EN E N} {m : Fin N → ℝ}
    {CdR CdL νR νL AR AL BR BL Cu : ℝ}
    (hCdR : 0 ≤ CdR) (hCdL : 0 ≤ CdL) (hνR : 0 < νR) (hνL : 0 < νL) (hCu : 0 ≤ Cu)
    (hA : 0 < AR + AL)
    (hsmall : CdR * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)
        + BR * ‖δ‖ + CdL * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)
        + BL * ‖δ‖ ≤ (AR + AL) / 2 * ‖δ‖ ^ ((1:ℝ)/2)) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      (lam ^ ((1:ℝ)/3) * ((CdR * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
            + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)) + (-AR * ‖δ‖ ^ ((1:ℝ)/2) + BR * ‖δ‖))
        + lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2))))
      + (lam ^ ((1:ℝ)/3) * ((CdL * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
            + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)) + (-AL * ‖δ‖ ^ ((1:ℝ)/2) + BL * ‖δ‖))
        + lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))))
      < 0 := by
  set WR : ℝ := T * Cu * (2 * ‖δ‖ / νR ^ 2) with hWR
  set WL : ℝ := T * Cu * (2 * ‖δ‖ / νL ^ 2) with hWL
  have hev : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      lam ^ ((4:ℝ)/3) * (WR + WL) < (AR + AL) / 2 * ‖δ‖ ^ ((1:ℝ)/2) :=
    eventually_rpow_mul_lt (by norm_num : (0:ℝ) < (4:ℝ)/3)
      (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with lam hlt hlam
  have h13 : 0 < lam ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos hlam _
  have eR : lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)))
      = lam ^ ((1:ℝ)/3) * (lam ^ ((4:ℝ)/3) * WR) := by
    have h1 : T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2))
        = lam ^ ((2:ℝ)/3) * WR := by
      rw [hWR]
      field_simp
    rw [h1, ← mul_assoc, mul_rpow_two_thirds lam hlam, mul_assoc]
  have eL : lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)))
      = lam ^ ((1:ℝ)/3) * (lam ^ ((4:ℝ)/3) * WL) := by
    have h1 : T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))
        = lam ^ ((2:ℝ)/3) * WL := by
      rw [hWL]
      field_simp
    rw [h1, ← mul_assoc, mul_rpow_two_thirds lam hlam, mul_assoc]
  have hTot : (lam ^ ((1:ℝ)/3) * ((CdR * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
          + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)) + (-AR * ‖δ‖ ^ ((1:ℝ)/2) + BR * ‖δ‖))
        + lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2))))
      + (lam ^ ((1:ℝ)/3) * ((CdL * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
          + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)) + (-AL * ‖δ‖ ^ ((1:ℝ)/2) + BL * ‖δ‖))
        + lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))))
      = lam ^ ((1:ℝ)/3) * (CdR * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖)
          + BR * ‖δ‖ + CdL * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
          + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖) + BL * ‖δ‖ - (AR + AL) * ‖δ‖ ^ ((1:ℝ)/2)
          + lam ^ ((4:ℝ)/3) * (WR + WL)) := by
    rw [eR, eL]
    ring
  rw [hTot]
  refine mul_neg_of_pos_of_neg h13 ?_
  nlinarith [hsmall, hlt]

/-! ## The final combination of the two windows -/

theorem exists_bump_competitor_window {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {T t₀ h : ℝ} (hT : 0 < T)
    (hδT : ‖δ‖ ≤ T / 2) {γ : ℝ → EN E N} {CdR CdL Cp νR νL AR AL BR BL Cu : ℝ}
    (hCdR : 0 ≤ CdR) (hCdL : 0 ≤ CdL) (hCp : 0 ≤ Cp) (hνR : 0 < νR) (hνL : 0 < νL)
    (hA : 0 < AR + AL)
    (hsmall : CdR * ‖stdPertVec m k i₀ δ‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
        + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖) + BR * ‖δ‖
        + CdL * ‖stdPertVec m k i₀ δ‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
        + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖) + BL * ‖δ‖
        ≤ (AR + AL) / 2 * ‖δ‖ ^ ((1:ℝ)/2))
    (hCu : Cu = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      m p.1 * m p.2)
    (hacR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (hncIR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∀ u ∈ Ioo t₀ (t₀ + lam * T), WithoutCollisions (γ u))
    (hvelR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k γ t₀ lam) t‖_[m] ≤ CdR * t ^ (-(1:ℝ)/3))
    (hUpotR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k γ t₀ lam t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hsgnR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (bumpRescaled m k γ t₀ lam t i₀ - bumpRescaled m k γ t₀ lam t j) δ)
    (hsepR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ClusterSeparated k (γ (t₀ + lam * t)) νR)
    (hpotR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∫ t in (0:ℝ)..T,
      (clusterPotential m k (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (bumpRescaled m k γ t₀ lam t))
      ≤ -AR * ‖δ‖ ^ ((1:ℝ)/2) + BR * ‖δ‖)
    (hacL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      AbsolutelyContinuousOnInterval (reflectCurve γ t₀) 0 (0 + lam * T))
    (hncIL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∀ u ∈ Ioo (0:ℝ) (0 + lam * T), WithoutCollisions (reflectCurve γ t₀ u))
    (hvelL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k (reflectCurve γ t₀) 0 lam) t‖_[m] ≤ CdL * t ^ (-(1:ℝ)/3))
    (hUpotL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k (reflectCurve γ t₀) 0 lam t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hsgnL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (bumpRescaled m k (reflectCurve γ t₀) 0 lam t i₀
          - bumpRescaled m k (reflectCurve γ t₀) 0 lam t j) δ)
    (hsepL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ClusterSeparated k (reflectCurve γ t₀ (0 + lam * t)) νL)
    (hpotL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∫ t in (0:ℝ)..T,
      (clusterPotential m k (bumpRescaled m k (reflectCurve γ t₀) 0 lam t
          + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (bumpRescaled m k (reflectCurve γ t₀) 0 lam t))
      ≤ -AL * ‖δ‖ ^ ((1:ℝ)/2) + BL * ‖δ‖)
    (hint : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), IntervalIntegrable
      (fun u => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))
      volume (t₀ - lam * T) (t₀ + lam * T)) :
    ∃ lam ∈ Ioi (0:ℝ), ∫ u in (t₀ - lam * T)..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)) < 0 := by
  have hCu_nn : 0 ≤ Cu := by
    rw [hCu]
    exact Finset.sum_nonneg fun p _ => mul_nonneg ((hm p.1).le) ((hm p.2).le)
  have hR := bump_window_action_le_eventually (m := m) (k := k) (i₀ := i₀) (h := h) hm hi₀ hδ hT hδT
    (γ := γ) (Cd := CdR) (Cp := Cp) (ν := νR) (Pb := -AR * ‖δ‖ ^ ((1:ℝ)/2) + BR * ‖δ‖)
    hCdR hCp hνR hacR hncIR hvelR hUpotR hsgnR hsepR hpotR
  have hL := bump_window_action_le_eventually (m := m) (k := k) (i₀ := i₀) (h := h) hm hi₀ hδ
    (t₀ := 0) hT hδT (γ := reflectCurve γ t₀) (Cd := CdL) (Cp := Cp) (ν := νL)
    (Pb := -AL * ‖δ‖ ^ ((1:ℝ)/2) + BL * ‖δ‖) hCdL hCp hνL hacL hncIL hvelL hUpotL hsgnL hsepL hpotL
  simp only [zero_add] at hL
  have hneg := eventually_two_window_bounds_negative (m := m) (δ := δ)
    (u₀ := stdPertVec m k i₀ δ) (T := T) hT hδ hCdR hCdL hνR hνL hCu_nn hA hsmall
  rw [hCu] at hneg
  refine exists_bump_window_negative (fun i => (hm i).le) hT
    (BR := fun lam => lam ^ ((1:ℝ)/3) * ((CdR * ‖stdPertVec m k i₀ δ‖_[m]
            * (T / 2) ^ (-(1:ℝ)/3) + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖))
          + (-AR * ‖δ‖ ^ ((1:ℝ)/2) + BR * ‖δ‖))
        + lam * (T * ((∑ p ∈ (pairFinset N).filter
              (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2))))
    (BL := fun lam => lam ^ ((1:ℝ)/3) * ((CdL * ‖stdPertVec m k i₀ δ‖_[m]
            * (T / 2) ^ (-(1:ℝ)/3) + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖))
          + (-AL * ‖δ‖ ^ ((1:ℝ)/2) + BL * ‖δ‖))
        + lam * (T * ((∑ p ∈ (pairFinset N).filter
              (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))))
    hR hL hneg hint

end Submission.NBody
