import Submission.FUP.PSHToFourier3

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-! ### The final pointwise estimates -/

/-- **Estimate (i) away from the origin, in the form used for `|F(x)| ≤ C e^{u(x)}`.** -/
lemma norm_F_sq_le_quarter {ρ CLip KF : ℝ} (hρ : 0 < ρ) (hCLip : 0 ≤ CLip) (hd : 1 ≤ d)
    {u u0 : ℂᵈ → ℝ} {F : ℂᵈ → ℂ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hFana : AnalyticOnNhd ℂ F Set.univ)
    (hMF : ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal KF)
    (hKF : 0 < KF)
    {x : ℝᵈ} (hx : 1 / 4 ≤ ‖toCpx x‖) :
    ‖F (toCpx x)‖ ^ 2 ≤ ((Real.pi * rr d ^ 2) ^ d)⁻¹
      * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
          + Bsmall2 ρ CLip d) * KF := by
  have hrp : (0:ℝ) < rr d := rr_pos hd
  have hsub : Metric.closedBall (toCpx x) (rr d) ⊆ U5 (d := d) := by
    intro w hw
    rw [mem_U5]
    have h2 : ‖w - toCpx x‖ ≤ rr d := by
      have h1 : dist w (toCpx x) ≤ rr d := by simpa [Metric.mem_closedBall] using hw
      simpa [dist_eq_norm] using h1
    have h3 : ‖toCpx x‖ ≤ ‖w‖ + ‖w - toCpx x‖ := by
      have h5 := norm_le_add_norm_add' (toCpx x) w
      rw [norm_sub_rev] at h5
      exact h5
    have h4 : rr d ≤ 1 / 8 := by
      rw [rr, div_le_iff₀ (by positivity : (0:ℝ) < 8 * Real.sqrt d)]
      have hs : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
      linarith
    linarith
  have hB : ∀ w ∈ Metric.closedBall (toCpx x) (rr d),
      section5Phi ρ u u0 w ≤ 2 * u (toCpx x) + ρ * u0 (toCpx x)
        + 20 * (d : ℝ) * Real.log (1 + ‖x‖) + Bsmall2 ρ CLip d :=
    fun w hw => section5Phi_le_at (d := d) hρ hCLip hunonpos hulip hugrowth hu0lip hu0growth w
      (Metric.closedBall_subset_closedBall (by
        rw [rr, div_le_iff₀ (by positivity : (0:ℝ) < 8 * Real.sqrt d)]
        have hs : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
        linarith) hw)
  have hana : AnalyticOnNhd ℂ F (Metric.closedBall (toCpx x) (rr d)) := hFana.mono (Set.subset_univ _)
  have h1 := ofReal_norm_sq_le_of_analyticOnNhd (ρ := ρ) (u := u) (u0 := u0) (f := F)
    hrp hana hB
  have h2 : ∫⁻ w in Metric.closedBall (toCpx x) (rr d),
      ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))) ≤ ENNReal.ofReal KF :=
    le_trans (lintegral_mono_set hsub) hMF
  have h3 : ENNReal.ofReal (‖F (toCpx x)‖ ^ 2)
      ≤ ENNReal.ofReal (((Real.pi * rr d ^ 2) ^ d)⁻¹
        * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
            + Bsmall2 ρ CLip d)) * ENNReal.ofReal KF :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal _ from bot_le))
  have h4 : ENNReal.ofReal (‖F (toCpx x)‖ ^ 2)
      ≤ ENNReal.ofReal ((((Real.pi * rr d ^ 2) ^ d)⁻¹
        * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
            + Bsmall2 ρ CLip d)) * KF) := by
    refine le_trans h3 ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4

/-- A lower bound at the origin from a bound on the punctured ball (continuity). -/
lemma le_norm_of_forall_near_zero (hd : 1 ≤ d) {F : ℂᵈ → ℂ} (hF : ContinuousAt F 0)
    {c rmin : ℝ} (hrmin : 0 < rmin)
    (h : ∀ x : ℝᵈ, 0 < ‖x‖ → ‖x‖ ≤ rmin → c ≤ ‖F (toCpx x)‖) :
    c ≤ ‖F 0‖ := by
  classical
  set e : ℝᵈ := EuclideanSpace.single ⟨0, hd⟩ 1 with he
  have he1 : ‖e‖ = 1 := by
    rw [he]
    simp
  set t : ℕ → ℝ := fun n => rmin * (1 / ((n : ℝ) + 1)) with ht
  have htpos : ∀ n, 0 < t n := fun n => by rw [ht]; positivity
  have htle : ∀ n, t n ≤ rmin := fun n => by
    rw [ht]
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith [hrmin]
  have hxn : ∀ n, ‖t n • e‖ = t n := fun n => by
    rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos (htpos n)]
  have htend : Tendsto t atTop (𝓝 0) := by
    rw [ht]
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => rmin * ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 (rmin * 0)) :=
      tendsto_const_nhds.mul h1
    simpa using h2
  have h2 : Tendsto (fun n : ℕ => toCpx (t n • e)) atTop (𝓝 (0 : ℂᵈ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) htend
    simp only [sub_zero]
    calc ‖toCpx (t n • e)‖ ≤ ‖t n • e‖ := norm_toCpx_le _
      _ = t n := hxn n
  have hcont : Tendsto (fun n : ℕ => F (toCpx (t n • e))) atTop (𝓝 (F 0)) :=
    hF.tendsto.comp h2
  have hnorm : Tendsto (fun n : ℕ => ‖F (toCpx (t n • e))‖) atTop (𝓝 ‖F 0‖) :=
    continuous_norm.continuousAt.tendsto.comp hcont
  exact ge_of_tendsto' hnorm (fun n => h (t n • e) (by rw [hxn n]; exact htpos n) (by
    rw [hxn n]; exact htle n))

lemma sqrt_exp (a : ℝ) : Real.sqrt (Real.exp a) = Real.exp (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  ring_nf

/-- **The two pointwise estimates on `F`** (i) growth in the imaginary direction and
(iii) reduction to `e^{u(x)}` on the real subspace. -/
lemma norm_F_bounds (hd : 1 ≤ d) {ρ CLip lam B1 B2 KF Kg : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam)
    (hCLip : 0 < CLip)
    {u u0 : ℂᵈ → ℝ} {F g : ℂᵈ → ℂ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0nonpos : ∀ x : ℝᵈ, u0 (toCpx x) ≤ 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hu0le : ∀ x : ℝᵈ, u0 (toCpx x) ≤ lam * omega0 x)
    (habs1 : ∀ t : ℝ, 0 ≤ t → 20 * (d : ℝ) * Real.log (1 + t) ≤ (ρ / 2) * t + B1)
    (habs2 : ∀ t : ℝ, 0 ≤ t → 20 * (d : ℝ) * Real.log (1 + t)
      - ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2)) ≤ B2)
    (hFana : AnalyticOnNhd ℂ F Set.univ)
    (hg_ana : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂᵈ) (1 / 2)))
    (hFeq : ∀ z, F z = bumpC (d := d) z - g z)
    (hMF : ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal KF)
    (hKF : 0 < KF)
    (hMg : ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal Kg)
    (hKg : 0 < Kg) :
    (∀ z : ℂᵈ, ‖F z‖ ≤ max (Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp (ρ / 4 + (B1 + B2) / 2))
      (1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg))
      * Real.exp (2 * ρ * ‖imVec z‖)) ∧
    (∀ x : ℝᵈ, ‖F (toCpx x)‖ ≤ max
      ((1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg))
        * Real.exp (CLip * Real.sqrt d / 4))
      (Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp ((B2 + Bsmall2 ρ CLip d) / 2)) * Real.exp (u (toCpx x))) := by
  set A1 : ℝ := Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
    * Real.exp (ρ / 4 + (B1 + B2) / 2) with hA1
  set A2 : ℝ := 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg)
    with hA2
  have hA2nn : 0 ≤ A2 := by rw [hA2]; positivity
  have hsmall : ∀ z : ℂᵈ, ‖z‖ < 1 / 4 → ‖F z‖ ≤ A2 := by
    intro z hz
    have h1 := norm_g_sq_le_le_quarter (d := d) hρ hCLip.le hKg hunonpos hugrowth hu0nonpos
      hu0growth hg_ana hMg hd hz.le
    have h2 : ‖g z‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg) :=
      Real.le_sqrt_of_sq_le h1
    rw [hFeq z, hA2]
    calc ‖bumpC (d := d) z - g z‖ ≤ ‖bumpC (d := d) z‖ + ‖g z‖ := norm_sub_le _ _
      _ ≤ 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg) :=
          add_le_add (norm_bumpC_le_one z) h2
  constructor
  · intro z
    rcases lt_or_ge ‖z‖ (1 / 4) with hz | hz
    · have h4 : A2 * Real.exp (2 * ρ * ‖imVec z‖) ≥ A2 := by
        have h5 : (1:ℝ) ≤ Real.exp (2 * ρ * ‖imVec z‖) := Real.one_le_exp (by positivity)
        nlinarith [Real.exp_pos (2 * ρ * ‖imVec z‖)]
      calc ‖F z‖ ≤ A2 := hsmall z hz
        _ ≤ max A1 A2 := le_max_right _ _
        _ ≤ max A1 A2 * Real.exp (2 * ρ * ‖imVec z‖) := by
            have h5 : (1:ℝ) ≤ Real.exp (2 * ρ * ‖imVec z‖) := Real.one_le_exp (by positivity)
            have h6 : 0 ≤ max A1 A2 := le_trans hA2nn (le_max_right A1 A2)
            have h7 : max A1 A2 ≤ max A1 A2 * Real.exp (2 * ρ * ‖imVec z‖) := by
              nlinarith [Real.exp_pos (2 * ρ * ‖imVec z‖)]
            exact h7
    · have h1 := norm_F_sq_le_ge_quarter (d := d) hd hρ hlam hunonpos hugrowth hu0growth hu0le
          habs1 habs2 hFana hMF hKF hz
      have h2 : ‖F z‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
          * Real.exp (2 * ρ * ‖imVec z‖ + ρ / 4 + (B1 + B2) / 2) := by
        refine le_trans (Real.le_sqrt_of_sq_le h1) (le_of_eq ?_)
        rw [Real.sqrt_mul (by positivity), sqrt_exp]
        congr 1
        ring
      have h3 : Real.exp (2 * ρ * ‖imVec z‖ + ρ / 4 + (B1 + B2) / 2)
          = Real.exp (ρ / 4 + (B1 + B2) / 2) * Real.exp (2 * ρ * ‖imVec z‖) := by
        rw [← Real.exp_add]; ring_nf
      rw [h3] at h2
      calc ‖F z‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
            * Real.exp (ρ / 4 + (B1 + B2) / 2) * Real.exp (2 * ρ * ‖imVec z‖) := by
            linarith [h2]
        _ = A1 * Real.exp (2 * ρ * ‖imVec z‖) := by rw [hA1]
        _ ≤ max A1 A2 * Real.exp (2 * ρ * ‖imVec z‖) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · intro x
    rcases lt_or_ge ‖toCpx x‖ (1 / 4) with hx | hx
    · have h1 : ‖F (toCpx x)‖ ≤ A2 := hsmall (toCpx x) hx
      have hxle : ‖x‖ ≤ Real.sqrt d / 4 := by
        have h := norm_toCpx_ge x
        have hs : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
        nlinarith [norm_nonneg (toCpx x), h]
      have h2 : -CLip * (Real.sqrt d / 4) ≤ u (toCpx x) := by
        have h := hulip x 0
        have h0 : u (toCpx (0 : ℝᵈ)) = 0 := huzero 0 (by simp)
        simp only [h0, sub_zero] at h
        have h3 : -CLip * ‖x‖ ≤ u (toCpx x) := by linarith [neg_abs_le (u (toCpx x))]
        have h4 : CLip * ‖x‖ ≤ CLip * (Real.sqrt d / 4) :=
          mul_le_mul_of_nonneg_left hxle hCLip.le
        linarith
      have h3 : A2 ≤ A2 * Real.exp (CLip * Real.sqrt d / 4) * Real.exp (u (toCpx x)) := by
        have he : Real.exp (-(CLip * (Real.sqrt d / 4))) ≤ Real.exp (u (toCpx x)) :=
          Real.exp_le_exp.mpr (by linarith)
        have he2 : Real.exp (CLip * Real.sqrt d / 4)
            * Real.exp (-(CLip * (Real.sqrt d / 4))) = 1 := by
          rw [← Real.exp_add]
          ring_nf
          simp
        have h7 : A2 * Real.exp (CLip * Real.sqrt d / 4)
            * Real.exp (-(CLip * (Real.sqrt d / 4))) = A2 := by
          rw [mul_assoc, he2, mul_one]
        have h8 : A2 * Real.exp (CLip * Real.sqrt d / 4) * Real.exp (-(CLip * (Real.sqrt d / 4)))
            ≤ A2 * Real.exp (CLip * Real.sqrt d / 4) * Real.exp (u (toCpx x)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hA2nn (Real.exp_pos _).le)
        linarith [h7, h8]
      calc ‖F (toCpx x)‖ ≤ A2 := h1
        _ ≤ A2 * Real.exp (CLip * Real.sqrt d / 4) * Real.exp (u (toCpx x)) := h3
        _ ≤ max (A2 * Real.exp (CLip * Real.sqrt d / 4))
              (Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
                * Real.exp ((B2 + Bsmall2 ρ CLip d) / 2)) * Real.exp (u (toCpx x)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have h1 := @norm_F_sq_le_quarter d ρ CLip KF hρ hCLip.le hd u u0 F hunonpos hulip hugrowth hu0lip hu0growth hFana hMF hKF x hx
      have h2 : ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖) ≤ B2 := by
        have h3 := habs2 ‖x‖ (norm_nonneg x)
        have h4 : u0 (toCpx x) ≤ lam * omega0 x := hu0le x
        have h5 : ρ * u0 (toCpx x) ≤ -(ρ * lam * (Real.smoothTransition (‖x‖ / 5 - 1)
            * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))) := by
          have h6 := mul_le_mul_of_nonneg_left h4 hρ.le
          rw [omega0] at h6
          linarith
        linarith
      have h7 : ‖F (toCpx x)‖ ^ 2 ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
          * Real.exp (2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d)) := by
        have hX : 2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
            + Bsmall2 ρ CLip d ≤ 2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d) := by linarith
        calc ‖F (toCpx x)‖ ^ 2 ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹
              * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
                  + Bsmall2 ρ CLip d)) * KF := h1
          _ ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
              * Real.exp (2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d)) := by
              have hA : (0:ℝ) ≤ ((Real.pi * rr d ^ 2) ^ d)⁻¹ := by positivity
              have he : Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x)
                  + 20 * (d : ℝ) * Real.log (1 + ‖x‖) + Bsmall2 ρ CLip d)
                  ≤ Real.exp (2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d)) :=
                Real.exp_le_exp.mpr hX
              calc (((Real.pi * rr d ^ 2) ^ d)⁻¹
                    * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
                        + Bsmall2 ρ CLip d)) * KF
                  = (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
                    * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
                        + Bsmall2 ρ CLip d) := by ring
                _ ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
                    * Real.exp (2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d)) :=
                    mul_le_mul_of_nonneg_left he (mul_nonneg hA hKF.le)
      have h8 : ‖F (toCpx x)‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
          * Real.exp ((B2 + Bsmall2 ρ CLip d) / 2) * Real.exp (u (toCpx x)) := by
        have h9 : ‖F (toCpx x)‖ ≤ Real.sqrt ((((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
            * Real.exp (2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d))) := Real.le_sqrt_of_sq_le h7
        refine le_trans h9 (le_of_eq ?_)
        have hz : (2 * u (toCpx x) + (B2 + Bsmall2 ρ CLip d)) / 2
            = u (toCpx x) + (B2 + Bsmall2 ρ CLip d) / 2 := by ring
        rw [Real.sqrt_mul (by positivity), sqrt_exp, hz, Real.exp_add]
        ring
      calc ‖F (toCpx x)‖
          ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
            * Real.exp ((B2 + Bsmall2 ρ CLip d) / 2) * Real.exp (u (toCpx x)) := h8
        _ ≤ max (A2 * Real.exp (CLip * Real.sqrt d / 4))
              (Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
                * Real.exp ((B2 + Bsmall2 ρ CLip d) / 2)) * Real.exp (u (toCpx x)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le


end Submission.FUP
