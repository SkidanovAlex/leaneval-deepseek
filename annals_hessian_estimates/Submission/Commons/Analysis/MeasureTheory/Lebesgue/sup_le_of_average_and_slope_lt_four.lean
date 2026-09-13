import Mathlib

open scoped Topology
open MeasureTheory Metric

namespace Commons.Analysis.MeasureTheory.Lebesgue

noncomputable section

lemma volume_ball_toReal_fin_four (x : EuclideanSpace ℝ (Fin 4)) {r : ℝ} (hr : 0 < r) :
    (MeasureTheory.volume (Metric.ball x r)).toReal = r ^ 4 * (√Real.pi ^ 4 / Real.Gamma 3) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  rw [show ((4:ℕ):ℝ) / 2 + 1 = 3 from by norm_num]
  rw [← ENNReal.ofReal_pow hr.le, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]

lemma volume_ball_toReal_ratio_fin_four
    (x y : EuclideanSpace ℝ (Fin 4)) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (MeasureTheory.volume (Metric.ball y t)).toReal
      / (MeasureTheory.volume (Metric.ball x s)).toReal = (t / s) ^ 4 := by
  rw [volume_ball_toReal_fin_four x hs, volume_ball_toReal_fin_four y ht]
  have hK : (√Real.pi ^ 4 / Real.Gamma 3) ≠ 0 := by positivity
  have hs4 : s ^ 4 ≠ 0 := by positivity
  field_simp

lemma setIntegral_abs_lower_bound_of_ball
    {h : EuclideanSpace ℝ (Fin 4) → ℝ} {x₀ y : EuclideanSpace ℝ (Fin 4)} {ρ t c : ℝ}
    (hint : IntegrableOn h (Metric.ball x₀ ρ) MeasureTheory.volume)
    (hsub : Metric.ball y t ⊆ Metric.ball x₀ ρ)
    (hle : ∀ z ∈ Metric.ball y t, c ≤ |h z|) :
    c * (MeasureTheory.volume (Metric.ball y t)).toReal ≤ ∫ z in Metric.ball x₀ ρ, |h z| := by
  have hcont : ∫ z in Metric.ball y t, |h z| ≤ ∫ z in Metric.ball x₀ ρ, |h z| := by
    apply setIntegral_mono_set (hint.abs)
    · filter_upwards with z using abs_nonneg (h z)
    · filter_upwards with z hz using hsub hz
  have hle2 : ∫ z in Metric.ball y t, c ≤ ∫ z in Metric.ball y t, |h z| := by
    apply setIntegral_mono_on
    · exact integrableOn_const
    · exact (hint.mono_set hsub).abs
    · exact measurableSet_ball
    · exact hle
  have hconst : ∫ z in Metric.ball y t, c = (MeasureTheory.volume (Metric.ball y t)).toReal * c := by
    rw [setIntegral_const, Measure.real_def]; ring
  linarith [hconst ▸ hle2]

lemma integrableOn_of_lipschitz_bound_on_closedBall
    {h : EuclideanSpace ℝ (Fin 4) → ℝ} {x₀ : EuclideanSpace ℝ (Fin 4)} {ρ L : ℝ} (hρ : 0 < ρ)
    (hbd : ∀ y ∈ Metric.closedBall x₀ ρ, ∀ z ∈ Metric.closedBall x₀ ρ,
      |h y - h z| ≤ L * dist y z) :
    IntegrableOn h (Metric.ball x₀ ρ) MeasureTheory.volume := by
  have hbd' : ∀ y ∈ Metric.closedBall x₀ ρ, ∀ z ∈ Metric.closedBall x₀ ρ,
      |h y - h z| ≤ (L.toNNReal : ℝ) * dist y z := by
    intro y hy z hz
    have h2 : L ≤ (L.toNNReal : ℝ) := Real.le_coe_toNNReal L
    have hd0 : 0 ≤ dist y z := dist_nonneg
    nlinarith [hbd y hy z hz, h2, hd0]
  have hLip : LipschitzOnWith L.toNNReal h (Metric.closedBall x₀ ρ) :=
    LipschitzOnWith.of_dist_le_mul (fun y hy z hz => by
      rw [Real.dist_eq]; exact hbd' y hy z hz)
  have hcont : ContinuousOn h (Metric.ball x₀ ρ) :=
    hLip.continuousOn.mono ball_subset_closedBall
  have haesm : AEStronglyMeasurable h (MeasureTheory.volume.restrict (Metric.ball x₀ ρ)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  have hx0 : x₀ ∈ Metric.closedBall x₀ ρ := mem_closedBall_self hρ.le
  refine IntegrableOn.of_bound measure_ball_lt_top haesm (|h x₀| + L.toNNReal * ρ) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  rw [Real.norm_eq_abs]
  calc |h y| = |h y - h x₀ + h x₀| := by ring_nf
    _ ≤ |h y - h x₀| + |h x₀| := abs_add_le _ _
    _ ≤ (L.toNNReal : ℝ) * dist y x₀ + |h x₀| := by
        gcongr
        exact hbd' y (ball_subset_closedBall hy) x₀ hx0
    _ ≤ (L.toNNReal : ℝ) * ρ + |h x₀| := by
        have hle : dist y x₀ ≤ ρ := le_of_lt (mem_ball.mp hy)
        nlinarith [hle, (L.toNNReal : ℝ), abs_nonneg (h x₀)]
    _ = |h x₀| + L.toNNReal * ρ := by ring

lemma integral_lower_bound
    {h : EuclideanSpace ℝ (Fin 4) → ℝ} {x₀ y : EuclideanSpace ℝ (Fin 4)} {r t c : ℝ}
    (hr : 0 < r) (ht : 0 < t) (htle : t ≤ r / 2) (hy : y ∈ Metric.ball x₀ (r / 2))
    (hint : IntegrableOn h (Metric.ball x₀ r) MeasureTheory.volume)
    (hle : ∀ z ∈ Metric.ball y t, c ≤ |h z|) :
    c * (t / r) ^ 4
      ≤ (∫ z in Metric.ball x₀ r, |h z|) / (MeasureTheory.volume (Metric.ball x₀ r)).toReal := by
  have hsub : Metric.ball y t ⊆ Metric.ball x₀ r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have hy' : dist y x₀ < r / 2 := mem_ball.mp hy
    calc dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle _ _ _
      _ < t + r / 2 := by linarith
      _ ≤ r := by linarith
  have hlb := setIntegral_abs_lower_bound_of_ball (h := h) (x₀ := x₀) (y := y)
    (ρ := r) (t := t) (c := c) hint hsub hle
  have hvolpos : 0 < (MeasureTheory.volume (Metric.ball x₀ r)).toReal := by
    rw [volume_ball_toReal_fin_four x₀ hr]; positivity
  rw [le_div_iff₀ hvolpos]
  calc c * (t / r) ^ 4 * (MeasureTheory.volume (Metric.ball x₀ r)).toReal
      = c * ((MeasureTheory.volume (Metric.ball y t)).toReal
          / (MeasureTheory.volume (Metric.ball x₀ r)).toReal)
          * (MeasureTheory.volume (Metric.ball x₀ r)).toReal := by
          rw [volume_ball_toReal_ratio_fin_four x₀ y hr ht]
    _ = c * (MeasureTheory.volume (Metric.ball y t)).toReal := by field_simp
    _ ≤ ∫ z in Metric.ball x₀ r, |h z| := hlb

theorem sup_le_of_average_and_slope_lt_four
    {h : EuclideanSpace ℝ (Fin 4) → ℝ} {x₀ : EuclideanSpace ℝ (Fin 4)} {A : ℝ} (hA : 0 ≤ A)
    (hx₀ : ‖x₀‖ < 4)
    (hL1 : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (∫ y in Metric.ball x₀ r, |h y|)
          / (MeasureTheory.volume (Metric.ball x₀ r)).toReal ≤ ε * r ^ 2)
    (hpoint : ∀ r : ℝ, 0 < r → 2 * r < 4 - ‖x₀‖ →
        ∀ y ∈ Metric.closedBall x₀ r, ∀ z ∈ Metric.closedBall x₀ r, y ≠ z →
        |h y - h z| / dist y z ≤ A / r * ((∫ w in Metric.ball x₀ (2 * r), |h w|)
          / (MeasureTheory.volume (Metric.ball x₀ (2 * r))).toReal) + A * r) :
    ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ y ∈ Metric.ball x₀ (r / 2), |h y| ≤ ε * r ^ 2 := by
  intro ε hε
  set μ : ℝ → ℝ := fun s => (∫ y in Metric.ball x₀ s, |h y|)
          / (MeasureTheory.volume (Metric.ball x₀ s)).toReal with hμ
  have hμnn : ∀ s, 0 ≤ μ s := by
    intro s; rw [hμ]
    exact div_nonneg (integral_nonneg fun y => abs_nonneg _) ENNReal.toReal_nonneg
  set ρ₁ : ℝ := (4 - ‖x₀‖) / 2 with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁]; linarith
  set Cc : ℝ := (2 * A) ^ 4 with hCc
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  set η : ℝ := min (1 / 4) (min (ε / 64) (ε ^ 5 / (32 * Cc + 1))) with hη
  have hηpos : 0 < η := by
    rw [hη]
    refine lt_min (by norm_num) (lt_min (by linarith) ?_)
    have hpos : (0:ℝ) < 32 * Cc + 1 := by positivity
    positivity
  have hηle : η ≤ 1 / 4 := by rw [hη]; exact min_le_left _ _
  have h32η : 32 * η ≤ ε := by
    have h1 : η ≤ ε / 64 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have h32ηC : 32 * η * Cc ≤ ε ^ 5 := by
    have h1 : η ≤ ε ^ 5 / (32 * Cc + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hden : (0:ℝ) < 32 * Cc + 1 := by positivity
    rw [le_div_iff₀ hden] at h1
    nlinarith [h1, hCc0, hηpos]
  have hgood : ({r : ℝ | μ r ≤ η * r ^ 2} : Set ℝ) ∈ 𝓝[>] (0:ℝ) := by
    rw [← Filter.eventually_iff]
    simpa only [hμ] using hL1 η hηpos
  rw [(nhdsGT_basis (0:ℝ)).mem_iff] at hgood
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := hgood
  set δ : ℝ := min ρ₁ (δ₁ / 2) with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min hρ₁pos (by linarith)
  rw [Filter.eventually_iff, (nhdsGT_basis (0:ℝ)).mem_iff]
  refine ⟨δ, hδpos, ?_⟩
  rintro r ⟨hrpos, hrδ⟩
  have hrρ₁ : r < ρ₁ := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hrδ₁ : r < δ₁ / 2 := lt_of_lt_of_le hrδ (min_le_right _ _)
  have h2r : 2 * r < 4 - ‖x₀‖ := by rw [hρ₁] at hrρ₁; linarith
  have hμr : μ r ≤ η * r ^ 2 := hδ₁sub ⟨hrpos, by linarith⟩
  have hμ2r : μ (2 * r) ≤ η * (2 * r) ^ 2 := hδ₁sub ⟨by linarith, by linarith⟩
  intro y hy
  rcases eq_or_lt_of_le (abs_nonneg (h y) : (0:ℝ) ≤ |h y|) with hv0 | hvpos
  · rw [← hv0]; exact mul_nonneg hε.le (sq_nonneg r)
  · set v : ℝ := |h y| with hv
    set L : ℝ := A / r * μ (2 * r) + A * r with hL
    have hLnonneg : 0 ≤ L := by
      rw [hL]
      have hAr : 0 ≤ A / r := div_nonneg hA hrpos.le
      have := hμnn (2 * r)
      nlinarith [hAr, this, hA, hrpos]
    have hLbd : ∀ y' ∈ Metric.closedBall x₀ r, ∀ z ∈ Metric.closedBall x₀ r,
        |h y' - h z| ≤ L * dist y' z := by
      intro y' hy' z hz
      rcases eq_or_ne y' z with rfl | hne
      · simp
      · have hd : 0 < dist y' z := dist_pos.mpr hne
        have hp : |h y' - h z| / dist y' z ≤ A / r * μ (2 * r) + A * r := by
          simpa only [hμ] using hpoint r hrpos h2r y' hy' z hz hne
        rw [hL]
        exact (div_le_iff₀ hd).mp hp
    have hint : IntegrableOn h (Metric.ball x₀ r) MeasureTheory.volume :=
      integrableOn_of_lipschitz_bound_on_closedBall hrpos hLbd
    have hkey : v ≤ 32 * μ r ∨ v ^ 5 ≤ 32 * μ r * L ^ 4 * r ^ 4 := by
      by_cases hcase : v ≤ r * L
      · right
        by_cases hL0 : L = 0
        · exfalso
          rw [hL0, mul_zero] at hcase
          linarith
        · have hLpos : 0 < L := lt_of_le_of_ne hLnonneg (Ne.symm hL0)
          set s : ℝ := v / (2 * L) with hs
          have hspos : 0 < s := by rw [hs]; positivity
          have hsle : s ≤ r / 2 := by
            rw [hs, div_le_iff₀ (by positivity : (0:ℝ) < 2 * L)]
            nlinarith [hcase]
          have hle : ∀ z ∈ Metric.ball y s, v / 2 ≤ |h z| := by
            intro z hz
            have hdz : dist z y < s := mem_ball.mp hz
            have hzc : z ∈ Metric.closedBall x₀ r := by
              rw [mem_closedBall]
              have hy' : dist y x₀ < r / 2 := mem_ball.mp hy
              calc dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle _ _ _
                _ ≤ s + r / 2 := by linarith
                _ ≤ r := by linarith
            have hyc : y ∈ Metric.closedBall x₀ r := by
              rw [mem_closedBall]; linarith [mem_ball.mp hy, hrpos]
            have hbdzy := hLbd z hzc y hyc
            have h1 : L * dist z y < v / 2 := by
              rw [hs] at hdz
              have he : L * (v / (2 * L)) = v / 2 := by field_simp
              calc L * dist z y < L * (v / (2 * L)) := mul_lt_mul_of_pos_left hdz hLpos
                _ = v / 2 := he
            have hab : v - |h z - h y| ≤ |h z| := by
              have hsab := abs_sub_abs_le_abs_sub (h y) (h z)
              rw [abs_sub_comm (h y) (h z)] at hsab
              linarith [hv]
            have hlt : |h z - h y| < v / 2 := lt_of_le_of_lt hbdzy h1
            linarith
          have hlb := integral_lower_bound hrpos hspos hsle hy hint hle
          have hden : 0 < 32 * L ^ 4 * r ^ 4 := by positivity
          have hleμ : (v / 2) * (s / r) ^ 4 ≤ μ r := by rw [hμ]; exact hlb
          have hmul : (v / 2) * (s / r) ^ 4 * (32 * L ^ 4 * r ^ 4)
              ≤ μ r * (32 * L ^ 4 * r ^ 4) :=
            mul_le_mul_of_nonneg_right hleμ (le_of_lt hden)
          have heq : (v / 2) * (s / r) ^ 4 * (32 * L ^ 4 * r ^ 4) = v ^ 5 := by
            rw [hs]; field_simp; ring
          calc v ^ 5 = (v / 2) * (s / r) ^ 4 * (32 * L ^ 4 * r ^ 4) := heq.symm
            _ ≤ μ r * (32 * L ^ 4 * r ^ 4) := hmul
            _ = 32 * μ r * L ^ 4 * r ^ 4 := by ring
      · left
        push_neg at hcase
        have hle : ∀ z ∈ Metric.ball y (r / 2), v / 2 ≤ |h z| := by
          intro z hz
          have hdz : dist z y < r / 2 := mem_ball.mp hz
          have hzc : z ∈ Metric.closedBall x₀ r := by
            rw [mem_closedBall]
            have hy' : dist y x₀ < r / 2 := mem_ball.mp hy
            calc dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle _ _ _
              _ ≤ r / 2 + r / 2 := by linarith
              _ = r := by ring
          have hyc : y ∈ Metric.closedBall x₀ r := by
            rw [mem_closedBall]; linarith [mem_ball.mp hy, hrpos]
          have hbdzy := hLbd z hzc y hyc
          have h1 : L * dist z y < v / 2 := by
            have h2 : L * dist z y ≤ L * (r / 2) :=
              mul_le_mul_of_nonneg_left (le_of_lt hdz) hLnonneg
            have h3 : L * (r / 2) < v / 2 := by nlinarith [hcase]
            linarith
          have hab : v - |h z - h y| ≤ |h z| := by
            have hsab := abs_sub_abs_le_abs_sub (h y) (h z)
            rw [abs_sub_comm (h y) (h z)] at hsab
            linarith [hv]
          have hlt : |h z - h y| < v / 2 := lt_of_le_of_lt hbdzy h1
          linarith
        have hlb := integral_lower_bound hrpos (by positivity : (0:ℝ) < r / 2) le_rfl hy hint hle
        have hleμ : (v / 2) * ((r / 2) / r) ^ 4 ≤ μ r := by rw [hμ]; exact hlb
        have he : (v / 2) * ((r / 2) / r) ^ 4 = v / 32 := by field_simp; ring
        rw [he] at hleμ
        linarith
    have hLle : L ≤ 2 * A * r := by
      rw [hL]
      have hAr : 0 ≤ A / r := div_nonneg hA hrpos.le
      have hterm : A / r * μ (2 * r) ≤ A / r * (η * (2 * r) ^ 2) :=
        mul_le_mul_of_nonneg_left hμ2r hAr
      have hexp : A / r * (η * (2 * r) ^ 2) = 4 * A * η * r := by
        rw [div_mul_eq_mul_div, div_eq_iff hrpos.ne']
        ring
      have hAr0 : 0 ≤ A * r := mul_nonneg hA hrpos.le
      have h4η : 4 * η ≤ 1 := by linarith [hηle]
      have hstep : 4 * A * η * r ≤ A * r := by
        have hm := mul_le_mul_of_nonneg_right h4η hAr0
        calc 4 * A * η * r = 4 * η * (A * r) := by ring
          _ ≤ 1 * (A * r) := hm
          _ = A * r := by ring
      linarith [hterm, hexp, hstep]
    have hpr : (0:ℝ) ≤ ε * r ^ 2 := mul_nonneg hε.le (sq_nonneg r)
    rcases hkey with hkey | hkey
    · have h1 : 32 * μ r ≤ 32 * (η * r ^ 2) := mul_le_mul_of_nonneg_left hμr (by norm_num)
      have h2 : 32 * η * r ^ 2 ≤ ε * r ^ 2 := by
        have := mul_le_mul_of_nonneg_right h32η (sq_nonneg r)
        linarith [this]
      linarith [hkey, h1, h2]
    · have hv5 : v ^ 5 ≤ (ε * r ^ 2) ^ 5 := by
        have hL4 : L ^ 4 ≤ (2 * A * r) ^ 4 := pow_le_pow_left₀ hLnonneg hLle 4
        have hμL : μ r * L ^ 4 ≤ (η * r ^ 2) * (2 * A * r) ^ 4 :=
          mul_le_mul hμr hL4 (by positivity) (by positivity)
        have hmid : 32 * μ r * L ^ 4 * r ^ 4
            ≤ 32 * (η * r ^ 2) * (2 * A * r) ^ 4 * r ^ 4 := by
          have hm := mul_le_mul_of_nonneg_right hμL (show (0:ℝ) ≤ 32 * r^4 by positivity)
          calc 32 * μ r * L ^ 4 * r ^ 4 = (μ r * L ^ 4) * (32 * r ^ 4) := by ring
            _ ≤ ((η * r ^ 2) * (2 * A * r) ^ 4) * (32 * r ^ 4) := hm
            _ = 32 * (η * r ^ 2) * (2 * A * r) ^ 4 * r ^ 4 := by ring
        calc v ^ 5 ≤ 32 * μ r * L ^ 4 * r ^ 4 := hkey
          _ ≤ 32 * (η * r ^ 2) * (2 * A * r) ^ 4 * r ^ 4 := hmid
          _ = 32 * η * Cc * r ^ 10 := by rw [hCc]; ring
          _ ≤ ε ^ 5 * r ^ 10 := by
              have hm := mul_le_mul_of_nonneg_right h32ηC (show (0:ℝ) ≤ r^10 by positivity)
              linarith [hm]
          _ = (ε * r ^ 2) ^ 5 := by ring
      have hv0 : 0 ≤ v := by rw [hv]; exact abs_nonneg _
      have hfin : v ≤ ε * r ^ 2 :=
        (pow_le_pow_iff_left₀ hv0 hpr (by norm_num)).mp hv5
      rw [hv] at hfin
      exact hfin

end

end Commons.Analysis.MeasureTheory.Lebesgue
