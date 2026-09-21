import Mathlib
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.VolterraLong.volterra_long_exists_C1
import Submission.Work.OddVolterra.Window.window_core_exists
import Submission.Work.OddVolterra.WinData.window_state_continuous
import Submission.Work.OddVolterra.WinData.smooth_upgrade
import Submission.Work.OddVolterra.WinData.contDiffOn_Ioi_extension
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddVolterra.WinData.fderiv_godd_close_box
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.Window.Kvec_deriv_close
import Submission.Work.OddVolterra.Existence.window_deriv_close_est

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

lemma one_sub_tau : (1 : ℝ) - tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]

lemma profileX_eq_sqrt (s : ℝ) : Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) := rfl

lemma baseState_zero (s : ℝ) : baseState s 0 = Commons.Geometry.Ulam.profileX s := rfl
lemma baseState_one (s : ℝ) : baseState s 1 = Commons.Geometry.Ulam.profileX s := rfl
lemma baseState_two (s : ℝ) : baseState s 2 = deriv Commons.Geometry.Ulam.profileX s := rfl
lemma baseState_three (s : ℝ) : baseState s 3 = deriv Commons.Geometry.Ulam.profileX s := rfl

/-- The ball profile stays above `7/10` on the slope interval `[1/4, 9/10]`. -/
lemma profileX_ge_seven_tenths {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (9 / 10)) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  have hsq : s ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by nlinarith [hs.1, hs.2]
  rw [profileX_eq_sqrt, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  have h1 : Real.sqrt (1 + s ^ 2) ≤ 10 / 7 := by
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((10 / 7 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 10 / 7 := Real.sqrt_sq (by norm_num)
  nlinarith [h1]

/-- The profile's slope is at most `-1/10` on `[1/4, 9/10]`. -/
lemma deriv_profileX_le_neg_tenth {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (9 / 10)) :
    deriv Commons.Geometry.Ulam.profileX s ≤ -(1 / 10 : ℝ) := by
  have hp := profileX_ge_seven_tenths hs
  rw [Commons.Geometry.Ulam.deriv_profileX_eq]
  have hspos : (0 : ℝ) < s / (1 + s ^ 2) := by
    apply div_pos (by linarith [hs.1]); positivity
  have hle : (4 / 17 : ℝ) ≤ s / (1 + s ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith [hs.1] : (0 : ℝ) ≤ s - 1 / 4)
      (by linarith [hs.2] : s - 4 ≤ 0)]
  have h1 : (4 / 17 : ℝ) * (7 / 10) ≤ s / (1 + s ^ 2) * Commons.Geometry.Ulam.profileX s :=
    mul_le_mul hle hp (by norm_num) (le_of_lt hspos)
  have h2 : (4 / 17 : ℝ) * (7 / 10) = 14 / 85 := by norm_num
  linarith [h1, h2]


/-! ## Generic facts about the first-slot partial derivative -/

lemma hasDerivAt_curry {F : ℝ × St → St} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (s : ℝ) (z : St) :
    HasDerivAt (fun u : ℝ => F (u, z)) (fderiv ℝ F (s, z) (1, 0)) s := by
  have hc : HasDerivAt (fun u : ℝ => (u, z)) (1, 0) s := by
    simpa using (hasDerivAt_id s).prodMk (hasDerivAt_const (c := z) (x := s))
  have hd : DifferentiableAt ℝ F (s, z) := hF.contDiffAt.differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt s hc

lemma deriv_curry_eq {F : ℝ × St → St} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (s : ℝ) (z : St) :
    deriv (fun u : ℝ => F (u, z)) s = fderiv ℝ F (s, z) (1, 0) :=
  (hasDerivAt_curry hF s z).deriv

lemma continuous_deriv_curry {F : ℝ × St → St} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun p : ℝ × St => deriv (fun u : ℝ => F (u, p.2)) p.1) := by
  have h1 : Continuous (fun p : ℝ × St => fderiv ℝ F p) := hF.continuous_fderiv (by simp)
  have h2 : Continuous (fun p : ℝ × St => (fderiv ℝ F p) (1, 0)) := h1.clm_apply continuous_const
  refine h2.congr ?_
  intro p
  exact (deriv_curry_eq hF p.1 p.2).symm

/-! ## The linearization of the clamped base datum at the ball state -/

lemma clamped_lin (n : ℕ) (hn : 1 ≤ n) :
    ∃ (A : ℝ → St ≃L[ℝ] St) (B : ℝ), 0 < B ∧
      (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        (A s : St →L[ℝ] St) = fderiv ℝ (fun z => WinData.Gcl n 0 s z) (baseState s)) ∧
      ContinuousOn (fun s => ((A s).symm : St →L[ℝ] St)) (Set.Icc (1 / 4 : ℝ) (19 / 20)) ∧
      (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ‖((A s).symm : St →L[ℝ] St)‖ ≤ B) := by
  obtain ⟨A, B, hB, hAspec, hAcont, hAb⟩ :=
    odd_linearization n hn (1 / 4) (19 / 20) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨A, B, hB, ?_, hAcont, hAb⟩
  intro s hs
  rw [hAspec s hs]
  have hEv : (fun z : St => WinData.Gcl n 0 s z) =ᶠ[𝓝 (baseState s)]
      (fun z : St => Godd n 0 s z) := by
    filter_upwards [Metric.ball_mem_nhds (baseState s) (by norm_num : (0 : ℝ) < 1 / 2)]
      with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact WinData.Gcl_eq_Godd (n := n) (h := fun _ : ℝ => (0 : ℝ)) hs (le_of_lt hz)
  rw [Filter.EventuallyEq.fderiv_eq hEv]

/-! ## The data-difference bound with state ball of radius `ρ` -/

theorem data_diff_bound_r {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b ρ : ℝ} (hab : a ≤ b)
    {G0s Gs : ℝ → E → E} {Θ0 Θ0s Θ Θs : ℝ → ℝ → E → E} {Ξ0s Ξs : ℝ → E}
    {Z₀ Z : ℝ → E} {L LG L1 K1 ε : ℝ} (hε : 0 < ε) (hK1 : 0 ≤ K1) (hρ : 0 ≤ ρ)
    (hL : 0 ≤ L) (hLG : 0 ≤ LG) (hL1 : 0 ≤ L1)
    (hZ : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) (hK1ε : K1 * ε ≤ ρ)
    (hZ_cont : ContinuousOn Z (Set.Icc a b)) (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΘ0s_cont : Continuous (fun p : ℝ × ℝ × E => Θ0s p.1 p.2.1 p.2.2))
    (hGs_lip : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) ρ,
      ∀ z' ∈ Metric.closedBall (Z₀ s) ρ, ‖Gs s z - Gs s z'‖ ≤ LG * ‖z - z'‖)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) ρ,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) ρ, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hΘs_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) ρ,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) ρ, ‖Θs s σ z - Θs s σ z'‖ ≤ L1 * ‖z - z'‖)
    (hGs_c : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) ρ, dist (Gs s z) (G0s s z) < ε)
    (hΘ_c : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) ρ,
      dist (Θ s σ z) (Θ0 s σ z) < ε)
    (hΘs_c : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) ρ,
      dist (Θs s σ z) (Θ0s s σ z) < ε)
    (hΞs_c : ∀ s ∈ Set.Icc a b, dist (Ξs s) (Ξ0s s) < ε) :
    ∀ s ∈ Set.Icc a b, ‖(- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)‖
      ≤ ((1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1) * ε := by
  intro s hs
  have hsa : a ≤ s := hs.1
  have hsb : s ≤ b := hs.2
  have hZ1 : ∀ σ ∈ Set.Icc a b, dist (Z σ) (Z₀ σ) ≤ ρ := by
    intro σ hσ
    linarith [hZ σ hσ, hK1ε]
  have hZmem : ∀ σ ∈ Set.Icc a b, Z σ ∈ Metric.closedBall (Z₀ σ) ρ :=
    fun σ hσ => Metric.mem_closedBall.mpr (hZ1 σ hσ)
  have hZ₀mem : ∀ σ ∈ Set.Icc a b, Z₀ σ ∈ Metric.closedBall (Z₀ σ) ρ :=
    fun σ hσ => Metric.mem_closedBall.mpr (by rw [dist_self]; exact hρ)
  have hZnorm : ∀ σ ∈ Set.Icc a b, ‖Z σ - Z₀ σ‖ ≤ K1 * ε := by
    intro σ hσ
    have h := hZ σ hσ
    rwa [dist_eq_norm] at h
  have hG : ‖Gs s (Z s) - G0s s (Z₀ s)‖ ≤ (1 + LG * K1) * ε := by
    have hlip := hGs_lip s hs (Z s) (hZmem s hs) (Z₀ s) (hZ₀mem s hs)
    have hcl := hGs_c s hs (Z₀ s) (hZ₀mem s hs)
    rw [dist_eq_norm] at hcl
    have h2 : LG * ‖Z s - Z₀ s‖ ≤ LG * (K1 * ε) :=
      mul_le_mul_of_nonneg_left (hZnorm s hs) hLG
    have h1 : ‖Gs s (Z s) - G0s s (Z₀ s)‖ ≤ LG * ‖Z s - Z₀ s‖ + ε := by
      have ht := dist_triangle (Gs s (Z s)) (Gs s (Z₀ s)) (G0s s (Z₀ s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have h3 : LG * (K1 * ε) + ε = (1 + LG * K1) * ε := by ring
    linarith
  have hΘb : ‖Θ s s (Z s) - Θ0 s s (Z₀ s)‖ ≤ (1 + L * K1) * ε := by
    have hlip := hΘ_lip s hs s hs (Z s) (hZmem s hs) (Z₀ s) (hZ₀mem s hs)
    have hcl := hΘ_c s hs s hs (Z₀ s) (hZ₀mem s hs)
    rw [dist_eq_norm] at hcl
    have h2 : L * ‖Z s - Z₀ s‖ ≤ L * (K1 * ε) :=
      mul_le_mul_of_nonneg_left (hZnorm s hs) hL
    have h1 : ‖Θ s s (Z s) - Θ0 s s (Z₀ s)‖ ≤ L * ‖Z s - Z₀ s‖ + ε := by
      have ht := dist_triangle (Θ s s (Z s)) (Θ s s (Z₀ s)) (Θ0 s s (Z₀ s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have h3 : L * (K1 * ε) + ε = (1 + L * K1) * ε := by ring
    linarith
  have hΞb : ‖Ξs s - Ξ0s s‖ ≤ 1 * ε := by
    have h := hΞs_c s hs
    rw [dist_eq_norm] at h
    linarith
  have hpoint : ∀ x ∈ Set.Icc s b,
      ‖Θs s x (Z x) - Θ0s s x (Z₀ x)‖ ≤ (1 + L1 * K1) * ε := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := ⟨hsa.trans hx.1, hx.2⟩
    have hlip := hΘs_lip s hs x hxab (Z x) (hZmem x hxab) (Z₀ x) (hZ₀mem x hxab)
    have hcl := hΘs_c s hs x hxab (Z₀ x) (hZ₀mem x hxab)
    rw [dist_eq_norm] at hcl
    have h2 : L1 * ‖Z x - Z₀ x‖ ≤ L1 * (K1 * ε) :=
      mul_le_mul_of_nonneg_left (hZnorm x hxab) hL1
    have h1 : ‖Θs s x (Z x) - Θ0s s x (Z₀ x)‖ ≤ L1 * ‖Z x - Z₀ x‖ + ε := by
      have ht := dist_triangle (Θs s x (Z x)) (Θs s x (Z₀ x)) (Θ0s s x (Z₀ x))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have h3 : L1 * (K1 * ε) + ε = (1 + L1 * K1) * ε := by ring
    linarith
  have hmapsZ : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc s b) :=
    ContinuousOn.prodMk continuousOn_const
      (ContinuousOn.prodMk continuousOn_id
        (hZ_cont.mono (fun x hx => ⟨hsa.trans hx.1, hx.2⟩)))
  have hmapsZ₀ : ContinuousOn (fun σ : ℝ => (s, σ, Z₀ σ)) (Set.Icc s b) :=
    ContinuousOn.prodMk continuousOn_const
      (ContinuousOn.prodMk continuousOn_id
        (hZ₀_cont.mono (fun x hx => ⟨hsa.trans hx.1, hx.2⟩)))
  have hFcont : ContinuousOn (fun σ : ℝ => Θs s σ (Z σ)) (Set.Icc s b) :=
    hΘs_cont.continuousOn.comp hmapsZ (fun _ _ => Set.mem_univ _)
  have hF0cont : ContinuousOn (fun σ : ℝ => Θ0s s σ (Z₀ σ)) (Set.Icc s b) :=
    hΘ0s_cont.continuousOn.comp hmapsZ₀ (fun _ _ => Set.mem_univ _)
  have hFint : IntervalIntegrable (fun σ : ℝ => Θs s σ (Z σ)) MeasureTheory.volume s b :=
    hFcont.intervalIntegrable_of_Icc hsb
  have hF0int : IntervalIntegrable (fun σ : ℝ => Θ0s s σ (Z₀ σ)) MeasureTheory.volume s b :=
    hF0cont.intervalIntegrable_of_Icc hsb
  have hint : ‖(∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))‖
      ≤ (b - a + 1) * (1 + L1 * K1) * ε := by
    rw [← intervalIntegral.integral_sub hFint hF0int]
    have hbound : ∀ x ∈ Set.uIoc s b, ‖Θs s x (Z x) - Θ0s s x (Z₀ x)‖ ≤ (1 + L1 * K1) * ε := by
      intro x hx
      rw [Set.uIoc_of_le hsb] at hx
      exact hpoint x (Set.Ioc_subset_Icc_self hx)
    have hni := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := b)
      (C := (1 + L1 * K1) * ε) hbound
    have habs : |b - s| = b - s := abs_of_nonneg (by linarith)
    rw [habs] at hni
    have hC : 0 ≤ (1 + L1 * K1) * ε := mul_nonneg (by linarith [hL1, hK1, mul_nonneg hL1 hK1]) (le_of_lt hε)
    have hbs : b - s ≤ b - a + 1 := by linarith
    have hmono := mul_le_mul_of_nonneg_left hbs hC
    have heq : ((1 + L1 * K1) * ε) * (b - a + 1) = (b - a + 1) * (1 + L1 * K1) * ε := by ring
    linarith
  have hb1 : ‖-(Gs s (Z s) - G0s s (Z₀ s))‖ ≤ (1 + LG * K1) * ε := by
    rw [norm_neg]; exact hG
  have hb2 : ‖-(Θ s s (Z s) - Θ0 s s (Z₀ s))‖ ≤ (1 + L * K1) * ε := by
    rw [norm_neg]; exact hΘb
  have htri : ∀ u1 u2 u3 u4 : E, ‖u1 + u2 + u3 + u4‖ ≤ ‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖ := by
    intro u1 u2 u3 u4
    have h1 : ‖u1 + u2 + u3 + u4‖ ≤ ‖u1 + u2 + u3‖ + ‖u4‖ := norm_add_le _ _
    have h2 : ‖u1 + u2 + u3‖ ≤ ‖u1 + u2‖ + ‖u3‖ := norm_add_le _ _
    have h3 : ‖u1 + u2‖ ≤ ‖u1‖ + ‖u2‖ := norm_add_le _ _
    linarith
  have htri_inst :
      ‖-(Gs s (Z s) - G0s s (Z₀ s)) + (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
        + ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ)))
        + (Ξs s - Ξ0s s)‖
      ≤ ‖-(Gs s (Z s) - G0s s (Z₀ s))‖ + ‖-(Θ s s (Z s) - Θ0 s s (Z₀ s))‖
        + ‖(∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))‖
        + ‖Ξs s - Ξ0s s‖ :=
    htri (-(Gs s (Z s) - G0s s (Z₀ s))) (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
      ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))) (Ξs s - Ξ0s s)
  have key : (- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)
      = -(Gs s (Z s) - G0s s (Z₀ s)) + (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
        + ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ)))
        + (Ξs s - Ξ0s s) := by abel
  rw [key]
  calc ‖-(Gs s (Z s) - G0s s (Z₀ s)) + (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
        + ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ)))
        + (Ξs s - Ξ0s s)‖
      ≤ ‖-(Gs s (Z s) - G0s s (Z₀ s))‖ + ‖-(Θ s s (Z s) - Θ0 s s (Z₀ s))‖
        + ‖(∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))‖
        + ‖Ξs s - Ξ0s s‖ := htri_inst
    _ ≤ (1 + LG * K1) * ε + (1 + L * K1) * ε + (b - a + 1) * (1 + L1 * K1) * ε + 1 * ε := by
        linarith [hb1, hb2, hint, hΞb]
    _ = ((1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1) * ε := by ring

/-- **The `C¹`-closeness of the window solution.**

For every smooth bump `h` which is `C^{n+3}`-small enough there is a constant `K`, depending only
on `n`, such that *any* state `Z` which is `C^∞` on `(0,∞)`, solves the paper's system on
`(1/4,1)` and agrees with the ball's state beyond `9/10` satisfies

`dist (deriv Z s) (deriv baseState s) ≤ K * ε` for `s ∈ [1/4, 19/20]`.

This is the derivative-closeness (NRZ Lemma 8) statement for the odd transition-slope system: it is
obtained by differentiating the system in `s` and comparing the linearised equation with the
unperturbed one. -/
theorem window_deriv_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ K ε₁ : ℝ, 0 < K ∧ 0 < ε₁ ∧ ε₁ ≤ 1 / 100 ∧
      ∀ (h : ℝ → ℝ) (Z : ℝ → St) (ε : ℝ), 0 < ε → ε ≤ ε₁ →
        IsSmallFlatBumpThree n ε h → h 0 = 0 →
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)) →
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Godd n h s (Z s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) + Xi n h s) →
        (∀ s : ℝ, 1 - tau ≤ s → Z s = baseState s) →
        (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ), dist (Z s) (baseState s) ≤ 9 / 20) →
        ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
          dist (deriv Z s) (deriv (baseState : ℝ → St) s) ≤ K * ε := by
  exact Work.OddVolterra.Existence.window_deriv_close_est n hn

theorem window_C1_state (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h → h 0 = 0 → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)) ∧
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) ∧
        (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) ∧
        (∀ s : ℝ, 1 / 4 ≤ s →
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2000 ∧
          dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
            ≤ 1 / 2000) ∧
        (∀ s : ℝ, 1 / 4 ≤ s →
          deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
        (∀ s : ℝ, 1 / 4 ≤ s → 0 < Z s 0 ∧ 0 < Z s 1 ∧ Z s 2 < 0 ∧ Z s 3 < 0) := by
  have hL1 : WinData.ThetaMCloseBox n (1 / 4) (19 / 20) (1 / 2) :=
    WinData.thetaM_close_box n hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hL4 : WinData.FderivGoddCloseBox n (1 / 4) (19 / 20) (1 / 2) :=
    WinData.fderiv_godd_close_box n hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  obtain ⟨K, ε₁, hKpos, hε₁pos, hε₁100, hC1⟩ := window_deriv_close n hn
  set r : ℝ := min (min (1 / 2000) (1 / (2000 * (K + 1)))) ε₁ with hrdef
  have hrpos : 0 < r := lt_min (lt_min (by norm_num) (by positivity)) hε₁pos
  have hr2000 : r ≤ 1 / 2000 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrK : r ≤ 1 / (2000 * (K + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrε₁ : r ≤ ε₁ := min_le_right _ _
  have hr100 : r ≤ 1 / 100 := le_trans hrε₁ hε₁100
  have hKr : K * r ≤ 1 / 2000 := by
    have h1 : K * r ≤ K * (1 / (2000 * (K + 1))) := mul_le_mul_of_nonneg_left hrK hKpos.le
    have h2 : K * (1 / (2000 * (K + 1))) ≤ 1 / 2000 := by
      have h4 : (0 : ℝ) < 2000 * (K + 1) := by positivity
      have he : K * (1 / (2000 * (K + 1))) = K / (2000 * (K + 1)) := by ring
      rw [he, div_le_iff₀ h4]
      linarith
    linarith
  obtain ⟨εc, hεcpos, Hc⟩ := WinData.window_state_continuous n hn hL1 hL4 r hrpos
  set ε : ℝ := min εc r with hεdef
  have hεpos : 0 < ε := lt_min hεcpos hrpos
  have hεεc : ε ≤ εc := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro h hbump h0 hne
  obtain ⟨hh, hsupp, hjet, hflat⟩ := hbump
  have hsuppI : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) :=
    fun x hx => ⟨(hsupp hx).1.le, (hsupp hx).2.le⟩
  have hε100 : ε ≤ 1 / 100 := le_trans hεr hr100
  have hsmallC : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ εc :=
    fun k hk s => le_trans (hjet k (by omega) s) hεεc
  have hsmall100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hε100
  obtain ⟨Z, hZc, hZeq, hZtail, hZd, hZder⟩ := Hc h hh hsuppI hflat hsmallC h0 hne
  have hZc' : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :=
    hZc.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  have hZd' : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
      dist (Z s) (baseState s) ≤ 1 / 2 := fun s hs =>
    le_trans (hZd s ⟨hs.1, le_trans hs.2 (by norm_num)⟩) (le_trans hr2000 (by norm_num))
  have hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :=
    WinData.smooth_upgrade n hn h hh hsuppI hflat hsmall100 Z hZc' hZeq hZtail hZd'
  have hZtail910 : ∀ s : ℝ, 9 / 10 ≤ s → Z s = baseState s := by
    intro s hs; exact hZtail s (by rw [one_sub_tau]; exact hs)
  have h914 : (9 / 10 : ℝ) ≤ 1 - tau := by rw [one_sub_tau]
  obtain ⟨Zf, hZfsm, hZfeq, hZfder⟩ :=
    WinData.contDiffOn_Ioi_extension hZsm hZtail910
      (fun s hs => (hZder s hs.le).1) (fun s hs => (hZder s hs.le).2)
  have hsys : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Godd n h s (Zf s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zf σ)) + Xi n h s := by
    intro s hs
    have hs14 : (1 / 4 : ℝ) ≤ s := le_of_lt hs.1
    rw [hZfeq s hs14, hZeq s hs]
    congr 1
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le hs.2.le] at hσ
    rw [hZfeq σ (le_trans hs14 hσ.1)]
  have htail' : ∀ s : ℝ, 1 - tau ≤ s → Zf s = baseState s := by
    intro s hs
    rw [hZfeq s (by linarith [h914, hs]), hZtail s hs]
  have hbd' : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ), dist (Zf s) (baseState s) ≤ 9 / 20 := by
    intro s hs
    rw [hZfeq s hs.1]
    exact le_trans (hZd s ⟨hs.1, le_trans hs.2 (by norm_num)⟩)
      (le_trans hr2000 (by norm_num))
  have hbump' : IsSmallFlatBumpThree n ε h := ⟨hh, hsupp, hjet, hflat⟩
  refine ⟨Zf, hZfsm, hsys, htail', ?_, hZfder, ?_⟩
  · -- the two closeness bounds
    intro s hs
    refine ⟨?_, ?_⟩
    · rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · rw [hZfeq s hs]
        exact le_trans (hZd s ⟨hs, by linarith⟩) hr2000
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), dist_self]
        norm_num
    · rcases le_or_gt s (19 / 20 : ℝ) with hle | hgt
      · have h1 := hC1 h Zf ε hεpos (le_trans hεr hrε₁) hbump' h0 hZfsm
          hsys htail' hbd' s ⟨hs, hle⟩
        have h2 : K * ε ≤ 1 / 2000 := by
          have h3 : K * ε ≤ K * r := mul_le_mul_of_nonneg_left hεr hKpos.le
          linarith
        linarith
      · have hev : Zf =ᶠ[𝓝 s] baseState := by
          filter_upwards [isOpen_Ioi.mem_nhds (by linarith : (9 / 10 : ℝ) < s)] with u hu
          have hu' : (9 / 10 : ℝ) < u := hu
          rw [hZfeq u (by linarith)]
          exact hZtail910 u (le_of_lt hu)
        rw [Filter.EventuallyEq.deriv_eq hev, dist_self]
        norm_num
  · -- the sign pattern
    intro s hs
    have hcomp : ∀ i : Fin 4, dist (Zf s i) (baseState s i) ≤ 1 / 2000 := by
      intro i
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := hZd s ⟨hs, by linarith⟩
        have h' : dist (Z s) (baseState s) ≤ 1 / 2000 := le_trans h hr2000
        rw [dist_eq_norm] at h'
        have hb := norm_le_pi_norm (Z s - baseState s) i
        rw [Pi.sub_apply] at hb
        have h1 : Zf s i - baseState s i = (Z s - baseState s) i := by
          rw [hZfeq s hs]; rfl
        rw [Real.dist_eq, h1, ← Real.norm_eq_abs]
        exact le_trans hb h'
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), dist_self]
        norm_num
    have hget : ∀ i : Fin 4, |Zf s i - baseState s i| ≤ 1 / 2000 := by
      intro i
      have h := hcomp i
      rwa [Real.dist_eq] at h
    have h0pos : (0 : ℝ) < Zf s 0 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 0)).1
        have hp := profileX_ge_seven_tenths ⟨hs, hle⟩
        rw [baseState_zero] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_zero, profileX_eq_sqrt]
        exact div_pos one_pos (Real.sqrt_pos.mpr (by positivity))
    have h1pos : (0 : ℝ) < Zf s 1 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 1)).1
        have hp := profileX_ge_seven_tenths ⟨hs, hle⟩
        rw [baseState_one] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_one, profileX_eq_sqrt]
        exact div_pos one_pos (Real.sqrt_pos.mpr (by positivity))
    have h2neg : Zf s 2 < 0 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 2)).2
        have hd := deriv_profileX_le_neg_tenth ⟨hs, hle⟩
        rw [baseState_two] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_two]
        exact Commons.Geometry.Ulam.deriv_profileX_neg (by linarith)
    have h3neg : Zf s 3 < 0 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 3)).2
        have hd := deriv_profileX_le_neg_tenth ⟨hs, hle⟩
        rw [baseState_three] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_three]
        exact Commons.Geometry.Ulam.deriv_profileX_neg (by linarith)
    exact ⟨h0pos, h1pos, h2neg, h3neg⟩

end

end Work.OddVolterra.Existence
