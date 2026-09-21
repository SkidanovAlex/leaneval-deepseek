import Mathlib

namespace Work.VolterraLong.C1

theorem data_diff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b)
    {G0s Gs : ℝ → E → E} {Θ0 Θ0s Θ Θs : ℝ → ℝ → E → E} {Ξ0s Ξs : ℝ → E}
    {Z₀ Z : ℝ → E} {L LG L1 K1 ε : ℝ} (hε : 0 < ε) (hK1 : 0 ≤ K1)
    (hL : 0 ≤ L) (hLG : 0 ≤ LG) (hL1 : 0 ≤ L1)
    (hZ : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) (hK1ε : K1 * ε ≤ 1)
    (hZ_cont : ContinuousOn Z (Set.Icc a b)) (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΘ0s_cont : Continuous (fun p : ℝ × ℝ × E => Θ0s p.1 p.2.1 p.2.2))
    (hGs_lip : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ s) 1, ‖Gs s z - Gs s z'‖ ≤ LG * ‖z - z'‖)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hΘs_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θs s σ z - Θs s σ z'‖ ≤ L1 * ‖z - z'‖)
    (hGs_c : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1, dist (Gs s z) (G0s s z) < ε)
    (hΘ_c : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      dist (Θ s σ z) (Θ0 s σ z) < ε)
    (hΘs_c : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      dist (Θs s σ z) (Θ0s s σ z) < ε)
    (hΞs_c : ∀ s ∈ Set.Icc a b, dist (Ξs s) (Ξ0s s) < ε) :
    ∀ s ∈ Set.Icc a b, ‖(- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)‖
      ≤ ((1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1) * ε := by
  intro s hs
  have hsa : a ≤ s := hs.1
  have hsb : s ≤ b := hs.2
  -- ### distance facts from the perturbation hypothesis
  have hZ1 : ∀ σ ∈ Set.Icc a b, dist (Z σ) (Z₀ σ) ≤ 1 := by
    intro σ hσ
    have h := hZ σ hσ
    linarith
  have hZmem : ∀ σ ∈ Set.Icc a b, Z σ ∈ Metric.closedBall (Z₀ σ) 1 :=
    fun σ hσ => Metric.mem_closedBall.mpr (hZ1 σ hσ)
  have hZ₀mem : ∀ σ ∈ Set.Icc a b, Z₀ σ ∈ Metric.closedBall (Z₀ σ) 1 :=
    fun σ hσ => Metric.mem_closedBall.mpr (by simp)
  have hZnorm : ∀ σ ∈ Set.Icc a b, ‖Z σ - Z₀ σ‖ ≤ K1 * ε := by
    intro σ hσ
    have h := hZ σ hσ
    rwa [dist_eq_norm] at h
  -- ### the smallness of each of the four differences
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
  -- ### pointwise bound for the integrand
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
  -- ### continuity / integrability of the two integral kernels
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
  -- ### bound for the difference of the two integrals
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
  -- ### the four-term triangle inequality
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


end Work.VolterraLong.C1
