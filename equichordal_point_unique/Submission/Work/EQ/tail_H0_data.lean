import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroChain
import Submission.Work.EQ.HeteroRit
import Submission.Work.EQ.HeteroRk
import Submission.Work.EQ.germC_y_inverse
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.tail_identity_all

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- The tail data of the heteroclinic connection, with the size bound on the germ coordinate that the complex chain family needs. -/
theorem tail_H0_data {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}
    (hh : IsStableGerm a h r) (hΓ : IsHeteroclinic a h r Γ) :
    ∃ (N : ℕ) (t₀ δ δr ρ g0 : ℝ) (g : ℂ → ℂ),
      0 < t₀ ∧ 0 < δ ∧ 0 < ρ ∧ 0 < g0 ∧ t₀ + δ < δr ∧ t₀ + δ < ρ ∧
      AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρ) ∧
      AnalyticOnNhd ℂ g (Metric.ball 0 g0) ∧ g 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : ℂ) g0, (germC a h (g w)).2 = w) ∧
      (∀ (k : ℕ) (t : ℝ), 0 < t → t < δr → Rk a h k t = Rpt (Γ ((eqLam a)⁻¹ ^ k * t))) ∧
      (∀ v : ℂ, ‖v‖ < ρ → RegPair a (germC a h v) (germC a h ((eqLam a : ℂ) * v))) ∧
      (∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < δ → (Rk a h N u).2 ∈ Metric.ball (0 : ℂ) g0) ∧
      (∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < δ → ‖g ((Rk a h N u).2)‖ < ρ) ∧
      ∀ (n : ℕ) (u : ℂ), N ≤ n → ‖u - (t₀ : ℂ)‖ < δ →
        Rk a h n u = ugermC a h (((eqLam a : ℂ) ^ n) * ((((eqLam a : ℂ) ^ N)⁻¹) *
          g ((Rk a h N u).2))) := by
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlcne : (eqLam a : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hl0
  obtain ⟨ρg, hρg, hAnC, hC0, hRPc, hInjC, hderivY⟩ := germC_facts ha0 ha1 hh
  obtain ⟨ρy, g, hρy, hgan, hg0, hgy⟩ := germC_y_inverse ha0 ha1 hh
  obtain ⟨ρf, hρf, hfwd⟩ := invBranch_ugermC ha0 ha1 hh hΓ
  obtain ⟨δr, hδr, hRkreal⟩ := Rk_real ha0 ha1 hh hΓ
  obtain ⟨ε, s, hε, hspos, _, _, hstail⟩ := gamma_tail ha0 ha1 hh hΓ
  -- ## thresholds for the two continuity arguments
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ w : ℂ, ‖w‖ < δ₁ → ‖g w‖ < min ρg ρf / 2 := by
    have hpos : 0 < min ρg ρf / 2 := by positivity
    have hgc : ContinuousAt g 0 := (hgan 0 (by simpa using hρy)).continuousAt
    have hev : ∀ᶠ w in 𝓝 (0 : ℂ), g w ∈ Metric.ball (0 : ℂ) (min ρg ρf / 2) := by
      have ht := hgc.tendsto
      rw [hg0] at ht
      exact ht (Metric.ball_mem_nhds 0 hpos)
    obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨δ₁, hδ₁pos, fun w hw => ?_⟩
    have hb : w ∈ Metric.ball (0 : ℂ) δ₁ := by rwa [Metric.mem_ball, dist_zero_right]
    have h2 : g w ∈ Metric.ball (0 : ℂ) (min ρg ρf / 2) := hδ₁sub hb
    rwa [Metric.mem_ball, dist_zero_right] at h2
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ w : ℂ, ‖w‖ < δ₀ → ‖(germC a h w).2‖ < min ρy δ₁ / 4 := by
    have hpos : 0 < min ρy δ₁ / 4 := by positivity
    have hcont : ContinuousAt (fun w : ℂ => (germC a h w).2) 0 := by
      have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρg := by simpa using hρg
      exact continuous_snd.continuousAt.comp ((hAnC 0 hmem).continuousAt)
    have hev : ∀ᶠ w in 𝓝 (0 : ℂ), (germC a h w).2 ∈ Metric.ball (0 : ℂ) (min ρy δ₁ / 4) := by
      have ht := hcont.tendsto
      rw [show (germC a h 0).2 = 0 by simp [hC0]] at ht
      exact ht (Metric.ball_mem_nhds 0 hpos)
    obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨δ₀, hδ₀pos, fun w hw => ?_⟩
    have hb : w ∈ Metric.ball (0 : ℂ) δ₀ := by rwa [Metric.mem_ball, dist_zero_right]
    have h2 : (germC a h w).2 ∈ Metric.ball (0 : ℂ) (min ρy δ₁ / 4) := hδ₀sub hb
    rwa [Metric.mem_ball, dist_zero_right] at h2
  -- ## the interval and the accumulation point
  set M₀ : ℝ := min δr ρg with hM₀
  have hM₀pos : 0 < M₀ := by rw [hM₀]; exact lt_min hδr hρg
  have hM₀δr : M₀ ≤ δr := by rw [hM₀]; exact min_le_left _ _
  have hM₀ρg : M₀ ≤ ρg := by rw [hM₀]; exact min_le_right _ _
  set α : ℝ := M₀ / 4 with hα
  set β : ℝ := M₀ / 2 with hβ
  have hαpos : 0 < α := by rw [hα]; positivity
  have hαβ : α < β := by rw [hα, hβ]; linarith
  have hβδr : β < δr := by
    have hb : β < M₀ := by rw [hβ]; linarith
    exact lt_of_lt_of_le hb hM₀δr
  have hβρg : β < ρg := by
    have hb : β < M₀ := by rw [hβ]; linarith
    exact lt_of_lt_of_le hb hM₀ρg
  obtain ⟨c, hcpos, t₀, hαt₀, ht₀β, hacc⟩ := exists_sublevel_accPt s hαβ
  have ht₀pos : 0 < t₀ := lt_of_lt_of_le hαpos hαt₀
  have ht₀δr : t₀ < δr := lt_of_le_of_lt ht₀β hβδr
  have ht₀ρg : t₀ < ρg := lt_of_le_of_lt ht₀β hβρg
  -- ## the level `N`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (eqLam a) ^ N * c < min δ₀ (min ε (min ρy ρg)) := by
    have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ n * c) atTop (𝓝 0) := by
      have hh' := (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hl0) hl1).mul_const c
      simpa using hh'
    have hpos : 0 < min δ₀ (min ε (min ρy ρg)) := by positivity
    exact (hlim.eventually (eventually_lt_nhds hpos)).exists
  have hthr : ∀ t : ℝ, α ≤ t → t ≤ β → s t < c →
      (eqLam a) ^ N * s t < δ₀ ∧ (eqLam a) ^ N * s t < ε ∧
      (eqLam a) ^ N * s t < ρy ∧ (eqLam a) ^ N * s t < ρg := by
    intro t _ _ hst
    have h1 : (eqLam a) ^ N * s t < (eqLam a) ^ N * c :=
      mul_lt_mul_of_pos_left hst (pow_pos hl0 N)
    have h2 : (eqLam a) ^ N * s t < min δ₀ (min ε (min ρy ρg)) := lt_trans h1 hN
    exact ⟨lt_of_lt_of_le h2 (min_le_left _ _),
      lt_of_lt_of_le h2 (le_trans (min_le_right _ _) (min_le_left _ _)),
      lt_of_lt_of_le h2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))),
      lt_of_lt_of_le h2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))⟩
  -- ## norm of the parameter
  have hwr : ∀ t : ℝ, 0 < t → ‖((eqLam a : ℂ) ^ N * (s t : ℂ))‖ = (eqLam a) ^ N * s t := by
    intro t ht
    rw [← Complex.ofReal_pow (eqLam a) N, ← Complex.ofReal_mul,
      Complex.norm_of_nonneg (le_of_lt (mul_pos (pow_pos hl0 N) (hspos t ht)))]
  -- ## the real identity at level `N`
  have hreal_id : ∀ t : ℝ, α ≤ t → t ≤ β → s t < c →
      Rk a h N (t : ℂ) = ugermC a h ((eqLam a : ℂ) ^ N * (s t : ℂ)) ∧
      g ((Rk a h N (t : ℂ)).2) = (eqLam a : ℂ) ^ N * (s t : ℂ) := by
    intro t hαt hβt hst
    obtain ⟨hltδ₀, hltε, hltρy, hltρg⟩ := hthr t hαt hβt hst
    have ht0 : 0 < t := lt_of_lt_of_le hαpos hαt
    have htdr : t < δr := lt_of_le_of_lt hβt hβδr
    have hAN : Rk a h N (t : ℂ) = ugermC a h ((eqLam a : ℂ) ^ N * (s t : ℂ)) :=
      (hRkreal N t ht0 htdr).trans (hstail t ht0 N hltε)
    refine ⟨hAN, ?_⟩
    have hy : (Rk a h N (t : ℂ)).2 = (germC a h ((eqLam a : ℂ) ^ N * (s t : ℂ))).2 := by
      rw [hAN]; exact ugermC_snd_tia a h _
    have hwδ₀ : ‖((eqLam a : ℂ) ^ N * (s t : ℂ))‖ < δ₀ := by
      rw [hwr t ht0]; exact hltδ₀
    have hylt : ‖(Rk a h N (t : ℂ)).2‖ < min ρy δ₁ / 4 := by
      rw [hy]; exact hδ₀ _ hwδ₀
    have hybd : ‖(Rk a h N (t : ℂ)).2‖ < δ₁ :=
      lt_of_lt_of_le hylt (by have := min_le_right ρy δ₁; linarith)
    have hyball : (Rk a h N (t : ℂ)).2 ∈ Metric.ball (0 : ℂ) ρy := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hylt (by have := min_le_left ρy δ₁; linarith)
    have hwρg : ((eqLam a : ℂ) ^ N * (s t : ℂ)) ∈ Metric.ball (0 : ℂ) ρg := by
      rw [Metric.mem_ball, dist_zero_right, hwr t ht0]; exact hltρg
    have hgw : g ((Rk a h N (t : ℂ)).2) ∈ Metric.ball (0 : ℂ) ρg := by
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖g ((Rk a h N (t : ℂ)).2)‖ < min ρg ρf / 2 := hδ₁ _ hybd
        _ < ρg := by have := min_le_left ρg ρf; linarith
    refine hInjC hgw hwρg ?_
    change (germC a h (g ((Rk a h N (t : ℂ)).2))).2 =
      (germC a h ((eqLam a : ℂ) ^ N * (s t : ℂ))).2
    rw [hgy _ hyball]
    exact hy
  -- ## analyticity at `t₀`
  have hAan : AnalyticAt ℂ (fun u : ℂ => Rk a h N u) (t₀ : ℂ) := by
    have hmem : (t₀ : ℂ) ∈ Metric.ball (0 : ℂ) ρg := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht₀pos]
      exact ht₀ρg
    refine analyticAt_Rk (k := N) hh (hAnC (t₀ : ℂ) hmem) ?_
    intro j hj
    rw [hRkreal j t₀ ht₀pos ht₀δr]
    exact bsq_subO1_Rpt_mem_slitPlane a (hΓ.2.2.1 ((eqLam a)⁻¹ ^ j * t₀) (by positivity))
  have hyNan : AnalyticAt ℂ (fun u : ℂ => (Rk a h N u).2) (t₀ : ℂ) :=
    AnalyticAt.comp (f := fun u : ℂ => Rk a h N u) (x := (t₀ : ℂ))
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (Rk a h N (t₀ : ℂ))) hAan
  have hyb : ‖(Rk a h N (t₀ : ℂ)).2‖ ≤ min ρy δ₁ / 4 := by
    have hSbd : ∀ u ∈ Complex.ofReal '' {t : ℝ | α ≤ t ∧ t ≤ β ∧ s t < c},
        ‖(Rk a h N u).2‖ ≤ min ρy δ₁ / 4 := by
      rintro u ⟨t, ht, rfl⟩
      have ht0 : 0 < t := lt_of_lt_of_le hαpos ht.1
      have hwδ₀ : ‖((eqLam a : ℂ) ^ N * (s t : ℂ))‖ < δ₀ := by
        rw [hwr t ht0]; exact (hthr t ht.1 ht.2.1 ht.2.2).1
      rw [show (Rk a h N ((t : ℂ))).2 = (germC a h ((eqLam a : ℂ) ^ N * (s t : ℂ))).2 by
        rw [(hreal_id t ht.1 ht.2.1 ht.2.2).1]; exact ugermC_snd_tia a h _]
      exact le_of_lt (hδ₀ _ hwδ₀)
    haveI : NeBot (𝓝[≠] (t₀ : ℂ) ⊓
        Filter.principal (Complex.ofReal '' {t : ℝ | α ≤ t ∧ t ≤ β ∧ s t < c})) := hacc
    have htend : Tendsto (fun u : ℂ => ‖(Rk a h N u).2‖)
        (𝓝[≠] (t₀ : ℂ) ⊓ Filter.principal (Complex.ofReal '' {t : ℝ | α ≤ t ∧ t ≤ β ∧ s t < c}))
        (𝓝 ‖(Rk a h N (t₀ : ℂ)).2‖) :=
      (hyNan.continuousAt.norm.tendsto).mono_left (le_trans inf_le_left nhdsWithin_le_nhds)
    have hev : ∀ᶠ u in 𝓝[≠] (t₀ : ℂ) ⊓
        Filter.principal (Complex.ofReal '' {t : ℝ | α ≤ t ∧ t ≤ β ∧ s t < c}),
        ‖(Rk a h N u).2‖ ≤ min ρy δ₁ / 4 := by
      rw [Filter.eventually_inf_principal]
      filter_upwards with u hu
      exact hSbd u hu
    exact le_of_tendsto htend hev
  have hyball₀ : (Rk a h N (t₀ : ℂ)).2 ∈ Metric.ball (0 : ℂ) ρy := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hyb (by have := min_le_left ρy δ₁; linarith)
  have hVan : AnalyticAt ℂ (fun u : ℂ => g ((Rk a h N u).2)) (t₀ : ℂ) :=
    AnalyticAt.comp (f := fun u : ℂ => (Rk a h N u).2) (x := (t₀ : ℂ))
      (hgan ((Rk a h N (t₀ : ℂ)).2) hyball₀) hyNan
  have hVb : ‖g ((Rk a h N (t₀ : ℂ)).2)‖ < min ρg ρf / 2 :=
    hδ₁ _ (lt_of_le_of_lt hyb (by have := min_le_right ρy δ₁; linarith))
  have hVball₀ : g ((Rk a h N (t₀ : ℂ)).2) ∈ Metric.ball (0 : ℂ) ρg := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hVb (by have := min_le_left ρg ρf; linarith)
  have hCan : AnalyticAt ℂ (fun u : ℂ => ugermC a h (g ((Rk a h N u).2))) (t₀ : ℂ) := by
    have hgerm : AnalyticAt ℂ (fun u : ℂ => germC a h (g ((Rk a h N u).2))) (t₀ : ℂ) :=
      AnalyticAt.comp (f := fun u : ℂ => g ((Rk a h N u).2)) (x := (t₀ : ℂ))
        (hAnC (g ((Rk a h N (t₀ : ℂ)).2)) hVball₀) hVan
    have h1 : AnalyticAt ℂ (fun u : ℂ => (germC a h (g ((Rk a h N u).2))).1) (t₀ : ℂ) :=
      AnalyticAt.comp (f := fun u : ℂ => germC a h (g ((Rk a h N u).2))) (x := (t₀ : ℂ))
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _) hgerm
    have h2 : AnalyticAt ℂ (fun u : ℂ => (germC a h (g ((Rk a h N u).2))).2) (t₀ : ℂ) :=
      AnalyticAt.comp (f := fun u : ℂ => germC a h (g ((Rk a h N u).2))) (x := (t₀ : ℂ))
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _) hgerm
    have heq : (fun u : ℂ => ugermC a h (g ((Rk a h N u).2)))
        = fun u : ℂ => (-(germC a h (g ((Rk a h N u).2))).1,
            (germC a h (g ((Rk a h N u).2))).2) := by
      funext u; rfl
    rw [heq]
    exact h1.neg.prod h2
  -- ## identity theorem
  obtain ⟨ρA, hρApos, hAon⟩ := hAan.exists_ball_analyticOnNhd
  obtain ⟨ρC, hρCpos, hCon⟩ := hCan.exists_ball_analyticOnNhd
  set ρU : ℝ := min ρA ρC with hρU
  have hρUpos : 0 < ρU := lt_min hρApos hρCpos
  have hAonU : AnalyticOnNhd ℂ (fun u : ℂ => Rk a h N u) (Metric.ball (t₀ : ℂ) ρU) :=
    hAon.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hConU : AnalyticOnNhd ℂ (fun u : ℂ => ugermC a h (g ((Rk a h N u).2)))
      (Metric.ball (t₀ : ℂ) ρU) :=
    hCon.mono (Metric.ball_subset_ball (min_le_right _ _))
  have hmemU : (t₀ : ℂ) ∈ Metric.ball (t₀ : ℂ) ρU := by simp [hρUpos]
  have hfreq : ∃ᶠ u in 𝓝[≠] (t₀ : ℂ), Rk a h N u = ugermC a h (g ((Rk a h N u).2)) := by
    have hS : ∃ᶠ u in 𝓝[≠] (t₀ : ℂ),
        u ∈ Complex.ofReal '' {t : ℝ | α ≤ t ∧ t ≤ β ∧ s t < c} := by
      rw [Filter.frequently_iff_neBot]
      exact hacc
    refine hS.mono (fun u hu => ?_)
    obtain ⟨t, ht, rfl⟩ := hu
    rw [(hreal_id t ht.1 ht.2.1 ht.2.2).2]
    exact (hreal_id t ht.1 ht.2.1 ht.2.2).1
  have hEqOn : Set.EqOn (fun u : ℂ => Rk a h N u)
      (fun u : ℂ => ugermC a h (g ((Rk a h N u).2))) (Metric.ball (t₀ : ℂ) ρU) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hAonU hConU
      Metric.isPreconnected_ball hmemU hfreq
  -- ## smallness of the parameter on a ball
  obtain ⟨ρV, hρVpos, hρV⟩ : ∃ ρV : ℝ, 0 < ρV ∧
      ∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < ρV → ‖g ((Rk a h N u).2)‖ < ρf := by
    have hlt : ‖g ((Rk a h N (t₀ : ℂ)).2)‖ < ρf :=
      lt_of_lt_of_le hVb (by have := min_le_right ρg ρf; linarith)
    have hev : ∀ᶠ u in 𝓝 (t₀ : ℂ), ‖g ((Rk a h N u).2)‖ < ρf :=
      (hVan.continuousAt.norm.tendsto).eventually (eventually_lt_nhds hlt)
    obtain ⟨ρV, hρVpos, hρVsub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨ρV, hρVpos, fun u hu => hρVsub ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact hu
  -- ## the two size bounds near `t₀`
  obtain ⟨r₇, hr₇pos, hr₇⟩ : ∃ r₇ : ℝ, 0 < r₇ ∧
      ∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < r₇ → (Rk a h N u).2 ∈ Metric.ball (0 : ℂ) ρy := by
    have hev : ∀ᶠ u in 𝓝 (t₀ : ℂ), (Rk a h N u).2 ∈ Metric.ball (0 : ℂ) ρy :=
      hyNan.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hyball₀)
    obtain ⟨r₇, hr₇pos, hr₇sub⟩ := Metric.mem_nhds_iff.mp hev
    exact ⟨r₇, hr₇pos, fun u hu => hr₇sub (by rw [Metric.mem_ball, dist_eq_norm]; exact hu)⟩
  obtain ⟨r₈, hr₈pos, hr₈⟩ : ∃ r₈ : ℝ, 0 < r₈ ∧
      ∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < r₈ → ‖g ((Rk a h N u).2)‖ < ρg := by
    have hlt : ‖g ((Rk a h N (t₀ : ℂ)).2)‖ < ρg :=
      lt_of_lt_of_le hVb (by have := min_le_left ρg ρf; linarith)
    have hev : ∀ᶠ u in 𝓝 (t₀ : ℂ), ‖g ((Rk a h N u).2)‖ < ρg :=
      (hVan.continuousAt.norm.tendsto).eventually (eventually_lt_nhds hlt)
    obtain ⟨r₈, hr₈pos, hr₈sub⟩ := Metric.mem_nhds_iff.mp hev
    exact ⟨r₈, hr₈pos, fun u hu => hr₈sub (by rw [Metric.mem_ball, dist_eq_norm]; exact hu)⟩
  -- ## the final radius
  set δ : ℝ := min (min ρU ρV)
    (min r₇ (min r₈ (min ((δr - t₀) / 2) ((ρg - t₀) / 2)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hρUpos hρVpos)
      (lt_min hr₇pos (lt_min hr₈pos (lt_min (by linarith) (by linarith))))
  have hδU : δ ≤ ρU := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδV : δ ≤ ρV := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδr₇ : δ ≤ r₇ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδr₈ : δ ≤ r₈ := by
    rw [hδdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδδr : δ ≤ (δr - t₀) / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδρg : δ ≤ (ρg - t₀) / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have ht₀δδr : t₀ + δ < δr := by linarith [ht₀δr, hδδr]
  have ht₀δρg : t₀ + δ < ρg := by linarith [ht₀ρg, hδρg]
  have hRP' : ∀ v : ℂ, ‖v‖ < ρg →
      RegPair a (germC a h v) (germC a h ((eqLam a : ℂ) * v)) :=
    fun v hv => (hRPc v (by rw [Metric.mem_ball, dist_zero_right]; exact hv)).1
  have hbnd₇ : ∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < δ → (Rk a h N u).2 ∈ Metric.ball (0 : ℂ) ρy :=
    fun u hu => hr₇ u (lt_of_lt_of_le hu hδr₇)
  have hbnd₈ : ∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < δ → ‖g ((Rk a h N u).2)‖ < ρg :=
    fun u hu => hr₈ u (lt_of_lt_of_le hu hδr₈)
  -- ## the iteration
  have hiter : ∀ (k : ℕ) (w : ℂ),
      (∀ j : ℕ, j < k → (eqLam a : ℂ) ^ j * w ∈ Metric.ball (0 : ℂ) ρf) →
      ((invBranch a true)^[k]) (ugermC a h w) = ugermC a h ((eqLam a : ℂ) ^ k * w) := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [Function.iterate_succ_apply', ih w (fun j hj => hw j (lt_trans hj (Nat.lt_succ_self k))),
        hfwd ((eqLam a : ℂ) ^ k * w) (hw k (Nat.lt_succ_self k))]
      congr 1
      rw [pow_succ]; ring
  have hRkiter : ∀ (k : ℕ) (u : ℂ),
      Rk a h (N + k) u = ((invBranch a true)^[k]) (Rk a h N u) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [show N + (k + 1) = (N + k) + 1 by ring, Rk_succ, ih u, Function.iterate_succ_apply']
  have hpow : ∀ n : ℕ, N ≤ n →
      (eqLam a : ℂ) ^ n * ((eqLam a : ℂ) ^ N)⁻¹ = (eqLam a : ℂ) ^ (n - N) := by
    intro n hn
    have h1 : (eqLam a : ℂ) ^ n = (eqLam a : ℂ) ^ N * (eqLam a : ℂ) ^ (n - N) := by
      rw [← pow_add, Nat.add_sub_of_le hn]
    rw [h1, mul_assoc, mul_comm ((eqLam a : ℂ) ^ (n - N)) (((eqLam a : ℂ) ^ N)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero N hlcne), one_mul]
  -- ## assembly
  refine ⟨N, t₀, δ, δr, ρg, ρy, g, ht₀pos, hδpos, hρg, hρy, ht₀δδr, ht₀δρg,
    hAnC, hgan, hg0, hgy, hRkreal, hRP', hbnd₇, hbnd₈, ?_⟩
  intro n u hn hu
  have huU : u ∈ Metric.ball (t₀ : ℂ) ρU := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hu hδU
  have huV : ‖g ((Rk a h N u).2)‖ < ρf := hρV u (lt_of_lt_of_le hu hδV)
  have hbase : Rk a h N u = ugermC a h (g ((Rk a h N u).2)) := hEqOn huU
  have hball : ∀ j : ℕ, j < n - N →
      (eqLam a : ℂ) ^ j * g ((Rk a h N u).2) ∈ Metric.ball (0 : ℂ) ρf := by
    intro j hj
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖(eqLam a : ℂ) ^ j * g ((Rk a h N u).2)‖
        = ‖(eqLam a : ℂ) ^ j‖ * ‖g ((Rk a h N u).2)‖ := norm_mul _ _
      _ = (eqLam a) ^ j * ‖g ((Rk a h N u).2)‖ := by
          rw [norm_pow, Complex.norm_of_nonneg (le_of_lt hl0)]
      _ ≤ ‖g ((Rk a h N u).2)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (le_of_lt hl0) (le_of_lt hl1))
      _ < ρf := huV
  calc Rk a h n u
      = Rk a h (N + (n - N)) u := by rw [Nat.add_sub_of_le hn]
    _ = ((invBranch a true)^[n - N]) (Rk a h N u) := hRkiter (n - N) u
    _ = ((invBranch a true)^[n - N]) (ugermC a h (g ((Rk a h N u).2))) :=
          congrArg (fun w => ((invBranch a true)^[n - N]) w) hbase
    _ = ugermC a h ((eqLam a : ℂ) ^ (n - N) * g ((Rk a h N u).2)) :=
          hiter (n - N) (g ((Rk a h N u).2)) hball
    _ = ugermC a h ((eqLam a : ℂ) ^ n * (((eqLam a : ℂ) ^ N)⁻¹ * g ((Rk a h N u).2))) :=
          congrArg (ugermC a h) (by rw [← mul_assoc, hpow n hn])

end

end Work.EQ
