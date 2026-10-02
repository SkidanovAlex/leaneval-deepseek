import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.approxEcal_end_out_small
import Submission.Work.PARIMPL2.Lavaurs.wout_model
import Submission.Work.PARIMPL2.LavaursA.exit_zeta_lo
import Submission.Work.PARIMPL2.LavaursA.log_le_lin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.LavaursA

open Work.PARIMPL (ParNormal chartZeta approxU ecalU)
open Work.PARIMPL2.Lavaurs (zeta0 uniform_model_coord slit_of_small_a)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The chart drift.**  For `A` bounding `‖m c − z₁‖` and `‖s c − s c₀‖`, with `‖s c‖ ≥ ‖s c₀‖/2`,
the chart value `chartZeta P c z` differs from the limiting `zeta0 P z` by at most
`2 (L A + A ‖s c₀‖)/‖s c₀‖²` whenever `‖z − z₁‖ ≤ L`. -/
theorem drift_zeta0_le {P : ParNormal d} {A L : ℝ} (hA : 0 < A) (hL : 0 ≤ L) {c z : ℂ}
    (hsc : P.s c ≠ 0) (hm : ‖P.m c - d.z₁‖ ≤ A) (hs : ‖P.s c - P.s c₀‖ ≤ A)
    (hs2 : ‖P.s c₀‖ / 2 ≤ ‖P.s c‖) (hzL : ‖z - d.z₁‖ ≤ L) :
    ‖chartZeta P c z - zeta0 P z‖ ≤ 2 * (L * A + A * ‖P.s c₀‖) / ‖P.s c₀‖ ^ 2 := by
  have hs0 : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hs0pos : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs0
  have hkey : chartZeta P c z - zeta0 P z
      = ((z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀) / (P.s c * P.s c₀) := by
    rw [chartZeta, Work.PARIMPL2.Lavaurs.zeta0]
    field_simp
    ring
  have hnum : ‖(z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀‖
      ≤ L * A + A * ‖P.s c₀‖ := by
    have hs' : ‖P.s c₀ - P.s c‖ ≤ A := by rwa [norm_sub_rev] at hs
    have h1 : ‖(z - d.z₁) * (P.s c₀ - P.s c)‖ ≤ L * A := by
      rw [norm_mul]
      exact mul_le_mul hzL hs' (norm_nonneg _) hL
    have h2 : ‖(d.z₁ - P.m c) * P.s c₀‖ ≤ A * ‖P.s c₀‖ := by
      rw [norm_mul, ← norm_sub_rev (P.m c) d.z₁]
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    calc _ ≤ ‖(z - d.z₁) * (P.s c₀ - P.s c)‖ + ‖(d.z₁ - P.m c) * P.s c₀‖ := norm_add_le _ _
      _ ≤ L * A + A * ‖P.s c₀‖ := add_le_add h1 h2
  have hden : ‖P.s c₀‖ / 2 * ‖P.s c₀‖ ≤ ‖P.s c‖ * ‖P.s c₀‖ :=
    mul_le_mul_of_nonneg_right hs2 (norm_nonneg _)
  have hdenpos : 0 < ‖P.s c₀‖ / 2 * ‖P.s c₀‖ := by positivity
  rw [hkey, norm_div, norm_mul]
  calc ‖(z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀‖ / (‖P.s c‖ * ‖P.s c₀‖)
      ≤ (L * A + A * ‖P.s c₀‖) / (‖P.s c‖ * ‖P.s c₀‖) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (L * A + A * ‖P.s c₀‖) / (‖P.s c₀‖ / 2 * ‖P.s c₀‖) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden
    _ = 2 * (L * A + A * ‖P.s c₀‖) / ‖P.s c₀‖ ^ 2 := by ring_nf

theorem wout_level {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀, ∀ H : ℝ, R ≥ 8 * (H + 1) → ∀ ε > 0, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z : ℂ,
        z ≠ d.z₁ →
        ‖Work.PARIMPL.chartZeta P c z‖ ≤ 4 / R →
        0 < (Work.PARIMPL.chartZeta P c z).re →
        (Work.PARIMPL.approxU P c z).re ∈ Set.Icc R (R + 2) →
        |(Work.PARIMPL.approxU P c z).im| ≤ H →
        1 / (4 * R) ≤ ‖Work.PARIMPL.chartZeta P c z‖ ∧
        ‖Work.PARIMPL.approxU P c z + Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)‖ ≤ ε := by
  obtain ⟨Rz, hRzpos, hzlo⟩ := exit_zeta_lo P
  set K : ℝ := ‖P.κ c₀‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hK0 : 0 ≤ K := hKpos.le
  obtain ⟨Rlog, hRlogpos, hRlog⟩ :=
    log_le_lin K 0 (4 * Real.exp 6) (4 / 9) hK0 (by positivity) (by norm_num)
  refine ⟨max 64 (max Rz Rlog), by positivity, ?_⟩
  intro R hR H hRH ε hε
  have hR64 : 64 ≤ R := le_trans (le_max_left 64 (max Rz Rlog)) hR
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hHle : H ≤ R / 8 := by linarith
  have hRzle : Rz ≤ R :=
    le_trans (le_trans (le_max_left Rz Rlog) (le_max_right 64 (max Rz Rlog))) hR
  have hRlogle : Rlog ≤ R :=
    le_trans (le_trans (le_max_right Rz Rlog) (le_max_right 64 (max Rz Rlog))) hR
  obtain ⟨ρz, hρzpos, hzlo'⟩ := hzlo R hRzle H hRH
  obtain ⟨C, hC0, hC⟩ := Work.PARIMPL2.approxEcal_end_out_small K hK0
  have hBIG : K * (Real.log (4 * R) + 6) ≤ (4 / 9) * R := by
    have h := hRlog R hRlogle
    have heq : Real.log (0 + (4 * Real.exp 6) * R) = Real.log (4 * R) + 6 := by
      have h1 : (0 : ℝ) + (4 * Real.exp 6) * R = (4 * R) * Real.exp 6 := by ring
      rw [h1, Real.log_mul (by positivity) (Real.exp_ne_zero 6), Real.log_exp]
    rwa [heq] at h
  set reLo : ℝ := 1 / (1024 * R) with hreLodef
  have hreLopos : 0 < reLo := by rw [hreLodef]; positivity
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    uniform_model_coord (reLo := reLo) hreLopos (P.κ c₀) (ε := ε / 2) (by linarith)
  set δ : ℝ := min δ₁ reLo / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle₁ : δ ≤ δ₁ / 2 := by rw [hδdef]; linarith [min_le_left δ₁ reLo]
  have hδlelo : δ ≤ reLo / 2 := by rw [hδdef]; linarith [min_le_right δ₁ reLo]
  set S : ℝ := ‖P.s c₀‖ with hSdef
  have hSpos : 0 < S := by
    rw [hSdef]; exact norm_pos_iff.mpr (P.s_ne c₀ (mem_ball_self P.hρ₀))
  set A : ℝ := min δ 1 * S / 32 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hAleS : A ≤ S := by
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    have h0 : 0 < min δ 1 := lt_min hδpos one_pos
    rw [hAdef]; nlinarith [hSpos, h1, h0]
  have hAle : A ≤ δ * S / 32 := by
    rw [hAdef]
    have h1 : min δ 1 ≤ δ := min_le_left _ _
    have := mul_le_mul_of_nonneg_right h1 hSpos.le
    linarith
  set lamMax : ℝ :=
    min (1 / (1048576 * R ^ 2)) (Real.sqrt (ε / (128 * (C + 1) * R ^ 3))) with hlamMaxdef
  have hlamMaxpos : 0 < lamMax := by
    rw [hlamMaxdef]; exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
  have hlamMax1 : lamMax ≤ 1 / (1048576 * R ^ 2) := by rw [hlamMaxdef]; exact min_le_left _ _
  have hlamMax2 : lamMax ≤ Real.sqrt (ε / (128 * (C + 1) * R ^ 3)) := by
    rw [hlamMaxdef]; exact min_le_right _ _
  have hf1 : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c ≤ lamMax :=
    (P.tendsto_lam c₀ P.a2₀ (by simpa using P.hρ₀)).eventually (Iic_mem_nhds hlamMaxpos)
  have hf2 : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.κ c - P.κ c₀‖ ≤ min δ 1 := by
    have hcont : ContinuousAt P.κ c₀ := P.cont_κ.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have h : ∀ᶠ c in 𝓝 c₀, P.κ c ∈ Metric.ball (P.κ c₀) (min δ 1) :=
      hcont.tendsto.eventually (Metric.ball_mem_nhds _ (lt_min hδpos one_pos))
    refine (h.filter_mono inf_le_left).mono ?_
    intro c hc
    rw [Metric.mem_ball, dist_eq_norm] at hc
    exact le_of_lt hc
  have hf3 : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.s c - P.s c₀‖ ≤ A := by
    have hcont : ContinuousAt P.s c₀ := P.cont_s.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have h : ∀ᶠ c in 𝓝 c₀, P.s c ∈ Metric.ball (P.s c₀) A :=
      hcont.tendsto.eventually (Metric.ball_mem_nhds _ hApos)
    refine (h.filter_mono inf_le_left).mono ?_
    intro c hc
    rw [Metric.mem_ball, dist_eq_norm] at hc
    exact le_of_lt hc
  have hf4 : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ := by
    have hcont : ContinuousAt P.s c₀ := P.cont_s.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have h : ∀ᶠ c in 𝓝 c₀, P.s c ∈ Metric.ball (P.s c₀) (‖P.s c₀‖ / 2) :=
      hcont.tendsto.eventually (Metric.ball_mem_nhds _ (by positivity))
    refine (h.filter_mono inf_le_left).mono ?_
    intro c hc
    rw [Metric.mem_ball, dist_eq_norm] at hc
    have h4 : ‖P.s c₀‖ - ‖P.s c‖ ≤ ‖P.s c₀ - P.s c‖ := by
      have habs := abs_le.mp (abs_norm_sub_norm_le (P.s c₀) (P.s c))
      linarith [habs.1]
    rw [norm_sub_rev (P.s c₀) (P.s c)] at h4
    linarith
  have hf5 : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.m c - d.z₁‖ ≤ A := by
    have hcont : ContinuousAt P.m c₀ := P.cont_m.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have h : ∀ᶠ c in 𝓝 c₀, P.m c ∈ Metric.ball (P.m c₀) A :=
      hcont.tendsto.eventually (Metric.ball_mem_nhds _ hApos)
    refine (h.filter_mono inf_le_left).mono ?_
    intro c hc
    rw [Metric.mem_ball, dist_eq_norm, P.m₀] at hc
    exact le_of_lt hc
  have hall : ∀ᶠ c in 𝓝[P.Nm] c₀,
      (P.lam c ≤ lamMax ∧ ‖P.κ c - P.κ c₀‖ ≤ min δ 1 ∧ ‖P.s c - P.s c₀‖ ≤ A ∧
        ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ ∧ ‖P.m c - d.z₁‖ ≤ A) :=
    hf1.and (hf2.and (hf3.and (hf4.and hf5)))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hall
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := hall
  refine ⟨min ρz ρ₂, lt_min hρzpos hρ₂pos, ?_⟩
  intro c hc z hz1 hζub hζre hUre hUim
  obtain ⟨hcNm, hcball⟩ := hc
  rw [mem_ball] at hcball
  have hcρz : c ∈ Metric.ball c₀ ρz :=
    mem_ball.mpr (lt_of_lt_of_le hcball (min_le_left _ _))
  have hcρ₂ : c ∈ Metric.ball c₀ ρ₂ :=
    mem_ball.mpr (lt_of_lt_of_le hcball (min_le_right _ _))
  obtain ⟨hlamle, hκclose, hsclose, hs2, hmclose⟩ :=
    hρ₂ (Metric.mem_ball.mp hcρ₂) hcNm
  set ζ : ℂ := chartZeta P c z with hζdef
  set U : ℂ := approxU P c z with hUdef
  have hub : ‖ζ‖ ≤ 4 / R := by rw [hζdef]; exact hζub
  have hre : 0 < ζ.re := by rw [hζdef]; exact hζre
  have hUmre : U.re ∈ Set.Icc R (R + 2) := by rw [hUdef]; exact hUre
  have hUmim : |U.im| ≤ H := by rw [hUdef]; exact hUim
  have hub' : ‖chartZeta P c z‖ ≤ 4 / R := by rw [← hζdef]; exact hζub
  have hlow : 1 / (4 * R) ≤ ‖ζ‖ := by
    have h := hzlo' c ⟨hcNm, hcρz⟩ z hub' hζre hUre hUim
    rwa [← hζdef] at h
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * R)) hlow
  have hζ64 : ‖ζ‖ ≤ 1 / 4 := by
    have h : (4 : ℝ) / R ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith [hub]
  have hζ1 : ‖ζ‖ ≤ 1 := by linarith [hub]
  have hζ4 : ‖ζ‖ ≤ 4 := by linarith [hub]
  have h1r : 1 / ‖ζ‖ ≤ 4 * R := by
    have hpos : 0 < (1 : ℝ) / (4 * R) := by positivity
    have h := one_div_le_one_div_of_le hpos hlow
    rwa [one_div_one_div] at h
  have hlogr : Real.log (1 / ‖ζ‖) ≤ Real.log (4 * R) := Real.log_le_log (by positivity) h1r
  have hlogr0 : 0 ≤ Real.log (1 / ‖ζ‖) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hζpos]; linarith [hζ1]
  have hκK : ‖P.κ c‖ ≤ K := by
    have h2 : ‖P.κ c - P.κ c₀‖ ≤ 1 := le_trans hκclose (min_le_right _ _)
    have h3 : ‖(P.κ c - P.κ c₀) + P.κ c₀‖ ≤ ‖P.κ c - P.κ c₀‖ + ‖P.κ c₀‖ := norm_add_le _ _
    rw [sub_add_cancel] at h3
    rw [hKdef]; linarith
  have hlampos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
  have ha_ne : P.a c ≠ 0 := by
    rw [P.a_of_mem_Nm hcNm]
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hlampos) Complex.I_ne_zero
  have hanorm : ‖P.a c‖ = P.lam c := by
    have h4 : ‖((P.lam c : ℝ) : ℂ)‖ = P.lam c :=
      (RCLike.norm_ofReal (K := ℂ) (P.lam c)).trans (abs_of_pos hlampos)
    rw [P.a_of_mem_Nm hcNm, norm_mul, Complex.norm_I, mul_one]
    exact h4
  have ha2 : ‖P.a c‖ ^ 2 ≤ reLo ^ 4 := by
    rw [hanorm]
    have h1 : P.lam c ≤ reLo ^ 2 := by
      have h1b : reLo ^ 2 = 1 / (1048576 * R ^ 2) := by
        rw [hreLodef, div_pow, one_pow]; ring_nf
      rw [h1b]
      exact le_trans hlamle hlamMax1
    calc (P.lam c) ^ 2 ≤ (reLo ^ 2) ^ 2 := pow_le_pow_left₀ hlampos.le h1 2
      _ = reLo ^ 4 := by ring
  have h4a : 4 * ‖P.a c‖ ≤ ‖ζ‖ := by
    rw [hanorm]
    have h2 : 4 * (1 / (1048576 * R ^ 2)) ≤ 1 / (4 * R) := by
      rw [show 4 * (1 / (1048576 * R ^ 2)) = 4 / (1048576 * R ^ 2) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hR1]
    have h3 : 4 * P.lam c ≤ 4 * (1 / (1048576 * R ^ 2)) :=
      mul_le_mul_of_nonneg_left (le_trans hlamle hlamMax1) (by norm_num)
    linarith [hlow]
  have hReInv : (4 / 9) * R ≤ (ζ⁻¹).re := by
    have hmodel := approxEcal_sub_inv_le (a := P.a c) (κ := P.κ c) (ζ := ζ) ha_ne hre hζ1 h4a
    have hUde : U = Work.Implosion.approxEcal (P.a c) (P.κ c)
        (Work.Implosion.ecalCoord (P.a c) ζ) := by
      rw [hUdef, Work.PARIMPL.approxU, Work.PARIMPL.ecalU]
    have hnorm : ‖(1 : ℂ) / ζ - U‖ ≤ 1 / (36 * ‖ζ‖) + ‖P.κ c‖ * (Real.log (1 / ‖ζ‖) + 6) := by
      rw [hUde, norm_sub_rev]
      exact hmodel
    have h3 : U.re - (1 / (36 * ‖ζ‖) + ‖P.κ c‖ * (Real.log (1 / ‖ζ‖) + 6)) ≤
        ((1 : ℂ) / ζ).re := by
      have h4 := Complex.abs_re_le_norm ((1 : ℂ) / ζ - U)
      have h5 : -‖(1 : ℂ) / ζ - U‖ ≤ ((1 : ℂ) / ζ - U).re := (abs_le.mp h4).1
      have h6 : ((1 : ℂ) / ζ - U).re = ((1 : ℂ) / ζ).re - U.re := Complex.sub_re _ _
      rw [h6] at h5
      linarith [h5, hnorm, hUmre.1]
    have h6 : 1 / (36 * ‖ζ‖) ≤ R / 9 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 36 * ‖ζ‖)]
      have h7 : 1 ≤ 4 * R * ‖ζ‖ := by
        have h8 : 1 / (4 * R) ≤ ‖ζ‖ := hlow
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * R)] at h8
        linarith [h8]
      rw [show (R / 9) * (36 * ‖ζ‖) = 4 * R * ‖ζ‖ by ring]
      exact h7
    have h7 : ‖P.κ c‖ * (Real.log (1 / ‖ζ‖) + 6) ≤ K * (Real.log (4 * R) + 6) :=
      mul_le_mul hκK (by linarith [hlogr]) (by linarith [hlogr0]) hK0
    have h8 : R - (R / 9 + K * (Real.log (4 * R) + 6)) ≤ ((1 : ℂ) / ζ).re := by
      linarith [h3, h6, h7, hUmre.1]
    have h9 : (4 / 9) * R ≤ ((1 : ℂ) / ζ).re := by linarith [h8, hBIG]
    rwa [one_div] at h9
  have hζre32 : 1 / (36 * R) ≤ ζ.re := by
    have hζne : ζ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hζpos
      exact lt_irrefl _ hζpos
    have hnsq : (‖ζ‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hζne)
    have h1 : ζ.re = ‖ζ‖ ^ 2 * (ζ⁻¹).re := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
      field_simp
    rw [h1]
    have h2 : (1 / (4 * R)) ^ 2 * ((4 / 9) * R) ≤ ‖ζ‖ ^ 2 * (ζ⁻¹).re :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hlow 2) hReInv (by positivity) (by positivity)
    have h3 : (1 / (4 * R)) ^ 2 * ((4 / 9) * R) = 1 / (36 * R) := by
      field_simp
      ring
    linarith [h2, h3.le]
  have hreLole : reLo ≤ ζ.re := by
    rw [hreLodef]
    have h2 : (1 : ℝ) / (1024 * R) ≤ 1 / (36 * R) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith [hζre32, h2]
  have hslit : Complex.sinh (P.a c * Work.Implosion.ecalCoord (P.a c) ζ) / P.a c ∈
      Complex.slitPlane :=
    slit_of_small_a (a := P.a c) ha_ne hreLopos hreLole hζ64 h4a ha2
  have hmain1 : ‖U - ((1 : ℂ) / ζ - P.κ c * Complex.log ζ)‖ ≤ ε / 2 := by
    have hh := hC (P.a c) (P.κ c) ζ ha_ne hκK hre hζ4 h4a hslit
    have hUde : U = Work.Implosion.approxEcal (P.a c) (P.κ c)
        (Work.Implosion.ecalCoord (P.a c) ζ) := by
      rw [hUdef, Work.PARIMPL.approxU, Work.PARIMPL.ecalU]
    rw [hUde]
    refine le_trans hh ?_
    rw [hanorm]
    have hζ3 : 0 < ‖ζ‖ ^ 3 := by positivity
    rw [div_le_iff₀ hζ3]
    have hlam2 : (P.lam c) ^ 2 ≤ ε / (128 * (C + 1) * R ^ 3) := by
      have h3 : lamMax ^ 2 ≤ ε / (128 * (C + 1) * R ^ 3) := by
        have hs := pow_le_pow_left₀ hlamMaxpos.le hlamMax2 2
        rwa [Real.sq_sqrt (by positivity)] at hs
      exact le_trans (pow_le_pow_left₀ hlampos.le hlamle 2) h3
    have ha : C * (P.lam c) ^ 2 ≤ C * (ε / (128 * (C + 1) * R ^ 3)) :=
      mul_le_mul_of_nonneg_left hlam2 hC0
    have hb : C * (ε / (128 * (C + 1) * R ^ 3)) ≤ (ε / 2) * (1 / (4 * R)) ^ 3 := by
      have hL : C * (ε / (128 * (C + 1) * R ^ 3)) =
          (ε / R ^ 3) * (C / (128 * (C + 1))) := by
        field_simp
      have hR' : (ε / 2) * (1 / (4 * R)) ^ 3 = (ε / R ^ 3) * (1 / 128) := by
        field_simp
        ring
      rw [hL, hR']
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hc : (1 / (4 * R)) ^ 3 ≤ ‖ζ‖ ^ 3 := pow_le_pow_left₀ (by positivity) hlow 3
    have hε2 : 0 ≤ ε / 2 := by linarith
    linarith [ha, hb, hc, hε2, mul_le_mul_of_nonneg_left hc hε2,
      mul_le_mul_of_nonneg_left hb hε2]
  have hzL : ‖z - d.z₁‖ ≤ 8 * S / R + A := by
    have hsc : P.s c ≠ 0 := P.s_ne c hcNm.1
    have h1 : z - d.z₁ = P.s c * ζ + (P.m c - d.z₁) := by
      rw [hζdef, chartZeta]
      field_simp
      ring
    have h2 : ‖P.s c‖ ≤ S + A := by
      have h3 := norm_add_le (P.s c - P.s c₀) (P.s c₀)
      rw [sub_add_cancel] at h3
      rw [hSdef]; linarith [hsclose]
    calc ‖z - d.z₁‖ = ‖P.s c * ζ + (P.m c - d.z₁)‖ := by rw [h1]
      _ ≤ ‖P.s c * ζ‖ + ‖P.m c - d.z₁‖ := norm_add_le _ _
      _ = ‖P.s c‖ * ‖ζ‖ + ‖P.m c - d.z₁‖ := by rw [norm_mul]
      _ ≤ (S + A) * (4 / R) + A := by
          have h3 : ‖P.s c‖ * ‖ζ‖ ≤ (S + A) * (4 / R) :=
            mul_le_mul h2 hub (norm_nonneg _) (by positivity)
          linarith [hmclose]
      _ ≤ 8 * S / R + A := by
          have h4 : (S + A) * (4 / R) ≤ 8 * S / R := by
            have h5 : (S + A) * (4 / R) = 4 * (S + A) / R := by ring
            rw [h5]
            apply div_le_div_of_nonneg_right _ hRpos.le
            linarith [hAleS]
          linarith [h4]
  have hdrift : ‖ζ - zeta0 P z‖ ≤ δ := by
    have hsc : P.s c ≠ 0 := P.s_ne c hcNm.1
    have hdr := drift_zeta0_le (P := P) (A := A) (L := 8 * S / R + A) hApos
      (by positivity) hsc hmclose hsclose hs2 hzL
    rw [← hSdef] at hdr
    refine le_trans hdr ?_
    have hL : (8 * S / R + A) * A + A * S ≤ A * (10 * S) := by
      have hR8 : 8 * S / R ≤ 8 * S := by
        rw [div_le_iff₀ hRpos]; nlinarith [hSpos, hR1]
      nlinarith [hR8, hAleS, hApos, hSpos]
    have h1 : 2 * (A * (10 * S)) / S ^ 2 = 20 * A / S := by
      field_simp
      ring
    have h2 : 20 * A / S ≤ 20 * (δ * S / 32) / S :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAle (by norm_num)) hSpos.le
    have h3 : 20 * (δ * S / 32) / S = 5 * δ / 8 := by field_simp; ring
    have h4 : 5 * δ / 8 ≤ δ := by linarith [hδpos]
    calc 2 * ((8 * S / R + A) * A + A * S) / S ^ 2
        ≤ 2 * (A * (10 * S)) / S ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [hL]
      _ = 20 * A / S := h1
      _ ≤ 20 * (δ * S / 32) / S := h2
      _ = 5 * δ / 8 := h3
      _ ≤ δ := h4
  have hzeta0re : reLo ≤ (zeta0 P z).re := by
    have h1 : (zeta0 P z).re ≥ ζ.re - ‖zeta0 P z - ζ‖ := by
      have h2 := Complex.abs_re_le_norm (zeta0 P z - ζ)
      have h3 : (zeta0 P z - ζ).re = (zeta0 P z).re - ζ.re := Complex.sub_re _ _
      rw [h3] at h2
      linarith [(abs_le.mp h2).1]
    have h4 : ‖zeta0 P z - ζ‖ ≤ δ := by rw [norm_sub_rev]; exact hdrift
    have h5 : 2 * reLo ≤ ζ.re := by
      rw [hreLodef]
      have h6 : 2 * (1 / (1024 * R)) = 1 / (512 * R) := by ring
      have h7 : (1 : ℝ) / (512 * R) ≤ 1 / (36 * R) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      linarith [hζre32, h6, h7]
    linarith [h1, h4, hδlelo, h5]
  have hzeta0norm : ‖zeta0 P z‖ ≤ 1 / 4 := by
    have h1 : ‖zeta0 P z‖ ≤ ‖ζ‖ + ‖zeta0 P z - ζ‖ := by
      calc ‖zeta0 P z‖ = ‖(zeta0 P z - ζ) + ζ‖ := by ring_nf
        _ ≤ ‖zeta0 P z - ζ‖ + ‖ζ‖ := norm_add_le _ _
        _ = ‖ζ‖ + ‖zeta0 P z - ζ‖ := by ring
    have h3 : δ ≤ 1 / (2048 * R) := by
      have h6 : reLo / 2 = 1 / (2048 * R) := by rw [hreLodef]; ring
      linarith [hδlelo, h6]
    have h4 : (4 : ℝ) / R + 1 / (2048 * R) ≤ 1 / 4 := by
      have h5 : (4 : ℝ) / R + 1 / (2048 * R) = (8193 / 2048) / R := by field_simp; ring
      rw [h5, div_le_iff₀ hRpos]
      linarith
    have h2 : ‖zeta0 P z - ζ‖ ≤ δ := by rw [norm_sub_rev]; exact hdrift
    linarith [h1, h2, h4, hub, h3]
  have hmain2 : ‖((1 : ℂ) / ζ - P.κ c * Complex.log ζ) -
      ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z))‖ ≤ ε / 2 := by
    have hd : dist (((ζ, P.κ c) : ℂ × ℂ)) (((zeta0 P z, P.κ c₀) : ℂ × ℂ)) < δ₁ := by
      rw [Prod.dist_eq]
      have h1 : dist ζ (zeta0 P z) ≤ δ := by rw [dist_eq_norm]; exact hdrift
      have h2 : dist (P.κ c) (P.κ c₀) ≤ δ := by
        rw [dist_eq_norm]; exact le_trans hκclose (min_le_left δ 1)
      exact lt_of_le_of_lt (max_le h1 h2) (by linarith [hδle₁, hδ₁pos])
    have h := hδ₁ (ζ, P.κ c) (zeta0 P z, P.κ c₀) hreLole hζ64 hzeta0re hzeta0norm
      (le_trans hκclose (min_le_right _ _)) (by simp) hd
    rw [dist_eq_norm] at h
    rw [one_div]
    exact le_of_lt h
  have hzeta0ne : zeta0 P z ≠ 0 := by
    intro h
    have hh := hzeta0re
    rw [h] at hh
    simp only [Complex.zero_re] at hh
    linarith [hreLopos]
  have harg : (zeta0 P z).arg ≠ Real.pi := by
    have hlt : |(zeta0 P z).arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (lt_of_lt_of_le hreLopos hzeta0re))
    have h2 := (abs_lt.mp hlt).2
    intro hc
    rw [hc] at h2
    linarith [Real.pi_pos]
  have hid : (zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z)
      = -Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z) := by
    have hw := Work.PARIMPL2.Lavaurs.w0_eq_neg_inv_zeta0 P hz1
    have h1 : Work.PARIMPL2.w0 P z = -((zeta0 P z)⁻¹) := by rw [hw]
    have h2 : -(Work.PARIMPL2.w0 P z) = (zeta0 P z)⁻¹ := by rw [hw]; ring
    have h3 : Complex.log (-(Work.PARIMPL2.w0 P z)) = -Complex.log (zeta0 P z) := by
      rw [h2]; exact Complex.log_inv _ harg
    rw [Work.PARIMPL2.approxCoordRep, h3, h1]
    ring
  refine ⟨?_, ?_⟩
  · exact hlow
  · have hsplit : U + Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)
        = (U - ((1 : ℂ) / ζ - P.κ c * Complex.log ζ)) +
          (((1 : ℂ) / ζ - P.κ c * Complex.log ζ) -
            ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z))) := by
      rw [hid]; ring
    have hcalc := calc ‖U + Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)‖
          = ‖(U - ((1 : ℂ) / ζ - P.κ c * Complex.log ζ)) +
              (((1 : ℂ) / ζ - P.κ c * Complex.log ζ) -
                ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z)))‖ := by rw [hsplit]
        _ ≤ ‖U - ((1 : ℂ) / ζ - P.κ c * Complex.log ζ)‖ +
              ‖((1 : ℂ) / ζ - P.κ c * Complex.log ζ) -
                ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z))‖ := norm_add_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add hmain1 hmain2
        _ = ε := by ring
    exact hcalc


end Work.PARIMPL2.LavaursA
