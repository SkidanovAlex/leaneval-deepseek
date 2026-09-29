import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.slitPieces
import Submission.Work.A14D.glue_three_LZ
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.A14D.log_structured_vanishes
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.uh_not_holo_at_ninth
import Submission.Work.A14D.hol_sol_at_one_smul
import Submission.Work.A14D.D_local_at_one
import Submission.Work.A14D.Dzc_helpers
import Submission.Work.A14D.exists_sol_LZ_Om1_of_ball_one
import Submission.Work.A14D.logCoeff_uh_cont_ne_zero

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators Topology
open Work.A14D

/-- If a solution `A` of `LZ = 0` on an open set `Ω ∋` (a germ of) `1` agrees with a solution `D`
of `LZ = 0` on the slit plane on a nonempty open piece of `ball 1 δ ∩ Om1`, then `A` itself solves
`LZ = 0` on the whole ball `ball 1 δ`. -/
lemma Dzc_LZ_zero_of_eqOn_Om1 {δ : ℝ} (hδ : 0 < δ) {A D : ℂ → ℂ}
    (hAd : DifferentiableOn ℂ A (Metric.ball (1 : ℂ) δ))
    (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hag : ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ Om1, D z = A z) :
    ∀ z ∈ Metric.ball (1 : ℂ) δ, LZ A z = 0 := by
  have hVo : IsOpen (Metric.ball (1 : ℂ) δ ∩ Om1) :=
    Metric.isOpen_ball.inter Dzc_isOpen_Om1
  -- `z ↦ LZ A z` is analytic on the ball
  have hd1 : DifferentiableOn ℂ (deriv A) (Metric.ball (1 : ℂ) δ) :=
    hAd.deriv Metric.isOpen_ball
  have hd2 : DifferentiableOn ℂ (deriv (deriv A)) (Metric.ball (1 : ℂ) δ) :=
    hd1.deriv Metric.isOpen_ball
  have hAna : AnalyticOnNhd ℂ (fun z => LZ A z) (Metric.ball (1 : ℂ) δ) := by
    have hd : DifferentiableOn ℂ (fun z => LZ A z) (Metric.ball (1 : ℂ) δ) := by
      have hPZ : DifferentiableOn ℂ PZ (Metric.ball (1 : ℂ) δ) := by unfold PZ; fun_prop
      have hPZ' : DifferentiableOn ℂ PZ' (Metric.ball (1 : ℂ) δ) := by unfold PZ'; fun_prop
      have hRZ : DifferentiableOn ℂ RZ (Metric.ball (1 : ℂ) δ) := by unfold RZ; fun_prop
      have he : (fun z => LZ A z)
          = fun z => PZ z * deriv (deriv A) z + PZ' z * deriv A z + RZ z * A z := by
        funext z; rw [LZ_def]
      rw [he]
      exact ((hPZ.mul hd2).add (hPZ'.mul hd1)).add (hRZ.mul hAd)
    exact hd.analyticOnNhd Metric.isOpen_ball
  -- it vanishes on the open set `ball 1 δ ∩ Om1`
  have hvanish : ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ Om1, LZ A z = 0 := by
    intro z hz
    have hev : A =ᶠ[𝓝 z] D := by
      filter_upwards [hVo.mem_nhds hz] with w hw
      exact (hag w hw).symm
    rw [LZ_congr_eventuallyEq hev]
    exact hDL z hz.2
  -- a point of the (nonempty, open) intersection
  obtain ⟨z₀, hz₀⟩ := Dzc_nonempty_ball_one_inter_Om1 hδ
  intro z hz
  exact hAna.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    ((convex_ball (1 : ℂ) δ).isPreconnected) hz₀.1
    (by filter_upwards [hVo.mem_nhds hz₀] with w hw; exact hvanish w hw) hz

/-- **The core log-coefficient argument.**  Let `f` solve `LZ = 0` on the slit plane `Om1` and
agree near `1` with a multiple of the holomorphic solution `uh` at `1` (i.e. `f = c·uh` on
`ball 1 δ ∩ Om1`).  If the log coefficient of `f` at `1/9` from above vanishes (i.e. `f` agrees
with a function holomorphic on `ball (1/9) δu` on `halfU δu`), then `f` vanishes on `Om1`. -/
theorem Dzc_sol_logCoeff_zero {δ : ℝ} {δu : ℝ} (hδ : 0 < δ) (hδ89 : δ < 8 / 9) {c : ℂ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Om1) (hfL : ∀ z ∈ Om1, LZ f z = 0)
    (hag : ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ Om1, f z = c * uh z)
    {y9 : ℂ → ℂ} (hY : Y9 y9 δu)
    (hLog : LogCoeff y9 δu (halfU δu) f 0) :
    ∀ z ∈ Om1, f z = 0 := by
  have hYc := hY
  obtain ⟨hδu_pos, -, hy9d, hy9ne, -⟩ := hYc
  have hδ89le : δ ≤ 8 / 9 := le_of_lt hδ89
  -- the global continuation `UH` of `uh` to `Om1`
  obtain ⟨UH, hUHd, hUHL, hUHuh⟩ : ∃ UH : ℂ → ℂ, DifferentiableOn ℂ UH Om1 ∧
      (∀ z ∈ Om1, LZ UH z = 0) ∧ ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ Om1, UH z = uh z := by
    exact exists_sol_LZ_Om1_of_ball_one hδ hδ89
      (uh_ode.1.mono (Metric.ball_subset_ball hδ89le))
      (fun z hz => uh_ode.2.2 z (Metric.ball_subset_ball hδ89le hz))
  -- `f = c·UH` on `Om1`
  have hfUH : ∀ z ∈ Om1, f z = c * UH z := by
    refine Dzc_eqOn_of_agree_open (U := Om1) (V := Metric.ball (1 : ℂ) δ ∩ Om1)
      Dzc_isOpen_Om1 Dzc_isPreconnected_Om1 (fun z hz => Dzc_PZ_ne_zero_of_mem_Om1 hz)
      hf (hUHd.const_mul c) hfL ?_ Set.inter_subset_right
      (Metric.isOpen_ball.inter Dzc_isOpen_Om1) (Dzc_nonempty_ball_one_inter_Om1 hδ) ?_
    · intro z hz
      rw [Dzc_LZ_const_mul Dzc_isOpen_Om1 hUHd hz, hUHL z hz, mul_zero]
    · intro z hz
      show f z = c * UH z
      rw [hag z hz, hUHuh z hz]
  -- `UH = uh` on `Om1 ∩ ball 1 (8/9)`
  have hUHuh89 : ∀ z ∈ Om1 ∩ Metric.ball (1 : ℂ) (8 / 9), UH z = uh z := by
    refine Dzc_eqOn_of_agree_open (U := Om1 ∩ Metric.ball (1 : ℂ) (8 / 9))
      (V := Metric.ball (1 : ℂ) δ ∩ Om1)
      (Dzc_isOpen_Om1.inter Metric.isOpen_ball) (Dzc_isPreconnected_Om1_inter_ball (8 / 9))
      (fun z hz => Dzc_PZ_ne_zero_of_mem_Om1 hz.1)
      (hUHd.mono Set.inter_subset_left) (uh_ode.1.mono Set.inter_subset_right)
      (fun z hz => hUHL z hz.1) (fun z hz => uh_ode.2.2 z hz.2)
      (by intro z hz; exact ⟨hz.2, Metric.ball_subset_ball hδ89le hz.1⟩)
      (Metric.isOpen_ball.inter Dzc_isOpen_Om1) (Dzc_nonempty_ball_one_inter_Om1 hδ)
      (by intro z hz; exact hUHuh z hz)
  -- the log coefficient of `UH` at `1/9` is non-zero
  obtain ⟨lam, hlamne, hlam⟩ : ∃ lam : ℂ, lam ≠ 0 ∧ LogCoeff y9 δu (halfU δu) UH lam :=
    logCoeff_uh_cont_ne_zero hY UH hUHd hUHL hUHuh89
  obtain ⟨h, hhd, hheq⟩ := hLog
  obtain ⟨h', h'hd, h'eq⟩ := hlam
  -- the key relation on `halfU δu`
  have hkey : ∀ z ∈ halfU δu,
      (c * lam * y9 z) * Complex.log (z - ninth) + (c * h' z - h z) = 0 := by
    intro z hz
    have hzOm1 : z ∈ Om1 := Or.inl (ne_of_gt hz.2)
    have h1 := hheq z hz
    have h2 := h'eq z hz
    have h3 := hfUH z hzOm1
    rw [h3, h2] at h1
    linear_combination h1
  -- extend off the real axis and apply the log-structured vanishing
  have hext : ∀ z ∈ Metric.ball ninth δu, z.im ≠ 0 →
      (fun w => c * lam * y9 w) z * Complex.log (z - ninth)
        + (fun w => c * h' w - h w) z = 0 :=
    Dzc_log_structured_extend hδu_pos (hy9d.const_mul (c * lam))
      ((h'hd.mono Set.sdiff_subset).const_mul c |>.sub (hhd.mono Set.sdiff_subset)) hkey
  have hGzero := log_structured_vanishes hδu_pos (hy9d.const_mul (c * lam))
    ((h'hd.mono Set.sdiff_subset).const_mul c |>.sub (hhd.mono Set.sdiff_subset)) hext
  have hcl : c * lam = 0 := by
    have h9 := hGzero ninth (Metric.mem_ball_self hδu_pos)
    rcases mul_eq_zero.mp h9 with h | h
    · exact h
    · exact absurd h hy9ne
  have hc0 : c = 0 := (mul_eq_zero.mp hcl).resolve_right hlamne
  intro z hz
  rw [hfUH z hz, hc0, zero_mul]

/-- In the `A14D` setting: if `c = 0` and the log coefficient `κU` of the jump `D` at `1/9` from
above vanishes, then `D` vanishes identically on the slit plane `Om1`. -/
theorem D_zero_of_c_eq_zero (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (hc : c = 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hκ : κU = 0) :
    ∀ z ∈ Om1, D z = 0 := by
  -- `D` extends holomorphically across `1` (`D_local_at_one` with `c = 0`)
  obtain ⟨δ₁, hδ₁, A, hAd, hAeq⟩ := D_local_at_one a b c h hb HU HL hHU hHL D hD hDL hDj
  have hAeq' : ∀ z ∈ Metric.ball (1 : ℂ) δ₁ ∩ Om1, D z = A z := by
    intro z hz
    have h := hAeq z hz
    rw [hc] at h
    simpa using h
  -- hence `A` solves the homogeneous equation on `ball 1 δ₁`
  have hLZA : ∀ z ∈ Metric.ball (1 : ℂ) δ₁, LZ A z = 0 :=
    Dzc_LZ_zero_of_eqOn_Om1 hδ₁ hAd hDL hAeq'
  -- shrink the ball and use that holomorphic solutions at `1` are multiples of `uh`
  set δ₂ : ℝ := min δ₁ (1 / 2) with hδ₂def
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂def]; exact lt_min hδ₁ (by norm_num)
  have hδ₂le : δ₂ ≤ δ₁ := by rw [hδ₂def]; exact min_le_left _ _
  have hδ₂89 : δ₂ < 8 / 9 := by
    rw [hδ₂def]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c₀, hc₀⟩ := hol_sol_at_one_smul hδ₂pos hδ₂89
    (hAd.mono (Metric.ball_subset_ball hδ₂le))
    (fun z hz => hLZA z (Metric.ball_subset_ball hδ₂le hz))
  -- so `D = c₀·uh` near `1`
  have hag : ∀ z ∈ Metric.ball (1 : ℂ) δ₂ ∩ Om1, D z = c₀ * uh z := by
    intro z hz
    rw [hAeq' z ⟨Metric.ball_subset_ball hδ₂le hz.1, hz.2⟩, hc₀ z hz.1]
  exact Dzc_sol_logCoeff_zero hδ₂pos hδ₂89 hD hDL hag hY
    (by rw [hκ] at hU; exact hU)

end Work.A14D
