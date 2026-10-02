import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.approxEcal_end_in_small_sum
import Submission.Work.PARIMPL2.Lavaurs.norm_log_sub_log_le
import Submission.Work.PARIMPL2.Lavaurs.chartZeta_uniform_close
import Submission.Work.PARIMPL2.Lavaurs.model_value_identity
import Submission.Work.PARIMPL2.Lavaurs.winG_w0_bounds
import Submission.Work.PARIMPL2.approxEcal_end_in_small
import Submission.Work.PARIMPL2.approxEcal_end_out_small

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal chartZeta approxUin ecalUin ecalU)
open Work.Implosion (approxEcal ecalCoord)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## The two limit facts -/

private theorem lam_le_of_close (P : ParNormal d) (θ : ℝ) (hθ : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, P.lam c ≤ θ := by
  have h : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) :=
    P.tendsto_lam c₀ P.a2₀ (by simpa using P.hρ₀)
  have hev : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c ≤ θ := h.eventually (Iic_mem_nhds hθ)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hρ'⟩ := hev
  exact ⟨ρ, hρ, fun c hc => hρ' (by simpa [Metric.mem_ball] using hc.2) hc.1⟩

private theorem kappa_close (P : ParNormal d) (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ‖P.κ c - P.κ c₀‖ ≤ η := by
  have hcont : ContinuousAt P.κ c₀ := P.cont_κ.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hcont η hη
  exact ⟨ρ, hρ, fun c hc => le_of_lt (by simpa [dist_eq_norm] using hρ' hc)⟩

private theorem approxUin_eq_lam (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (z : ℂ) :
    approxUin P c z = approxEcal ((P.lam c : ℂ) * Complex.I) (P.κ c)
      (ecalCoord ((P.lam c : ℂ) * Complex.I) (chartZeta P c z)
        + Real.pi * Complex.I / ((P.lam c : ℂ) * Complex.I)) := by
  simp only [Work.PARIMPL.approxUin, Work.PARIMPL.ecalUin, Work.PARIMPL.ecalU,
    P.a_of_mem_Nm hc]

private theorem pi_I_div (lam : ℝ) (hlam : lam ≠ 0) :
    Real.pi * Complex.I / ((lam : ℂ) * Complex.I) = ((Real.pi / lam : ℝ) : ℂ) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [div_eq_iff (mul_ne_zero (Complex.ofReal_ne_zero.mpr hlam) hI)]
  push_cast
  field_simp
  rw [div_self (Complex.ofReal_ne_zero.mpr hlam)]

/-! ## The main estimate -/

/-- **The incoming model estimate on `WinG` (design §3.4, L2).**  At fixed depth `R` (above the
chart threshold `RchOK`) and width `H` with `R ≥ 8(H+1)`, the incoming approximate coordinate
`approxUin P c z'` of the *parameter* `c` agrees, uniformly on the incoming window and for `z'`
close to its point `z`, with the model value `π/λ_c - approxCoord κ₀ (w0 z)` — the value
`π/λ_c + 1/ζ₀ - κ₀ log(-ζ₀)` at the limit `ζ₀ = -1/(w0 z)`, with `κ₀ = P.κ c₀` fixed at `c₀`.

The error is `≤ ε` for every `ε > 0` (the constant is `C λ_c²/‖ζ‖³` with `λ_c → 0` and
`ζ_c(z') → ζ₀`, uniformly on the compact window), and `δ > 0` is the neighbourhood of `z` on
which the limit is uniform.  Uses `Work.PARIMPL2.Lavaurs.approxEcal_end_in_small_sum` in the
branch-free sum form `πi/a + 1/ζ - κ log(-ζ)`, the chart limit `ζ_c(z') → -1/(w0 z)`
(`P.cont_m`, `P.cont_s`, `P.m₀`, `P.s_ne`) and `κ_c → κ₀` (`P.cont_κ`), plus `RchOK` to keep the
chart coordinate inside the germ ball.  (`WinG` is compact and `‖ζ_c z‖ ≤ 1/8` on it once
`R ≥ 8`, so the small-`ζ` hypotheses `‖ζ‖ ≤ 4`, `4λ_c ≤ ‖ζ‖` hold for `ρ` small; for `H < 0` the
window is empty and the statement is vacuous.) -/
theorem win_model {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (R H : ℝ) (hR : Work.PARIMPL2.RchOK P R) (hH : R ≥ 8 * (H + 1)) :
    ∀ ε > 0, ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      ∀ z ∈ Work.PARIMPL2.WinG P R H,
      ∀ z' : ℂ, ‖z' - z‖ ≤ δ →
        ‖Work.PARIMPL.approxUin P c z' -
          (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
            (Work.PARIMPL2.w0 P z))‖ ≤ ε := by
  intro ε hε
  set K : ℝ := ‖P.κ c₀‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hK0 : 0 ≤ K := hKpos.le
  obtain ⟨C, hC0, hC⟩ := approxEcal_end_in_small_sum K hK0
  by_cases hempty : (Work.PARIMPL2.WinG P R H).Nonempty
  · obtain ⟨z0, hz0⟩ := hempty
    have hH0 : 0 ≤ H := (winG_w0_bounds P hH hz0).1
    have hR8 : 8 ≤ R := (winG_w0_bounds P hH hz0).2.1
    have hRpos : 0 < R := by linarith
    have hden : 0 < R + 2 + H := by linarith
    -- the two geometric constants of the window
    set rlow : ℝ := R / (R + 2 + H) ^ 2 with hrlowdef
    have hrlowpos : 0 < rlow := by rw [hrlowdef]; positivity
    set ζlow : ℝ := rlow / 2 with hζlowdef
    have hζlowpos : 0 < ζlow := by rw [hζlowdef]; linarith
    set B : ℝ := Real.log (R + 2 + H) + Real.pi with hBdef
    have hBpos : 0 < B := by
      rw [hBdef]
      have : 0 < Real.log (R + 2 + H) := Real.log_pos (by linarith)
      linarith [Real.pi_pos]
    -- the closeness radius of ζ
    set η : ℝ := min (ε * rlow ^ 2 / 12) (min (ε * ζlow / (6 * K)) (min rlow ζlow))
      with hηdef
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min (by positivity) (lt_min (by positivity) (lt_min hrlowpos hζlowpos))
    have hη_r : η ≤ ε * rlow ^ 2 / 12 := by rw [hηdef]; exact min_le_left _ _
    have hη_κ : η ≤ ε * ζlow / (6 * K) := by
      rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hη_rlow : η ≤ rlow := by
      rw [hηdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hη_ζlow : η ≤ ζlow := by
      rw [hηdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    -- the λ-threshold
    set θ : ℝ := min (ζlow / 4) (Real.sqrt (ε * ζlow ^ 3 / (3 * C + 1))) with hθdef
    have hθpos : 0 < θ := by
      rw [hθdef]
      exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
    have hθ_le : θ ≤ ζlow / 4 := by rw [hθdef]; exact min_le_left _ _
    have hθ_sq : θ ^ 2 ≤ ε * ζlow ^ 3 / (3 * C + 1) := by
      have h : θ ≤ Real.sqrt (ε * ζlow ^ 3 / (3 * C + 1)) := by
        rw [hθdef]; exact min_le_right _ _
      calc θ ^ 2 ≤ (Real.sqrt (ε * ζlow ^ 3 / (3 * C + 1))) ^ 2 := pow_le_pow_left₀ hθpos.le h 2
        _ = ε * ζlow ^ 3 / (3 * C + 1) := Real.sq_sqrt (by positivity)
    -- the κ-tolerance
    set κtol : ℝ := min 1 (ε / (3 * B)) with hκtoldef
    have hκtolpos : 0 < κtol := by rw [hκtoldef]; exact lt_min one_pos (by positivity)
    have hκtol_le_one : κtol ≤ 1 := by rw [hκtoldef]; exact min_le_left _ _
    have hκtol_le : κtol ≤ ε / (3 * B) := by rw [hκtoldef]; exact min_le_right _ _
    obtain ⟨ρ₁, δ, hρ₁, hδ, h₁⟩ := chartZeta_uniform_close P R H η hH hηpos
    obtain ⟨ρ₂, hρ₂, h₂⟩ := lam_le_of_close P θ hθpos
    obtain ⟨ρ₃, hρ₃, h₃⟩ := kappa_close P κtol hκtolpos
    refine ⟨min ρ₁ (min ρ₂ ρ₃), δ, lt_min hρ₁ (lt_min hρ₂ hρ₃), hδ, ?_⟩
    intro c hc z hz z' hz'
    obtain ⟨hcNm, hcball⟩ := hc
    have hcdist : dist c c₀ < min ρ₁ (min ρ₂ ρ₃) := Metric.mem_ball.mp hcball
    have hc1 : c ∈ P.Nm ∩ Metric.ball c₀ ρ₁ :=
      ⟨hcNm, Metric.mem_ball.mpr (lt_of_lt_of_le hcdist (min_le_left _ _))⟩
    have hc2 : c ∈ P.Nm ∩ Metric.ball c₀ ρ₂ :=
      ⟨hcNm, Metric.mem_ball.mpr (lt_of_lt_of_le hcdist (le_trans (min_le_right _ _) (min_le_left _ _)))⟩
    have hc3 : c ∈ Metric.ball c₀ ρ₃ :=
      Metric.mem_ball.mpr (lt_of_lt_of_le hcdist (le_trans (min_le_right _ _) (min_le_right _ _)))
    obtain ⟨hH0', hR8', hwne, hprod, hwn_ge, hwn_le, hζ₀eq, hζ₀norm, hζ₀re, hlogw⟩ :=
      winG_w0_bounds P hH hz
    have hζclose : ‖chartZeta P c z' - chartZeta P c₀ z‖ ≤ η := h₁ c hc1 z hz z' hz'
    have hlam_le : P.lam c ≤ θ := h₂ c hc2
    have hκ1 : ‖P.κ c - P.κ c₀‖ ≤ 1 := le_trans (h₃ c hc3) hκtol_le_one
    have hκ2 : ‖P.κ c - P.κ c₀‖ ≤ ε / (3 * B) := le_trans (h₃ c hc3) hκtol_le
    have hκnorm : ‖P.κ c‖ ≤ K := by
      calc ‖P.κ c‖ = ‖P.κ c₀ + (P.κ c - P.κ c₀)‖ := by ring_nf
        _ ≤ ‖P.κ c₀‖ + ‖P.κ c - P.κ c₀‖ := norm_add_le _ _
        _ ≤ ‖P.κ c₀‖ + 1 := add_le_add le_rfl hκ1
        _ = K := by rw [hKdef]
    have hlampos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
    have hlamnn : 0 ≤ P.lam c := hlampos.le
    -- the bound on ζ₀
    have hζ₀re' : (chartZeta P c₀ z).re ≤ -rlow := by linarith [hrlowdef, hζ₀re]
    have hζ₀norm_ge : rlow ≤ ‖chartZeta P c₀ z‖ := by
      have h1 : |(chartZeta P c₀ z).re| ≤ ‖chartZeta P c₀ z‖ := Complex.abs_re_le_norm _
      have h2 : |(chartZeta P c₀ z).re| = -((chartZeta P c₀ z).re) :=
        abs_of_neg (by linarith [hζ₀re', hrlowpos])
      linarith
    -- the derived bounds on ζ_c(z')
    have hζ're_le : (chartZeta P c z').re ≤ -rlow + η := by
      have hsplit_re : (chartZeta P c₀ z).re + (chartZeta P c z' - chartZeta P c₀ z).re
          = (chartZeta P c z').re := by
        rw [← Complex.add_re,
          show chartZeta P c₀ z + (chartZeta P c z' - chartZeta P c₀ z) = chartZeta P c z'
            from by ring]
      have h2 : (chartZeta P c z' - chartZeta P c₀ z).re
          ≤ ‖chartZeta P c z' - chartZeta P c₀ z‖ :=
        le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      linarith [hζ₀re', h2, hζclose]
    have hζ're_neg : (chartZeta P c z').re < 0 := by
      have h : η ≤ rlow / 2 := by rw [← hζlowdef]; exact hη_ζlow
      linarith [hζ're_le, hrlowpos]
    have hζ'norm_ge : ζlow ≤ ‖chartZeta P c z'‖ := by
      have h1 : -((chartZeta P c z').re) ≤ ‖chartZeta P c z'‖ := by
        have h := Complex.abs_re_le_norm (chartZeta P c z')
        rwa [abs_of_neg hζ're_neg] at h
      have h2 : ζlow ≤ -((chartZeta P c z').re) := by linarith [hζ're_le, hη_ζlow, hζlowdef]
      linarith
    have hζ'norm_le : ‖chartZeta P c z'‖ ≤ 4 := by
      have h1 : ‖chartZeta P c z'‖ ≤ ‖chartZeta P c₀ z‖ + η := by
        have hsplit_norm : ‖chartZeta P c₀ z + (chartZeta P c z' - chartZeta P c₀ z)‖
            = ‖chartZeta P c z'‖ := by
          rw [show chartZeta P c₀ z + (chartZeta P c z' - chartZeta P c₀ z) = chartZeta P c z'
            from by ring]
        have h2 := norm_add_le (chartZeta P c₀ z) (chartZeta P c z' - chartZeta P c₀ z)
        linarith [hsplit_norm, h2, hζclose]
      have h3 : 1 / R ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      have hrlow_le : rlow ≤ 1 / R := by
        rw [hrlowdef, div_le_iff₀ (by positivity : (0:ℝ) < (R + 2 + H) ^ 2)]
        rw [div_mul_eq_mul_div, le_div_iff₀ hRpos]
        have h2H : 0 ≤ 2 + H := by linarith
        nlinarith [sq_nonneg (2 + H), mul_nonneg hRpos.le h2H]
      have h4 : ζlow ≤ 1 / 8 := by
        rw [hζlowdef]
        linarith [hrlow_le, h3]
      linarith [h1, hζ₀norm, h3, h4]
    have h4lam : 4 * P.lam c ≤ ‖chartZeta P c z'‖ := by
      have h : 4 * P.lam c ≤ 4 * θ := by linarith
      linarith [hθ_le, hζ'norm_ge, hζlowpos]
    -- the abbreviations of the three model values
    set M' : ℂ := ((Real.pi / P.lam c : ℝ) : ℂ)
      + (1 / chartZeta P c z' - P.κ c * Complex.log (-(chartZeta P c z'))) with hM'
    set M₀ : ℂ := ((Real.pi / P.lam c : ℝ) : ℂ)
      + (1 / chartZeta P c₀ z - P.κ c * Complex.log (-(chartZeta P c₀ z))) with hM₀₀
    set T0 : ℂ := ((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
      (Work.PARIMPL2.w0 P z) with hT0
    have h2bound : ‖M' - M₀‖ ≤ ε / 3 := by
      have hdiff : M' - M₀ = (1 / chartZeta P c z' - 1 / chartZeta P c₀ z)
          - P.κ c * (Complex.log (-(chartZeta P c z')) - Complex.log (-(chartZeta P c₀ z))) := by
        rw [hM', hM₀₀]; ring
      rw [hdiff]
      have hζ'ne : chartZeta P c z' ≠ 0 := by
        intro h0
        have := hζ'norm_ge
        rw [h0, norm_zero] at this
        linarith
      have hζ₀ne : chartZeta P c₀ z ≠ 0 := by
        intro h0
        have := hζ₀norm_ge
        rw [h0, norm_zero] at this
        linarith
      have hpiece1 : ‖1 / chartZeta P c z' - 1 / chartZeta P c₀ z‖ ≤ η / (ζlow * rlow) := by
        have hinv : 1 / chartZeta P c z' - 1 / chartZeta P c₀ z
            = (chartZeta P c₀ z - chartZeta P c z')
              / (chartZeta P c z' * chartZeta P c₀ z) := by
          field_simp
        rw [hinv, norm_div, norm_mul]
        have hnum : ‖chartZeta P c₀ z - chartZeta P c z'‖ ≤ η := by
          rw [norm_sub_rev]; exact hζclose
        have hden : ζlow * rlow ≤ ‖chartZeta P c z'‖ * ‖chartZeta P c₀ z‖ :=
          mul_le_mul hζ'norm_ge hζ₀norm_ge hrlowpos.le (norm_nonneg _)
        exact div_le_div₀ hηpos.le hnum (mul_pos hζlowpos hrlowpos) hden
      have hpiece2 : ‖P.κ c‖ * ‖Complex.log (-(chartZeta P c z'))
            - Complex.log (-(chartZeta P c₀ z))‖ ≤ K * (η / ζlow) := by
        have hlog : ‖Complex.log (-(chartZeta P c z')) - Complex.log (-(chartZeta P c₀ z))‖
            ≤ η / ζlow := by
          have h1 : ζlow ≤ (-(chartZeta P c z')).re := by
            rw [Complex.neg_re]; linarith [hζ're_le, hη_ζlow, hζlowdef]
          have h2 : ζlow ≤ (-(chartZeta P c₀ z)).re := by
            rw [Complex.neg_re]; linarith [hζ₀re', hζlowdef]
          have h3 := norm_log_sub_log_le hζlowpos h1 h2
          refine le_trans h3 ?_
          rw [show (-(chartZeta P c z')) - (-(chartZeta P c₀ z))
              = -(chartZeta P c z' - chartZeta P c₀ z) by ring, norm_neg]
          exact div_le_div_of_nonneg_right hζclose hζlowpos.le
        exact mul_le_mul hκnorm hlog (norm_nonneg _) hK0
      have hb1 : η / (ζlow * rlow) ≤ ε / 6 := by
        rw [div_le_iff₀ (mul_pos hζlowpos hrlowpos)]
        have heq : (ε / 6) * (ζlow * rlow) = ε * rlow ^ 2 / 12 := by rw [hζlowdef]; ring
        rw [heq]; exact hη_r
      have hb2 : K * (η / ζlow) ≤ ε / 6 := by
        have h1 : η / ζlow ≤ (ε * ζlow / (6 * K)) / ζlow :=
          div_le_div_of_nonneg_right hη_κ hζlowpos.le
        calc K * (η / ζlow) ≤ K * ((ε * ζlow / (6 * K)) / ζlow) :=
              mul_le_mul_of_nonneg_left h1 hK0
          _ = ε / 6 := by field_simp
      have hsum2 : η / (ζlow * rlow) + K * (η / ζlow) ≤ ε / 3 := by linarith
      calc ‖(1 / chartZeta P c z' - 1 / chartZeta P c₀ z)
              - P.κ c * (Complex.log (-(chartZeta P c z')) - Complex.log (-(chartZeta P c₀ z)))‖
          ≤ ‖1 / chartZeta P c z' - 1 / chartZeta P c₀ z‖
            + ‖P.κ c * (Complex.log (-(chartZeta P c z')) - Complex.log (-(chartZeta P c₀ z)))‖ :=
            norm_sub_le _ _
        _ = ‖1 / chartZeta P c z' - 1 / chartZeta P c₀ z‖
            + ‖P.κ c‖ * ‖Complex.log (-(chartZeta P c z')) - Complex.log (-(chartZeta P c₀ z))‖ := by
            rw [norm_mul]
        _ ≤ η / (ζlow * rlow) + K * (η / ζlow) := add_le_add hpiece1 hpiece2
        _ ≤ ε / 3 := hsum2
    have h3bound : ‖M₀ - T0‖ ≤ ε / 3 := by
      have heq : M₀ - T0 = (P.κ c - P.κ c₀) * Complex.log (Work.PARIMPL2.w0 P z) := by
        have hid := model_value_identity P R H hH hcNm hz
        have hshape : M₀ - T0 = (((Real.pi / P.lam c : ℝ) : ℂ) + 1 / chartZeta P c₀ z
              - P.κ c * Complex.log (-(chartZeta P c₀ z)))
            - (((Real.pi / P.lam c : ℝ) : ℂ)
              - Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P z)) := by
          rw [hM₀₀, hT0]; ring
        rw [hshape, hid]
        ring
      rw [heq, norm_mul]
      have hbound : ‖P.κ c - P.κ c₀‖ * ‖Complex.log (Work.PARIMPL2.w0 P z)‖ ≤ (ε / (3 * B)) * B :=
        mul_le_mul hκ2 hlogw (norm_nonneg _) (by positivity)
      calc ‖P.κ c - P.κ c₀‖ * ‖Complex.log (Work.PARIMPL2.w0 P z)‖ ≤ (ε / (3 * B)) * B := hbound
        _ = ε / 3 := by field_simp
    have h1bound : ‖approxUin P c z' - M'‖ ≤ ε / 3 := by
      have hsumb := hC (P.lam c) (P.κ c) (chartZeta P c z') hlampos hκnorm hζ're_neg
        hζ'norm_le h4lam
      have hA := approxUin_eq_lam P hcNm z'
      have hpi : Real.pi * Complex.I / ((P.lam c : ℂ) * Complex.I) = ((Real.pi / P.lam c : ℝ) : ℂ) :=
        pi_I_div (P.lam c) (ne_of_gt hlampos)
      rw [hpi] at hsumb
      have hM'shape : M' = ((Real.pi / P.lam c : ℝ) : ℂ)
          + (1 / chartZeta P c z' - P.κ c * Complex.log (-(chartZeta P c z'))) := by
        rw [hM']
      rw [hA, hpi, hM'shape]
      refine le_trans hsumb ?_
      have hlam_sq : (P.lam c) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hlamnn hlam_le 2
      have hζ_cube : ζlow ^ 3 ≤ ‖chartZeta P c z'‖ ^ 3 := pow_le_pow_left₀ hζlowpos.le hζ'norm_ge 3
      have hstep1 : C * (P.lam c) ^ 2 / ‖chartZeta P c z'‖ ^ 3 ≤ C * θ ^ 2 / ζlow ^ 3 :=
        div_le_div₀ (mul_nonneg hC0 (sq_nonneg θ)) (mul_le_mul_of_nonneg_left hlam_sq hC0)
          (pow_pos hζlowpos 3) hζ_cube
      have hstep2 : C * θ ^ 2 / ζlow ^ 3 ≤ C * (ε * ζlow ^ 3 / (3 * C + 1)) / ζlow ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθ_sq hC0) (pow_pos hζlowpos 3).le
      have hstep3 : C * (ε * ζlow ^ 3 / (3 * C + 1)) / ζlow ^ 3 = C * ε / (3 * C + 1) := by
        field_simp
      have hstep4 : C * ε / (3 * C + 1) ≤ ε / 3 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * C + 1)]
        nlinarith [hε.le, hC0]
      linarith [hstep1, hstep2, hstep3, hstep4]
    have hsplit : approxUin P c z' - T0 = (approxUin P c z' - M') + ((M' - M₀) + (M₀ - T0)) := by
      ring
    calc ‖approxUin P c z' - T0‖
        ≤ ‖approxUin P c z' - M'‖ + ‖(M' - M₀) + (M₀ - T0)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖approxUin P c z' - M'‖ + (‖M' - M₀‖ + ‖M₀ - T0‖) := by
          linarith [norm_add_le (M' - M₀) (M₀ - T0)]
      _ ≤ ε / 3 + (ε / 3 + ε / 3) := add_le_add h1bound (add_le_add h2bound h3bound)
      _ ≤ ε := by linarith
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro c hc z hz z' hz'
    exact absurd ⟨z, hz⟩ hempty

end Work.PARIMPL2.Lavaurs

end
