import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- The two-variable elementary bound used at the end of `exists_Rch`: if `R * r > 8` then
`(A/R + A·r/8)/(A/2) < r/2` for `A, r, R > 0`. -/
private theorem geom_chart_bound {A R r : ℝ} (hA : 0 < A) (hr : 0 < r) (hR : 0 < R)
    (h8 : 8 < R * r) :
    (A / R + A * r / 8) / (A / 2) < r / 2 := by
  have h1 : A / R < A * r / 8 := by
    rw [div_lt_div_iff₀ hR (by norm_num : (0 : ℝ) < 8)]
    nlinarith
  have h2 : (0 : ℝ) < A / 2 := by linarith
  rw [div_lt_iff₀ h2]
  nlinarith

end Work.PARIMPL2

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL2
open Work.PARIMPL (ParNormal chartZeta)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The chart radius.** For every `R` above a threshold `Rch ≥ 4`, the two geometric windows
`WinG P R H`, `WoutG P R H` (of `Work.PARIMPL2.Lavaurs.Defs`, i.e. `Re (w0 z) ∈ [R,R+2]`,
`|Im (w0 z)| ≤ H` respectively `Re (w0 z) ∈ [-R-2,-R]`, `|Im (w0 z)| ≤ H`, where
`w0 P z = -P.s c₀/(z - d.z₁)`) lie in the chart ball `‖ζ_c(z)‖ < P.r/2` of the parameter normal
form (`ζ_c(z) = (z - P.m c)/P.s c`) for all `c ∈ P.Nm` near `c₀`.

Reason: for `R ≥ 8(H+1)`, `|w0 z| ≥ R`, so `|z - d.z₁| = ‖P.s c₀‖/|w0 z| ≤ ‖P.s c₀‖/R`; and
`P.m c → P.m c₀ = d.z₁`, `P.s c → P.s c₀ ≠ 0` (`P.cont_m`, `P.cont_s`, `P.m₀`, `P.s_ne`), so
`‖(z - P.m c)/P.s c‖ ≤ 2/R + ε` for `c` close to `c₀`. -/
theorem exists_Rch (P : Work.PARIMPL.ParNormal d) :
    ∃ Rch : ℝ, 4 ≤ Rch ∧ ∀ R ≥ Rch, RchOK P R := by
  have hc0 : c₀ ∈ ball c₀ P.ρ₀ := by simp [Metric.mem_ball, P.hρ₀]
  have hs0 : P.s c₀ ≠ 0 := P.s_ne c₀ hc0
  have ha : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs0
  have hr : 0 < P.r := P.hr
  have hε : 0 < ‖P.s c₀‖ * P.r / 8 := by positivity
  -- continuity of `m` and `s` at `c₀`, read as explicit neighbourhood statements
  have hmc : ContinuousAt P.m c₀ := P.cont_m.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
  have hsc : ContinuousAt P.s c₀ := P.cont_s.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
  have hm_ev : ∀ᶠ c in 𝓝 c₀, ‖P.m c - d.z₁‖ < ‖P.s c₀‖ * P.r / 8 := by
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousAt_iff.mp hmc) _ hε
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun c hc => ?_⟩
    simpa [dist_eq_norm, P.m₀] using hδ' hc
  have hs_ev : ∀ᶠ c in 𝓝 c₀, ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ := by
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousAt_iff.mp hsc) _ (by positivity : 0 < ‖P.s c₀‖ / 2)
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun c hc => ?_⟩
    have h1 : ‖P.s c - P.s c₀‖ < ‖P.s c₀‖ / 2 := by simpa [dist_eq_norm] using hδ' hc
    have h2 : ‖P.s c₀‖ - ‖P.s c‖ ≤ ‖P.s c - P.s c₀‖ := by
      have h3 := abs_norm_sub_norm_le (P.s c₀) (P.s c)
      rw [norm_sub_rev (P.s c₀) (P.s c)] at h3
      linarith [le_abs_self (‖P.s c₀‖ - ‖P.s c‖)]
    linarith
  obtain ⟨ρm, hρm, hmρ⟩ := Metric.eventually_nhds_iff.mp hm_ev
  obtain ⟨ρs, hρs, hsρ⟩ := Metric.eventually_nhds_iff.mp hs_ev
  refine ⟨max 4 (8 / P.r + 1), le_max_left _ _, fun R hR => ?_⟩
  have hR4 : 4 ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := by linarith
  have hR8 : 8 / P.r < R := by
    have h1 : 8 / P.r + 1 ≤ R := le_trans (le_max_right _ _) hR
    linarith
  have h8lt : 8 < R * P.r := by rwa [div_lt_iff₀ hr] at hR8
  set ρ := min ρm ρs with hρdef
  have hρ : 0 < ρ := lt_min hρm hρs
  unfold RchOK
  refine ⟨ρ, hρ, fun H _hH c hc z hz => ?_⟩
  have hcm : dist c c₀ < ρm := lt_of_lt_of_le hc.2 (min_le_left _ _)
  have hcs : dist c c₀ < ρs := lt_of_lt_of_le hc.2 (min_le_right _ _)
  have hm_c : ‖P.m c - d.z₁‖ < ‖P.s c₀‖ * P.r / 8 := hmρ hcm
  have hs_c : ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ := hsρ hcs
  have hz₁ : z ≠ d.z₁ := by
    rcases hz with h | h
    · exact h.1
    · exact h.1
  -- the window gives `R ≤ ‖w0 z‖`
  have hz_norm : R ≤ ‖w0 P z‖ := by
    rcases hz with h | h
    · have hre : R ≤ (w0 P z).re := h.2.1.1
      calc R ≤ (w0 P z).re := hre
        _ ≤ |(w0 P z).re| := le_abs_self _
        _ ≤ ‖w0 P z‖ := Complex.abs_re_le_norm _
    · have hre : (w0 P z).re ≤ -R := h.2.1.2
      calc R ≤ -((w0 P z).re) := by linarith
        _ ≤ |(w0 P z).re| := neg_le_abs _
        _ ≤ ‖w0 P z‖ := Complex.abs_re_le_norm _
  -- hence `‖z - z₁‖ ≤ ‖P.s c₀‖/R`
  have hprod : (z - d.z₁) * w0 P z = -P.s c₀ := by
    have hz1ne : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz₁
    rw [w0]
    field_simp
  have hnorms : ‖z - d.z₁‖ * ‖w0 P z‖ = ‖P.s c₀‖ := by
    rw [← norm_mul, hprod, norm_neg]
  have hz1_le : ‖z - d.z₁‖ ≤ ‖P.s c₀‖ / R := by
    rw [le_div_iff₀ hRpos]
    calc ‖z - d.z₁‖ * R ≤ ‖z - d.z₁‖ * ‖w0 P z‖ :=
          mul_le_mul_of_nonneg_left hz_norm (norm_nonneg _)
      _ = ‖P.s c₀‖ := hnorms
  have hle : ‖z - P.m c‖ ≤ ‖P.s c₀‖ / R + ‖P.s c₀‖ * P.r / 8 := by
    have hdecomp : z - P.m c = (z - d.z₁) + (d.z₁ - P.m c) := by ring
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖d.z₁ - P.m c‖ = ‖P.m c - d.z₁‖ := norm_sub_rev _ _
    rw [h2]
    linarith
  have hnum_nn : 0 ≤ ‖P.s c₀‖ / R + ‖P.s c₀‖ * P.r / 8 := by
    have h1 : 0 ≤ ‖P.s c₀‖ / R := div_nonneg (norm_nonneg _) hRpos.le
    have h2 : 0 ≤ ‖P.s c₀‖ * P.r / 8 := by positivity
    linarith
  calc ‖chartZeta P c z‖ = ‖z - P.m c‖ / ‖P.s c‖ := by simp only [chartZeta, norm_div]
    _ ≤ (‖P.s c₀‖ / R + ‖P.s c₀‖ * P.r / 8) / ‖P.s c‖ :=
        div_le_div_of_nonneg_right hle (norm_nonneg _)
    _ ≤ (‖P.s c₀‖ / R + ‖P.s c₀‖ * P.r / 8) / (‖P.s c₀‖ / 2) :=
        div_le_div_of_nonneg_left hnum_nn (by linarith : 0 < ‖P.s c₀‖ / 2) hs_c
    _ < P.r / 2 := geom_chart_bound ha hr hRpos h8lt

end Work.PARIMPL2.Lavaurs

namespace Work.PARIMPL2

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- Compatibility statement of `Work.PARIMPL2.Lavaurs.exists_Rch` in the `Work.PARIMPL2`
namespace (the namespace the surrounding `PARIMPL2` development uses for `RchOK` and the windows). -/
theorem exists_Rch (P : Work.PARIMPL.ParNormal d) :
    ∃ Rch : ℝ, 4 ≤ Rch ∧ ∀ R ≥ Rch, RchOK P R :=
  Lavaurs.exists_Rch P

end Work.PARIMPL2

end
