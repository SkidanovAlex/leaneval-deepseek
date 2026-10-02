/-
# Continuity of translation in `L¹` over a compact set

For a locally integrable `f : ℂ → ℂ` and a compact set `K : Set ℂ`, the map

  `y ↦ ∫ z in K, ‖f (z + y) - f z‖`

is continuous.  This is the "continuity of translation" property of `L¹`: the group `ℂ` acts
continuously on `L¹(ℂ)` by translation (`MeasureTheory.Lp.instContinuousVAddDomAddAct`), so that
`∫ w, ‖g (h + w) - g w‖ → 0` for every integrable `g` as `h → 0`.  The statement for a locally
integrable `f` follows by localising: on a neighbourhood of a point `y₀` all the values `f (z + y)`
with `z ∈ K` lie in one compact set, where `f` may be replaced by an integrable function.

## Main result

* `Work.MRMT.Weyl.continuous_setIntegral_translate`
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Filter Metric
open scoped Topology Pointwise

set_option linter.style.haveILetI false

namespace Work.MRMT.Weyl

noncomputable section

/-- **Continuity of translation in `L¹`.**  For an integrable `g : ℂ → ℂ`, the `L¹`-norm of the
difference of translates, `h ↦ ∫ w, ‖g (h + w) - g w‖`, tends to `0` as `h → 0`.

The proof uses the continuous action of the additive group `ℂ` on `L¹(ℂ)` by translation
(`Lp.instContinuousVAddDomAddAct`), together with `Lp.norm_def` to identify the `L¹`-norm of a
difference with the integral of the pointwise norm of the difference. -/
theorem tendsto_integral_norm_sub_translate {g : ℂ → ℂ} (hg : Integrable g volume) :
    Tendsto (fun h : ℂ => ∫ w, ‖g (h + w) - g w‖) (𝓝 0) (𝓝 0) := by
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hmem : MemLp g 1 (volume : Measure ℂ) := memLp_one_iff_integrable.2 hg
  set G : Lp ℂ 1 (volume : Measure ℂ) := hmem.toLp g with hGdef
  have hG : ⇑G =ᵐ[volume] g := hmem.coeFn_toLp
  -- Identify the `L¹`-norm of the translate difference with the integral of interest.
  have hkey : ∀ c : ℂ, ‖((DomAddAct.mk c) +ᵥ G) - G‖ = ∫ w, ‖g (c + w) - g w‖ := by
    intro c
    have hvadd : ⇑((DomAddAct.mk c) +ᵥ G) =ᵐ[volume] (fun w => g (c + w)) := by
      have h1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk c) G
      have h2 := (measurePreserving_vadd (DomAddAct.mk.symm (DomAddAct.mk c))
        volume).quasiMeasurePreserving.ae_eq_comp hG
      exact h1.trans h2
    have hae : ⇑(((DomAddAct.mk c) +ᵥ G) - G) =ᵐ[volume] (fun w => g (c + w) - g w) := by
      have h := (Lp.coeFn_sub ((DomAddAct.mk c) +ᵥ G) G).trans (hvadd.sub hG)
      refine h.trans (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply]
    have hI : Integrable (fun w => g (c + w) - g w) volume := (hg.comp_add_left c).sub hg
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    rw [eLpNorm_one_eq_lintegral_enorm hI.aestronglyMeasurable]
    rw [← ofReal_integral_norm_eq_lintegral_enorm hI,
      ENNReal.toReal_ofReal (integral_nonneg (fun w => norm_nonneg _))]
  -- The translation action is continuous, hence `c +ᵥ G - G → 0` as `c → 0`.
  have hcont : Tendsto (fun c : ℂ => ‖((DomAddAct.mk c) +ᵥ G) - G‖) (𝓝 0) (𝓝 0) := by
    have h2 : Continuous (fun c : DomAddAct ℂ => (c +ᵥ G) - G) := by fun_prop
    have hc : Continuous (fun c : ℂ => ((DomAddAct.mk c) +ᵥ G) - G) :=
      h2.comp AddOpposite.continuous_op
    have h0 : ((DomAddAct.mk (0 : ℂ)) +ᵥ G) - G = 0 := by
      change ((0 : DomAddAct ℂ) +ᵥ G) - G = 0
      simp
    have hlim : Tendsto (fun c : ℂ => ((DomAddAct.mk c) +ᵥ G) - G) (𝓝 0) (𝓝 0) := by
      have := hc.tendsto (0 : ℂ)
      simpa only [h0] using this
    simpa using hlim.norm
  simpa only [hkey] using hcont

/-- For an integrable `g` and any set `K`, the map `y ↦ ∫ z in K, ‖g (z + y) - g z‖` is
continuous.

The key estimate is
`‖∫ z in K, ‖g (z+y) - g z‖ - ∫ z in K, ‖g (z+y₀) - g z‖‖ ≤ ∫ z in K, ‖g (z+y) - g (z+y₀)‖`,
followed by the translation invariance of Lebesgue measure and
`tendsto_integral_norm_sub_translate`. -/
theorem continuous_setIntegral_norm_sub_of_integrable {g : ℂ → ℂ} (hg : Integrable g volume)
    (K : Set ℂ) :
    Continuous (fun y : ℂ => ∫ z in K, ‖g (z + y) - g z‖) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  -- Pointwise (reverse triangle) bound by the translate difference.
  have hbound : ∀ y : ℂ,
      ‖(∫ z in K, ‖g (z + y) - g z‖) - (∫ z in K, ‖g (z + y₀) - g z‖)‖
        ≤ ∫ w, ‖g (w + (y - y₀)) - g w‖ := by
    intro y
    have hAy : Integrable (fun z => ‖g (z + y) - g z‖) (volume.restrict K) :=
      (((hg.comp_add_right y).sub hg).norm).integrableOn
    have hAy0 : Integrable (fun z => ‖g (z + y₀) - g z‖) (volume.restrict K) :=
      (((hg.comp_add_right y₀).sub hg).norm).integrableOn
    rw [← integral_sub hAy hAy0]
    have hbint : Integrable (fun z => ‖g (z + y) - g (z + y₀)‖) (volume.restrict K) :=
      (((hg.comp_add_right y).sub (hg.comp_add_right y₀)).norm).integrableOn
    calc ‖∫ z in K, (‖g (z + y) - g z‖ - ‖g (z + y₀) - g z‖)‖
        ≤ ∫ z in K, ‖‖g (z + y) - g z‖ - ‖g (z + y₀) - g z‖‖ :=
          norm_integral_le_integral_norm
            (fun z : ℂ => ‖g (z + y) - g z‖ - ‖g (z + y₀) - g z‖)
      _ ≤ ∫ z in K, ‖g (z + y) - g (z + y₀)‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hbint ?_
          filter_upwards with z
          have h := abs_norm_sub_norm_le (g (z + y) - g z) (g (z + y₀) - g z)
          rwa [show (g (z + y) - g z) - (g (z + y₀) - g z) = g (z + y) - g (z + y₀)
            by ring] at h
      _ ≤ ∫ z, ‖g (z + y) - g (z + y₀)‖ :=
          setIntegral_le_integral (((hg.comp_add_right y).sub (hg.comp_add_right y₀)).norm)
            (Eventually.of_forall fun z => norm_nonneg _)
      _ = ∫ w, ‖g (w + (y - y₀)) - g w‖ := by
          have hcongr : (fun z : ℂ => ‖g (z + y) - g (z + y₀)‖)
              = (fun z : ℂ => ‖g (z + y₀ + (y - y₀)) - g (z + y₀)‖) := by
            funext z; rw [show z + y = (z + y₀) + (y - y₀) by ring]
          rw [hcongr]
          exact integral_add_right_eq_self (fun w : ℂ => ‖g (w + (y - y₀)) - g w‖) y₀
  -- The majorant tends to `0`.
  have hsub : Tendsto (fun y : ℂ => y - y₀) (𝓝 y₀) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 y₀) (𝓝 y₀)).sub_const y₀)
  have hlim : Tendsto (fun y : ℂ => ∫ w, ‖g (w + (y - y₀)) - g w‖) (𝓝 y₀) (𝓝 0) := by
    have := (tendsto_integral_norm_sub_translate hg).comp hsub
    simpa [Function.comp_def, add_comm] using this
  have hnorm : Tendsto (fun y : ℂ =>
      ‖(∫ z in K, ‖g (z + y) - g z‖) - (∫ z in K, ‖g (z + y₀) - g z‖)‖) (𝓝 y₀) (𝓝 0) :=
    squeeze_zero (fun y => norm_nonneg _) hbound hlim
  have h2 : Tendsto
      (fun y : ℂ => (∫ z in K, ‖g (z + y) - g z‖) - (∫ z in K, ‖g (z + y₀) - g z‖))
      (𝓝 y₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hnorm
  have h3 := h2.add_const (∫ z in K, ‖g (z + y₀) - g z‖)
  show Tendsto (fun y : ℂ => ∫ z in K, ‖g (z + y) - g z‖) (𝓝 y₀)
    (𝓝 (∫ z in K, ‖g (z + y₀) - g z‖))
  simpa [sub_add_cancel] using h3

/-- **Continuity of the translated integral for a locally integrable function.**

For `f : ℂ → ℂ` locally integrable and `K : Set ℂ` compact, the map
`y ↦ ∫ z in K, ‖f (z + y) - f z‖` is continuous. -/
theorem continuous_setIntegral_translate {f : ℂ → ℂ} (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    {K : Set ℂ} (hK : IsCompact K) :
    Continuous (fun y : ℂ => ∫ z in K, ‖f (z + y) - f z‖) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  -- Localisation: choose a compact set containing `K` and `K + y` for all `y` near `y₀`, an open
  -- neighbourhood `u` of it on which `f` is integrable, and replace `f` by `u.indicator f`.
  set R : ℝ := ‖y₀‖ + 1 with hR
  have hRpos : 0 ≤ R := by rw [hR]; positivity
  have hk : IsCompact (K + closedBall (0 : ℂ) R) := hK.add (isCompact_closedBall 0 R)
  obtain ⟨u, hu_open, hku, hfint⟩ := hf.integrableOn_nhds_isCompact hk
  have hgint : Integrable (u.indicator f) volume :=
    (integrable_indicator_iff hu_open.measurableSet).mpr hfint
  -- On the ball of radius `1` around `y₀` the two integrands agree.
  have heq : (fun y : ℂ => ∫ z in K, ‖f (z + y) - f z‖) =ᶠ[𝓝 y₀]
      (fun y : ℂ => ∫ z in K, ‖(u.indicator f) (z + y) - (u.indicator f) z‖) := by
    filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    have hzk : z ∈ K + closedBall (0 : ℂ) R := by
      rw [Set.mem_add]
      exact ⟨z, hz, 0,
        by rw [Metric.mem_closedBall, dist_zero_right]; simpa using hRpos, by simp⟩
    have hyR : y ∈ closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖y‖ ≤ ‖y₀‖ + ‖y - y₀‖ := by
        calc ‖y‖ = ‖y₀ + (y - y₀)‖ := by ring_nf
          _ ≤ ‖y₀‖ + ‖y - y₀‖ := norm_add_le _ _
      have hy1 : ‖y - y₀‖ < 1 := by simpa [dist_eq_norm] using hy
      linarith [hR]
    have hzyk : z + y ∈ K + closedBall (0 : ℂ) R := by
      rw [Set.mem_add]
      exact ⟨z, hz, y, hyR, rfl⟩
    rw [Set.indicator_of_mem (hku hzyk) f, Set.indicator_of_mem (hku hzk) f]
  exact (continuous_setIntegral_norm_sub_of_integrable hgint K).continuousAt.congr_of_eventuallyEq heq

end

end Work.MRMT.Weyl
