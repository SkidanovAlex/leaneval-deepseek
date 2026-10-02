/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoordFix team
-/
import Mathlib
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.FatouCoord.Flower.tangency_of_antiholomorphic_root

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Growth of the real part of the chart dynamics of an antiholomorphic square root

Let `f z = z + z ^ 2 h z` (`h 0 = 1`) be a parabolic germ with `ParabolicBounds f h a r A A'`,
and let `g` be an **antiholomorphic square root** of `f` (`star ∘ g` holomorphic, `g ∘ g = f`,
`g 0 = 0`).  In the parabolic chart `W = -1/u` the map induced by `g` is
`gChart g W = -1 / g (-1 / W)`.

The main result is that past some level `M ≥ 0` the real part of `gChart g` grows by at least
`1/4` per step:
`W.re + 1/4 ≤ (gChart g W).re` whenever `M < W.re`.

The mechanism is the second order Taylor expansion of `G := star ∘ g`.  Writing
`G u = u + u ^ 2 G₂ u` (which is available because `G` is entire, `G 0 = 0` and `deriv G 0 = 1`
by `tangency_of_antiholomorphic_root`), the relation `g ∘ g = f` gives, in the limit,
`G₂ 0 + star (G₂ 0) = 1`, i.e. `Re (G₂ 0) = 1/2`.  Equivalently `g u = star u + O(u^2)` with
second order coefficient of real part `1/2`, which is exactly what makes
`-1 / g z + 1 / star z` tend to `star (G₂ 0)` (whose real part is `1/2`) as `z → 0`.
-/

open scoped Topology
open Filter Metric

namespace Work.FatouCoordFix.FlowerFix

theorem gChart_re_growth {f h g : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hg_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z)
    (hgg : g ∘ g = f) (hg0 : g 0 = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ W : ℂ, M < W.re → W.re + 1 / 4 ≤ (Work.FatouCoord.Flower.gChart g W).re := by
  -- ## The holomorphic conjugate `G = star ∘ g`
  set G : ℂ → ℂ := fun z => star (g z) with hGdef
  have hGdiff : Differentiable ℂ G := fun z => hg_anti z
  have hGan : AnalyticAt ℂ G 0 := hGdiff.analyticAt 0
  have hG0 : G 0 = 0 := by simp [hGdef, hg0]
  have hgg' : ∀ u : ℂ, g (g u) = f u := fun u => by
    have h := congrFun hgg u
    simpa [Function.comp_apply] using h
  have hh : DifferentiableAt ℂ h 0 := hb.h_diff.differentiableAt (ball_mem_nhds 0 hb.hr)
  have hh0 : h 0 = 1 := by
    have h1 : ‖h 0 - 1‖ ≤ 0 := by
      have h2 := hb.h_close 0 (by simpa using hb.hr)
      simpa using h2
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  have hfG : ∀ u : ℂ, ‖u‖ < r → f u = star (G (star (G u))) := by
    intro u _
    rw [← hgg' u]
    simp only [hGdef]
    simp
  have htd := Work.FatouCoord.Flower.tangency_of_antiholomorphic_root hb.hr hGan hG0 hfG
      (fun u hu => hb.f_eq u (mem_ball_zero_iff.mpr hu)) hh hh0
      (rfl : deriv h 0 = deriv h 0)
  have hG1 : deriv G 0 = 1 := htd.1
  -- ## The second order Taylor expansion of `G`
  obtain ⟨G₂, hG₂an, hG₂⟩ := hGan.exists_eq_sum_add_pow_mul 2
  have hGexp : ∀ u : ℂ, G u = u + u ^ 2 * G₂ u := by
    intro u
    rw [hG₂ u, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [iteratedDeriv_zero, iteratedDeriv_one, hG0, hG1]
    ring
  set c : ℂ := G₂ 0 with hcdef
  have hG₂c : ContinuousAt G₂ 0 := hG₂an.continuousAt
  -- ## `f` in terms of `G` and `G₂`
  have hFexp : ∀ u : ℂ, f u = G u + (G u) ^ 2 * star (G₂ (star (G u))) := by
    intro u
    calc f u = g (g u) := (hgg' u).symm
      _ = star (G (star (G u))) := by simp only [hGdef]; simp
      _ = star (star (G u) + (star (G u)) ^ 2 * G₂ (star (G u))) := by rw [hGexp (star (G u))]
      _ = G u + (G u) ^ 2 * star (G₂ (star (G u))) := by
            simp only [star_add, star_mul, star_pow, star_star]
            ring
  -- ## Comparing the two second order expansions of `f`
  have hkey : ∀ u : ℂ, u ≠ 0 →
      (f u - u) / u ^ 2 = G₂ u + (1 + u * G₂ u) ^ 2 * star (G₂ (star (G u))) := by
    intro u hu
    have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
    rw [hFexp u, hGexp u]
    field_simp
    ring
  have hball : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ ball 0 r :=
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hb.hr) (fun u hu => hu)).filter_mono
      nhdsWithin_le_nhds
  have hlimf : Tendsto (fun u : ℂ => (f u - u) / u ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hev : (fun u : ℂ => (f u - u) / u ^ 2) =ᶠ[𝓝[≠] (0 : ℂ)] h := by
      filter_upwards [hball, self_mem_nhdsWithin] with u hu hu'
      have hu0 : u ≠ 0 := by simpa using hu'
      rw [hb.f_eq u hu]
      field_simp
      ring
    have h1 : Tendsto h (𝓝[≠] (0 : ℂ)) (𝓝 (h 0)) :=
      hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [hh0] at h1
    exact h1.congr' hev.symm
  have hnum : Tendsto (fun z : ℂ => star (G₂ z)) (𝓝[≠] (0 : ℂ)) (𝓝 (star c)) := by
    have h : Tendsto G₂ (𝓝[≠] (0 : ℂ)) (𝓝 (G₂ 0)) :=
      hG₂c.tendsto.mono_left nhdsWithin_le_nhds
    have h' : Tendsto (fun z : ℂ => star (G₂ z)) (𝓝[≠] (0 : ℂ)) (𝓝 (star (G₂ 0))) := h.star
    simpa [hcdef] using h'
  have hlimG : Tendsto (fun u : ℂ => G₂ u + (1 + u * G₂ u) ^ 2 * star (G₂ (star (G u))))
      (𝓝[≠] (0 : ℂ)) (𝓝 (c + star c)) := by
    have h1 : Tendsto (fun u : ℂ => G₂ u) (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
      have h : Tendsto G₂ (𝓝[≠] (0 : ℂ)) (𝓝 (G₂ 0)) :=
        hG₂c.tendsto.mono_left nhdsWithin_le_nhds
      simpa [hcdef] using h
    have h2 : Tendsto (fun u : ℂ => (1 + u * G₂ u) ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
      have h : Tendsto (fun u : ℂ => 1 + u * G₂ u) (𝓝[≠] (0 : ℂ)) (𝓝 (1 + 0 * G₂ 0)) :=
        (continuousAt_const.add (continuousAt_id.mul hG₂c)).tendsto.mono_left nhdsWithin_le_nhds
      have h3 : (1:ℂ) + 0 * G₂ 0 = 1 := by ring
      rw [h3] at h
      simpa using h.pow 2
    have h4 : Tendsto (fun u : ℂ => star (G₂ (star (G u)))) (𝓝[≠] (0 : ℂ)) (𝓝 (star c)) := by
      have hGu : Tendsto (fun u : ℂ => star (G u)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        have h : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) :=
          hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        rw [hG0] at h
        simpa using h.star
      have h := (hG₂c.tendsto.comp hGu).star
      simpa [hcdef] using h
    have h5 := h1.add (h2.mul h4)
    simpa using h5
  have hcc : c + star c = 1 := by
    have hev : (fun u : ℂ => (f u - u) / u ^ 2) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u : ℂ => G₂ u + (1 + u * G₂ u) ^ 2 * star (G₂ (star (G u)))) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hkey u (by simpa using hu)
    have h2 : Tendsto (fun u : ℂ => (f u - u) / u ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 (c + star c)) :=
      hlimG.congr' hev.symm
    exact (tendsto_nhds_unique hlimf h2).symm
  have hcre : c.re = 1 / 2 := by
    have h1 : (c + star c).re = (1 : ℂ).re := congrArg Complex.re hcc
    rw [Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re] at h1
    linarith
  -- ## The limit of `-1/g z + 1/star z`
  obtain ⟨η, hηpos, hηb⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, ‖z‖ < η → ‖G₂ z‖ ≤ ‖c‖ + 1 := by
    rw [Metric.continuousAt_iff] at hG₂c
    obtain ⟨η, hη, hηb⟩ := hG₂c 1 (by norm_num)
    refine ⟨η, hη, fun z hz => ?_⟩
    have h1 : dist (G₂ z) (G₂ 0) < 1 := hηb (by simpa [dist_eq_norm] using hz)
    rw [dist_eq_norm] at h1
    have h2 : ‖G₂ z‖ ≤ ‖G₂ z - G₂ 0‖ + ‖G₂ 0‖ := by
      calc ‖G₂ z‖ = ‖(G₂ z - G₂ 0) + G₂ 0‖ := by ring_nf
        _ ≤ ‖G₂ z - G₂ 0‖ + ‖G₂ 0‖ := norm_add_le _ _
    have h3 : ‖G₂ 0‖ = ‖c‖ := by rw [hcdef]
    rw [h3] at h2
    linarith
  set K : ℝ := ‖c‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set δ₀ : ℝ := min η (1 / (2 * K)) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min hηpos (by positivity)
  have hδ₀η : δ₀ ≤ η := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀inv : δ₀ ≤ 1 / (2 * K) := by rw [hδ₀def]; exact min_le_right _ _
  have hden : ∀ z : ℂ, ‖z‖ < δ₀ → 1 + star z * star (G₂ z) ≠ 0 := by
    intro z hz h0
    have h1 : star z * star (G₂ z) = -1 := by linear_combination h0
    have h2 : ‖star z * star (G₂ z)‖ = 1 := by rw [h1, norm_neg, norm_one]
    rw [norm_mul, norm_star, norm_star] at h2
    have h3 : ‖G₂ z‖ ≤ K := by
      rw [hKdef]
      exact hηb z (lt_of_lt_of_le hz hδ₀η)
    have h4 : ‖z‖ * ‖G₂ z‖ ≤ ‖z‖ * K := mul_le_mul_of_nonneg_left h3 (norm_nonneg z)
    have h5 : ‖z‖ < 1 / (2 * K) := lt_of_lt_of_le hz hδ₀inv
    have h6 : ‖z‖ * K < (1 / (2 * K)) * K := mul_lt_mul_of_pos_right h5 hKpos
    have h7 : (1 / (2 * K)) * K = 1 / 2 := by field_simp
    linarith
  have hΦeq : ∀ z : ℂ, z ≠ 0 → 1 + star z * star (G₂ z) ≠ 0 →
      -1 / g z + 1 / star z = star (G₂ z) / (1 + star z * star (G₂ z)) := by
    intro z hz hd
    have hzstar : star z ≠ 0 := by simpa [star_eq_zero] using hz
    have hg : g z = star z * (1 + star z * star (G₂ z)) := by
      have h2 : g z = star (G z) := by simp [hGdef]
      rw [h2, hGexp z]
      simp only [star_add, star_mul, star_pow]
      ring
    rw [hg]
    field_simp
    ring
  have hsmallδ₀ : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ < δ₀ :=
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hδ₀pos)
      (fun z hz => by simpa [dist_eq_norm] using hz)).filter_mono nhdsWithin_le_nhds
  have hΦlim : Tendsto (fun z : ℂ => -1 / g z + 1 / star z) (𝓝[≠] (0 : ℂ)) (𝓝 (star c)) := by
    have hev : (fun z : ℂ => -1 / g z + 1 / star z) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ => star (G₂ z) / (1 + star z * star (G₂ z))) := by
      filter_upwards [self_mem_nhdsWithin, hsmallδ₀] with z hz hzs
      exact hΦeq z (by simpa using hz) (hden z hzs)
    have hdenlim : Tendsto (fun z : ℂ => 1 + star z * star (G₂ z)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
      have h1 : Tendsto (fun z : ℂ => star z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        have h : Tendsto (fun z : ℂ => z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
          (continuousAt_id (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
        simpa using h.star
      have h2 : Tendsto (fun z : ℂ => 1 + star z * star (G₂ z)) (𝓝[≠] (0 : ℂ))
          (𝓝 (1 + 0 * star c)) := tendsto_const_nhds.add (h1.mul hnum)
      simpa using h2
    have hR : Tendsto (fun z : ℂ => star (G₂ z) / (1 + star z * star (G₂ z)))
        (𝓝[≠] (0 : ℂ)) (𝓝 (star c)) := by
      have h := Tendsto.div hnum hdenlim one_ne_zero
      rw [show (star c) / 1 = star c by rw [div_one]] at h
      have h2 : (fun z : ℂ => star (G₂ z)) / (fun z : ℂ => 1 + star z * star (G₂ z))
          = fun z : ℂ => star (G₂ z) / (1 + star z * star (G₂ z)) := rfl
      rwa [h2] at h
    exact hR.congr' hev.symm
  have hbound : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < δ →
      (1 : ℝ) / 4 ≤ (-1 / g z + 1 / star z).re := by
    have h1 : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖-1 / g z + 1 / star z - star c‖ < 1 / 8 := by
      filter_upwards [hΦlim.eventually
        (Metric.ball_mem_nhds (star c) (by norm_num : (0 : ℝ) < 1 / 8))] with z hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.mp h1
    refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
    have hzball : z ∈ Metric.ball (0 : ℂ) δ := by simpa [dist_eq_norm] using hzδ
    have h3 : ‖-1 / g z + 1 / star z - star c‖ < 1 / 8 :=
      hδb ⟨hzball, by simpa using hz⟩
    have h4 : -(1 / 8 : ℝ) < (-1 / g z + 1 / star z - star c).re := by
      have h5 := Complex.abs_re_le_norm (-1 / g z + 1 / star z - star c)
      have h6 : |(-1 / g z + 1 / star z - star c).re| < 1 / 8 := lt_of_le_of_lt h5 h3
      linarith [(abs_lt.mp h6).1]
    have h5 : (star c).re = 1 / 2 := by
      rw [Complex.star_def, Complex.conj_re]
      exact hcre
    rw [Complex.sub_re] at h4
    linarith
  -- ## Assembly
  obtain ⟨δ, hδpos, hδb⟩ := hbound
  refine ⟨max 1 (1 / δ), by positivity, fun W hW => ?_⟩
  have hM1 : (1 : ℝ) ≤ max 1 (1 / δ) := le_max_left _ _
  have hMδ : 1 / δ ≤ max 1 (1 / δ) := le_max_right _ _
  have hMpos : 0 < max 1 (1 / δ) := lt_of_lt_of_le one_pos hM1
  have hWpos : 0 < W.re := lt_of_le_of_lt hMpos.le hW
  have hWne : W ≠ 0 := by
    intro h0
    rw [h0] at hW
    simp at hW
    linarith
  have hWnorm : max 1 (1 / δ) < ‖W‖ := lt_of_lt_of_le hW (Complex.re_le_norm W)
  have hznorm : ‖-1 / W‖ < δ := by
    rw [norm_div, norm_neg, norm_one]
    have h1 : 1 / ‖W‖ < 1 / (max 1 (1 / δ)) := one_div_lt_one_div_of_lt hMpos hWnorm
    have h2 : 1 / (max 1 (1 / δ)) ≤ δ := by
      rw [div_le_iff₀ hMpos]
      have h4 : δ * (1 / δ) = 1 := by field_simp
      calc (1 : ℝ) = δ * (1 / δ) := h4.symm
        _ ≤ δ * max 1 (1 / δ) := mul_le_mul_of_nonneg_left hMδ hδpos.le
    linarith
  have hzne : -1 / W ≠ 0 := by
    simp [hWne]
  have h1 := hδb (-1 / W) hzne hznorm
  have hstar : (1 / star (-1 / W)).re = -W.re := by
    rw [show 1 / star (-1 / W) = -star W from by
      have h1 : star (-1 / W) = -(1 / star W) := by
        rw [show (-1 / W : ℂ) = -(1 / W) by ring, star_neg]
        congr 1
        simp
      rw [h1]
      have h2 : star W ≠ 0 := by simpa [star_eq_zero] using hWne
      field_simp]
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re]
  rw [show Work.FatouCoord.Flower.gChart g W = -1 / g (-1 / W) from rfl]
  have h2 : (-1 / g (-1 / W) + 1 / star (-1 / W)).re
      = (-1 / g (-1 / W)).re + (1 / star (-1 / W)).re := Complex.add_re _ _
  rw [h2, hstar] at h1
  linarith

end Work.FatouCoordFix.FlowerFix
