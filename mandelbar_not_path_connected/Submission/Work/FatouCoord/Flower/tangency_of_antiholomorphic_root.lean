/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The antiholomorphic square root of a parabolic germ is tangent to conjugation
-/


open scoped Topology
open Filter Metric

namespace Work.FatouCoord.Flower

noncomputable section

theorem tangency_of_antiholomorphic_root {G f h : ℂ → ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hf : ∀ u : ℂ, ‖u‖ < ρ → f u = star (G (star (G u))))
    (hfh : ∀ u : ℂ, ‖u‖ < ρ → f u = u + u ^ 2 * h u)
    (hh : DifferentiableAt ℂ h 0) (hh0 : h 0 = 1) (ha : deriv h 0 = a) :
    deriv G 0 = 1 ∧ star a = a := by
  obtain ⟨g, hgan, hgeq⟩ := hG.exists_eq_sum_add_pow_mul 4
  set ν : ℂ := iteratedDeriv 1 G 0 with hν
  set c : ℂ := iteratedDeriv 2 G 0 / 2 with hc
  set d : ℂ := iteratedDeriv 3 G 0 / 6 with hd
  have hGexp : ∀ z : ℂ, G z = ν * z + c * z ^ 2 + d * z ^ 3 + z ^ 4 * g z := by
    intro z
    rw [hgeq z]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [hG0, iteratedDeriv_zero, iteratedDeriv_one, hν, hc, hd]
    norm_num
    ring
  -- the auxiliary functions
  set Ĕ : ℂ → ℂ := fun u => c + d * u + u ^ 2 * g u with hĔ
  set ĝ : ℂ → ℂ := fun u => star (g (star (G u))) with hĝ
  have hGfac : ∀ u : ℂ, G u = u * (ν + u * Ĕ u) := by
    intro u
    rw [hGexp u, hĔ]; ring
  -- the ball and the punctured neighbourhood
  have hball : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ ball 0 ρ := by
    have h1 : ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ ball 0 ρ :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hρ) (fun u hu => hu)
    exact h1.filter_mono nhdsWithin_le_nhds
  have hid : Tendsto (fun u : ℂ => u) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  -- continuity of the auxiliaries
  have hGcont : ContinuousAt G 0 := hG.continuousAt
  have hĔc : ContinuousAt Ĕ 0 := by
    have hcont : ContinuousAt (fun u : ℂ => c + d * u + u ^ 2 * g u) 0 :=
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).add
        ((continuousAt_id.pow 2).mul hgan.continuousAt)
    rw [← hĔ] at hcont
    exact hcont
  have hĔ0 : Ĕ 0 = c := by rw [hĔ]; simp
  have hĔcont : Tendsto Ĕ (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
    have h1 : Tendsto Ĕ (𝓝[≠] (0 : ℂ)) (𝓝 (Ĕ 0)) :=
      hĔc.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hĔ0] at h1
  have hĔslope : Tendsto (fun u : ℂ => (Ĕ u - c) / u) (𝓝[≠] (0 : ℂ)) (𝓝 d) := by
    have hev : (fun u : ℂ => (Ĕ u - c) / u) =ᶠ[𝓝[≠] (0 : ℂ)] (fun u : ℂ => d + u * g u) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := by simpa using hu
      rw [hĔ]
      field_simp
      ring
    have hcont : ContinuousAt (fun u : ℂ => d + u * g u) 0 :=
      continuousAt_const.add (continuousAt_id.mul hgan.continuousAt)
    have h1 : Tendsto (fun u : ℂ => d + u * g u) (𝓝[≠] (0 : ℂ)) (𝓝 (d + 0 * g 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [show d + 0 * g 0 = d by ring] at h1
    exact h1.congr' hev.symm
  have hĝcont : Tendsto ĝ (𝓝[≠] (0 : ℂ)) (𝓝 (star (g 0))) := by
    have h1 : Tendsto (fun u : ℂ => star (G u)) (𝓝 (0 : ℂ)) (𝓝 (star (G 0))) :=
      hGcont.tendsto.star
    rw [hG0, star_zero] at h1
    have h2 : Tendsto (fun u : ℂ => g (star (G u))) (𝓝 (0 : ℂ)) (𝓝 (g 0)) :=
      hgan.continuousAt.tendsto.comp h1
    have h3 : Tendsto (fun u : ℂ => star (g (star (G u)))) (𝓝 (0 : ℂ)) (𝓝 (star (g 0))) :=
      h2.star
    have h4 : Tendsto (fun u : ℂ => star (g (star (G u)))) (𝓝[≠] (0 : ℂ)) (𝓝 (star (g 0))) :=
      h3.mono_left nhdsWithin_le_nhds
    rwa [← hĝ] at h4
  -- `A u = G u / u` tends to `ν`, and its slope to `c`
  have hA : Tendsto (fun u : ℂ => G u / u) (𝓝[≠] (0 : ℂ)) (𝓝 ν) := by
    have hev : (fun u : ℂ => G u / u) =ᶠ[𝓝[≠] (0 : ℂ)] (fun u : ℂ => ν + u * Ĕ u) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := by simpa using hu
      rw [hGfac u]
      field_simp
    have hcont : ContinuousAt (fun u : ℂ => ν + u * Ĕ u) 0 :=
      continuousAt_const.add (continuousAt_id.mul hĔc)
    have h1 : Tendsto (fun u : ℂ => ν + u * Ĕ u) (𝓝[≠] (0 : ℂ)) (𝓝 (ν + 0 * Ĕ 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [hĔ0] at h1
    rw [show ν + 0 * c = ν by ring] at h1
    exact h1.congr' hev.symm
  have hAslope : Tendsto (fun u : ℂ => (G u / u - ν) / u) (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
    have hev : Ĕ =ᶠ[𝓝[≠] (0 : ℂ)] (fun u : ℂ => (G u / u - ν) / u) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := by simpa using hu
      rw [hGfac u]
      field_simp
      ring
    exact hĔcont.congr' hev
  -- the exact expression of `f` through `G`
  have hI1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), f u = star ν * G u + star c * (G u) ^ 2 + star d * (G u) ^ 3
      + (G u) ^ 4 * ĝ u := by
    filter_upwards [hball, self_mem_nhdsWithin] with u hu hu'
    rw [hf u (mem_ball_zero_iff.mp hu), hGexp (star (G u)), hĝ]
    simp only [star_add, star_mul, star_pow, star_star]
    ring
  -- limits of `f`
  have hf1 : Tendsto (fun u : ℂ => f u / u) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hev : (fun u : ℂ => f u / u) =ᶠ[𝓝[≠] (0 : ℂ)] (fun u : ℂ => 1 + u * h u) := by
      filter_upwards [hball, self_mem_nhdsWithin] with u hu hu'
      have hu0 : u ≠ 0 := by simpa using hu'
      rw [hfh u (mem_ball_zero_iff.mp hu)]
      field_simp
    have h1 : Tendsto (fun u : ℂ => 1 + u * h u) (𝓝[≠] (0 : ℂ)) (𝓝 (1 + 0 * h 0)) :=
      tendsto_const_nhds.add (hid.mul (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
    rw [hh0, zero_mul, add_zero] at h1
    exact h1.congr' hev.symm
  have hf2 : Tendsto (fun u : ℂ => (f u - u) / u ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hev : (fun u : ℂ => (f u - u) / u ^ 2) =ᶠ[𝓝[≠] (0 : ℂ)] h := by
      filter_upwards [hball, self_mem_nhdsWithin] with u hu hu'
      have hu0 : u ≠ 0 := by simpa using hu'
      rw [hfh u (mem_ball_zero_iff.mp hu)]
      field_simp
      ring
    have h1 : Tendsto h (𝓝[≠] (0 : ℂ)) (𝓝 (h 0)) :=
      hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [hh0] at h1
    exact h1.congr' hev.symm
  have hf3 : Tendsto (fun u : ℂ => (f u - u - u ^ 2) / u ^ 3) (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
    have hev : (fun u : ℂ => (f u - u - u ^ 2) / u ^ 3) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u : ℂ => (h u - h 0) / u) := by
      filter_upwards [hball, self_mem_nhdsWithin] with u hu hu'
      have hu0 : u ≠ 0 := by simpa using hu'
      rw [hfh u (mem_ball_zero_iff.mp hu)]
      field_simp
      rw [hh0]
      ring
    have h1 : Tendsto (fun u : ℂ => (h u - h 0) / u) (𝓝[≠] (0 : ℂ)) (𝓝 (deriv h 0)) := by
      have h2 := hh.hasDerivAt.tendsto_slope (x := (0 : ℂ))
      have h3 : (fun u : ℂ => (h u - h 0) / u) = fun u : ℂ => (u - 0)⁻¹ • (h u - h 0) := by
        funext u; rw [sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [h3]; exact h2
    rw [ha] at h1
    exact h1.congr' hev.symm
  -- the `G`-side limit of `f u / u`
  have hL1 : Tendsto (fun u : ℂ => f u / u) (𝓝[≠] (0 : ℂ)) (𝓝 (star ν * ν)) := by
    have hev : (fun u : ℂ => f u / u) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u : ℂ => star ν * (G u / u) + star c * u * (G u / u) ^ 2
          + star d * u ^ 2 * (G u / u) ^ 3 + u ^ 3 * (G u / u) ^ 4 * ĝ u) := by
      filter_upwards [hI1, self_mem_nhdsWithin] with u h1 hu
      have hu0 : u ≠ 0 := by simpa using hu
      rw [h1, hGfac u]
      field_simp
      try ring
    have h2 : Tendsto (fun u : ℂ => star ν * (G u / u) + star c * u * (G u / u) ^ 2
        + star d * u ^ 2 * (G u / u) ^ 3 + u ^ 3 * (G u / u) ^ 4 * ĝ u) (𝓝[≠] (0 : ℂ))
        (𝓝 (star ν * ν + star c * 0 * ν ^ 2 + star d * 0 ^ 2 * ν ^ 3
          + 0 ^ 3 * ν ^ 4 * star (g 0))) :=
      ((((hA.const_mul (star ν)).add ((hid.const_mul (star c)).mul (hA.pow 2))).add
        (((hid.pow 2).const_mul (star d)).mul (hA.pow 3))).add
        (((hid.pow 3).mul (hA.pow 4)).mul hĝcont))
    rw [show star ν * ν + star c * 0 * ν ^ 2 + star d * 0 ^ 2 * ν ^ 3
        + 0 ^ 3 * ν ^ 4 * star (g 0) = star ν * ν by ring] at h2
    exact h2.congr' hev.symm
  have hνν : star ν * ν = 1 := tendsto_nhds_unique hL1 hf1
  -- the identity `star ν * G u = u + star ν * u ^ 2 * Ĕ u`
  have hkey : ∀ u : ℂ, star ν * G u = u + star ν * u ^ 2 * Ĕ u := by
    intro u
    rw [hGfac u]
    have h1 : star ν * (u * (ν + u * Ĕ u)) = (star ν * ν) * u + (star ν * Ĕ u) * u ^ 2 := by
      ring
    rw [h1, hνν, one_mul]; ring
  -- the `G`-side limit of `(f u - u) / u ^ 2`
  have hL2 : Tendsto (fun u : ℂ => (f u - u) / u ^ 2) (𝓝[≠] (0 : ℂ))
      (𝓝 (star ν * c + star c * ν ^ 2)) := by
    have hev : (fun u : ℂ => (f u - u) / u ^ 2) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u : ℂ => star ν * ((G u / u - ν) / u) + star c * (G u / u) ^ 2
          + star d * u * (G u / u) ^ 3 + u ^ 2 * (G u / u) ^ 4 * ĝ u) := by
      filter_upwards [hI1, self_mem_nhdsWithin] with u h1 hu
      have hu0 : u ≠ 0 := by simpa using hu
      rw [h1, hkey u, hGfac u]
      field_simp
      try ring
    have h2 : Tendsto (fun u : ℂ => star ν * ((G u / u - ν) / u) + star c * (G u / u) ^ 2
        + star d * u * (G u / u) ^ 3 + u ^ 2 * (G u / u) ^ 4 * ĝ u) (𝓝[≠] (0 : ℂ))
        (𝓝 (star ν * c + star c * ν ^ 2 + star d * 0 * ν ^ 3
          + 0 ^ 2 * ν ^ 4 * star (g 0))) :=
      ((((hAslope.const_mul (star ν)).add ((hA.pow 2).const_mul (star c))).add
        (((hid.const_mul (star d)).mul (hA.pow 3)))).add
        (((hid.pow 2).mul (hA.pow 4)).mul hĝcont))
    rw [show star ν * c + star c * ν ^ 2 + star d * 0 * ν ^ 3 + 0 ^ 2 * ν ^ 4 * star (g 0)
        = star ν * c + star c * ν ^ 2 by ring] at h2
    exact h2.congr' hev.symm
  have hc2 : star ν * c + star c * ν ^ 2 = 1 := tendsto_nhds_unique hL2 hf2
  -- the `G`-side limit of `(f u - u - u ^ 2) / u ^ 3`
  have hL3 : Tendsto (fun u : ℂ => (f u - u - u ^ 2) / u ^ 3) (𝓝[≠] (0 : ℂ))
      (𝓝 (star ν * d + 2 * star c * ν * c + star d * ν ^ 3)) := by
    have hev : (fun u : ℂ => (f u - u - u ^ 2) / u ^ 3) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u : ℂ => star ν * ((Ĕ u - c) / u) + 2 * star c * ν * Ĕ u + u * (star c * (Ĕ u) ^ 2)
          + star d * (G u / u) ^ 3 + u * (G u / u) ^ 4 * ĝ u) := by
      filter_upwards [hI1, self_mem_nhdsWithin] with u h1 hu
      have hu0 : u ≠ 0 := by simpa using hu
      rw [h1, hkey u, hGfac u]
      field_simp
      ring_nf
      linear_combination (u : ℂ) * hc2
    have h2 : Tendsto (fun u : ℂ => star ν * ((Ĕ u - c) / u) + 2 * star c * ν * Ĕ u
        + u * (star c * (Ĕ u) ^ 2) + star d * (G u / u) ^ 3 + u * (G u / u) ^ 4 * ĝ u)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (star ν * d + 2 * star c * ν * c + 0 * (star c * c ^ 2) + star d * ν ^ 3
          + 0 * ν ^ 4 * star (g 0))) :=
      ((((hĔslope.const_mul (star ν)).add
        ((hĔcont.const_mul (2 * star c * ν)))).add
        (hid.mul ((hĔcont.pow 2).const_mul (star c)))).add
        ((hA.pow 3).const_mul (star d))).add
        (((hid.mul (hA.pow 4)).mul hĝcont))
    rw [show star ν * d + 2 * star c * ν * c + 0 * (star c * c ^ 2) + star d * ν ^ 3
        + 0 * ν ^ 4 * star (g 0) = star ν * d + 2 * star c * ν * c + star d * ν ^ 3 by ring] at h2
    exact h2.congr' hev.symm
  have ha_eq : a = star ν * d + 2 * star c * ν * c + star d * ν ^ 3 :=
    tendsto_nhds_unique hf3 hL3
  -- the algebra
  have hstarν : star ν = 1 := by
    have hA' : c + star c * ν ^ 3 = ν := by
      calc c + star c * ν ^ 3 = (star ν * ν) * c + star c * (ν ^ 2 * ν) := by
            rw [hνν, one_mul]; ring
        _ = (star ν * c + star c * ν ^ 2) * ν := by ring
        _ = ν := by rw [hc2, one_mul]
    have hB : ν * star c + star ν ^ 2 * c = 1 := by
      have h2 := congrArg star hc2
      rw [star_add, star_mul, star_mul, star_pow, star_star, star_one] at h2
      simpa [mul_comm] using h2
    have hA'' : c = ν - star c * ν ^ 3 := eq_sub_iff_add_eq.mpr hA'
    have e1 : star ν ^ 2 * ν = star ν := by
      calc star ν ^ 2 * ν = star ν * (star ν * ν) := by ring
        _ = star ν := by rw [hνν, mul_one]
    have e2 : star ν ^ 2 * (star c * ν ^ 3) = star c * ν := by
      have e : star ν ^ 2 * ν ^ 3 = ν := by
        calc star ν ^ 2 * ν ^ 3 = (star ν * ν) ^ 2 * ν := by ring
          _ = ν := by rw [hνν, one_pow, one_mul]
      calc star ν ^ 2 * (star c * ν ^ 3) = star c * (star ν ^ 2 * ν ^ 3) := by ring
        _ = star c * ν := by rw [e]
    have h4 : ν * star c + star ν ^ 2 * (ν - star c * ν ^ 3) = 1 := by
      rw [← hA'']; exact hB
    have h5 : ν * star c + star ν ^ 2 * (ν - star c * ν ^ 3) = star ν := by
      rw [mul_sub, e1, e2]; ring
    rw [h5] at h4
    exact h4
  have hν1 : ν = 1 := by
    have h2 := congrArg star hstarν
    simpa using h2
  refine ⟨?_, ?_⟩
  · rw [← iteratedDeriv_one, ← hν, hν1]
  · rw [ha_eq, hν1]
    simp only [star_add, star_mul, star_ofNat, star_one, star_star, one_mul, one_pow]
    ring

end

end Work.FatouCoord.Flower
