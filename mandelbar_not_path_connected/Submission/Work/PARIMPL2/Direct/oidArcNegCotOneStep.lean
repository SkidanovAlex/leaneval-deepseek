import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- The cotangent `t ↦ cos t / sin t` is antitone on `(0, π)`: for `0 < c ≤ y < π` we have
`cos y / sin y ≤ cos c / sin c`.  This is the elementary identity
`cot c - cot y = sin (y - c) / (sin c * sin y) ≥ 0`. -/
theorem oidArcNegCotOneStep_cot_mono {c y : ℝ} (hc : 0 < c) (hcy : c ≤ y)
    (hy : y < Real.pi) :
    Real.cos y / Real.sin y ≤ Real.cos c / Real.sin c := by
  have hsc : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc (lt_of_le_of_lt hcy hy)
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hc hcy) hy
  have hkey : Real.cos c / Real.sin c - Real.cos y / Real.sin y
      = Real.sin (y - c) / (Real.sin c * Real.sin y) := by
    field_simp
    rw [Real.sin_sub]
    ring
  have hle : 0 ≤ Real.sin (y - c) / (Real.sin c * Real.sin y) := by
    apply div_nonneg
    · exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    · positivity
  have hdiff_nonneg : 0 ≤ Real.cos c / Real.sin c - Real.cos y / Real.sin y := by
    rw [hkey]; exact hle
  linarith

/-- One-step mean-value bound for `t ↦ log (sin t)`: if `0 < x`, `0 < h` and `x + h ≤ y ≤ π/2`
then `h · cot y ≤ (π/2) · (log (sin y) - log (sin x))`.

The mean value theorem gives some `c ∈ (x, y)` with
`log (sin y) - log (sin x) = (y - x) · cot c`; since `c < y` and `cot` is antitone on `(0, π)`,
`cot c ≥ cot y ≥ 0`, and `y - x ≥ h`.  Multiplying by `π/2 ≥ 1` finishes. -/
theorem oidArcNegCotOneStep (x y h : ℝ) (hh : 0 < h) (hx : 0 < x)
    (hgap : x + h ≤ y) (hy : y ≤ Real.pi / 2) :
    h * (Real.cos y / Real.sin y)
      ≤ (Real.pi / 2) * (Real.log (Real.sin y) - Real.log (Real.sin x)) := by
  have hxlt : x < y := by linarith
  have hypos : 0 < y := by linarith
  have hypi : y < Real.pi := by linarith [Real.pi_gt_three]
  have hcont : ContinuousOn (fun t => Real.log (Real.sin t)) (Set.Icc x y) := by
    refine ContinuousOn.log Real.continuous_sin.continuousOn ?_
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, hypi]))
  have hdiff : DifferentiableOn ℝ (fun t => Real.log (Real.sin t)) (Set.Ioo x y) := by
    intro t ht
    have hsin : Real.sin t ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, hypi]))
    exact ((Real.hasDerivAt_sin t).log hsin).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope (fun t => Real.log (Real.sin t)) hxlt hcont hdiff
  have hc_pos : 0 < c := by linarith [hc.1]
  have hc_lt : c < y := hc.2
  have hsin_c : Real.sin c ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hc.1]) (by linarith [hc.2, hypi]))
  have hderiv_c : deriv (fun t => Real.log (Real.sin t)) c = Real.cos c / Real.sin c :=
    ((Real.hasDerivAt_sin c).log hsin_c).deriv
  have hslope : Real.log (Real.sin y) - Real.log (Real.sin x)
      = (y - x) * (Real.cos c / Real.sin c) := by
    have hne : y - x ≠ 0 := by linarith
    have h1 : (Real.log (Real.sin y) - Real.log (Real.sin x)) / (y - x)
        = Real.cos c / Real.sin c := by
      rw [← hceq]; exact hderiv_c
    rw [div_eq_iff hne] at h1
    rw [h1, mul_comm]
  have hmono : Real.cos y / Real.sin y ≤ Real.cos c / Real.sin c :=
    oidArcNegCotOneStep_cot_mono hc_pos (le_of_lt hc_lt) hypi
  have hA_ge : (y - x) * (Real.cos y / Real.sin y)
      ≤ Real.log (Real.sin y) - Real.log (Real.sin x) := by
    rw [hslope]
    exact mul_le_mul_of_nonneg_left hmono (by linarith)
  have hcoty_nn : 0 ≤ Real.cos y / Real.sin y := by
    have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hypos hypi
    exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hypos], by linarith⟩) (le_of_lt hsy)
  have hgap' : h ≤ y - x := by linarith
  have hstep : h * (Real.cos y / Real.sin y) ≤ (y - x) * (Real.cos y / Real.sin y) :=
    mul_le_mul_of_nonneg_right hgap' hcoty_nn
  have hA_h : h * (Real.cos y / Real.sin y)
      ≤ Real.log (Real.sin y) - Real.log (Real.sin x) := le_trans hstep hA_ge
  have hA_nn : 0 ≤ Real.log (Real.sin y) - Real.log (Real.sin x) :=
    le_trans (mul_nonneg (le_of_lt hh) hcoty_nn) hA_h
  have hpi2 : (1:ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  calc h * (Real.cos y / Real.sin y)
      ≤ Real.log (Real.sin y) - Real.log (Real.sin x) := hA_h
    _ = 1 * (Real.log (Real.sin y) - Real.log (Real.sin x)) := by ring
    _ ≤ (Real.pi / 2) * (Real.log (Real.sin y) - Real.log (Real.sin x)) :=
        mul_le_mul_of_nonneg_right hpi2 hA_nn

end Work.PARIMPL2.Direct
