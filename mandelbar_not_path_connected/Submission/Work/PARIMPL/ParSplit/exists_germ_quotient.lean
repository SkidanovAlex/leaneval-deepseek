import Mathlib
import Submission.Work.PARIMPL.ParSplit.Basic
import Submission.Work.PARIMPL.ParSplit.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

/-- **The germ quotient is continuous.**  Let `F` be entire, `m, s, a ∈ ℂ` with `a ≠ 0`, `s ≠ 0`,
and suppose `F (m + s a) = m + s a`, `F (m - s a) = m - s a` with the two fixed points *simple*
(`deriv F (m ± s a) ≠ 1`).  Then the germ
`ζ ↦ (F (m + s ζ) - m - s ζ)/(s (ζ² - a²))` extends continuously to the two points `ζ = ±a`
(because the numerator and the denominator both vanish there to first order), giving a function `h`
on the unit ball with
`F (m + s ζ) = m + s (ζ + (ζ² - a²) h ζ)`,  and `h a, h (-a) ≠ 0`.

The construction is the partial-fraction decomposition
`1/((ζ-a)(ζ+a)) = (1/2a) (1/(ζ-a) - 1/(ζ+a))`:  the quotient of the entire function
`P ζ = F (m + s ζ) - m - s ζ` by `ζ - a` (resp. `ζ + a`) extends continuously to `a`
(resp. `-a`) with value `P'(a)` (resp. `P'(-a)`), by `HasDerivAt.continuousAt_div`. -/
theorem exists_germ_quotient {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m s a : ℂ} (ha : a ≠ 0) (hs : s ≠ 0)
    (hadd : F (m + s * a) = m + s * a) (hsub : F (m - s * a) = m - s * a)
    (hdadd : deriv F (m + s * a) ≠ 1) (hdsub : deriv F (m - s * a) ≠ 1) :
    ∃ h : ℂ → ℂ, ContinuousOn h (Metric.ball 0 1) ∧
      (∀ ζ, ‖ζ‖ < 1 → F (m + s * ζ) = m + s * (ζ + (ζ ^ 2 - a ^ 2) * h ζ)) ∧
      (‖a‖ < 1 → h a ≠ 0 ∧ h (-a) ≠ 0) := by
  classical
  -- `P ζ = F (m + s ζ) - m - s ζ` is entire with `P (a) = P (-a) = 0`.
  set P : ℂ → ℂ := fun z => F (m + s * z) - (m + s * z) with hPdef
  have hPdiff : Differentiable ℂ P := by
    rw [hPdef]; exact (hF.comp (by fun_prop)).sub (by fun_prop)
  have hPcont : Continuous P := hPdiff.continuous
  have hPa : P a = 0 := by simp only [hPdef]; rw [hadd]; ring
  have hPna : P (-a) = 0 := by
    simp only [hPdef]
    have h : m + s * (-a) = m - s * a := by ring
    rw [h, hsub]; ring
  -- The derivative of `P`.
  have hderivP : ∀ z, deriv P z = s * (deriv F (m + s * z) - 1) := by
    intro z
    simp only [hPdef]
    have hφd : DifferentiableAt ℂ (fun w : ℂ => m + s * w) z := by fun_prop
    have hFφd : DifferentiableAt ℂ (fun w : ℂ => F (m + s * w)) z :=
      hF.differentiableAt.comp z hφd
    have hφ' : deriv (fun w : ℂ => m + s * w) z = s := by
      rw [show (fun w : ℂ => m + s * w) = (fun w => m + (fun y => s * y) w) from rfl]
      rw [deriv_const_add, deriv_const_mul_id]
    have hFφ' : deriv (fun w : ℂ => F (m + s * w)) z = deriv F (m + s * z) * s := by
      rw [show (fun w : ℂ => F (m + s * w)) = F ∘ (fun w : ℂ => m + s * w) from rfl,
          deriv_comp z hF.differentiableAt hφd]
      rw [hφ']
    rw [show (fun w : ℂ => F (m + s * w) - (m + s * w))
        = (fun w : ℂ => F (m + s * w)) - (fun w : ℂ => m + s * w) from rfl]
    rw [deriv_sub hFφd hφd, hFφ', hφ']
    ring
  have hdPa : deriv P a ≠ 0 := by
    rw [hderivP a]; exact mul_ne_zero hs (sub_ne_zero.mpr hdadd)
  have hdPna : deriv P (-a) ≠ 0 := by
    rw [hderivP (-a)]
    have h : m + s * (-a) = m - s * a := by ring
    rw [h]; exact mul_ne_zero hs (sub_ne_zero.mpr hdsub)
  -- The two continuous extensions of `P ζ / (ζ - a)` and `P ζ / (ζ + a)`.
  set A : ℂ → ℂ := Function.update (fun z => (P z - P a) / (z - a)) a (deriv P a) with hA
  set B : ℂ → ℂ := Function.update (fun z => (P z - P (-a)) / (z - (-a))) (-a) (deriv P (-a)) with hB
  have hAcont : Continuous A := by
    rw [hA, continuous_iff_continuousAt]; intro z
    by_cases hz : z = a
    · subst hz; exact hPdiff.differentiableAt.hasDerivAt.continuousAt_div
    · exact ContinuousAt.congr
        (f := fun z => (P z - P a) / (z - a))
        (g := Function.update (fun z => (P z - P a) / (z - a)) a (deriv P a))
        ((hPcont.continuousAt.sub continuousAt_const).div
          (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hz))
        (by filter_upwards [eventually_ne_nhds hz] with w hw
            exact (Function.update_of_ne (β := fun _ => ℂ) hw (deriv P a)
              (fun z => (P z - P a)/(z - a))).symm)
  have hBcont : Continuous B := by
    rw [hB, continuous_iff_continuousAt]; intro z
    by_cases hz : z = -a
    · subst hz; exact hPdiff.differentiableAt.hasDerivAt.continuousAt_div
    · exact ContinuousAt.congr
        (f := fun z => (P z - P (-a)) / (z - (-a)))
        (g := Function.update (fun z => (P z - P (-a)) / (z - (-a))) (-a) (deriv P (-a)))
        ((hPcont.continuousAt.sub continuousAt_const).div
          (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hz))
        (by filter_upwards [eventually_ne_nhds hz] with w hw
            exact (Function.update_of_ne (β := fun _ => ℂ) hw (deriv P (-a))
              (fun z => (P z - P (-a))/(z - (-a)))).symm)
  -- The quotient `h = (A - B)/(2 a s)`.
  set h : ℂ → ℂ := fun z => (2 * a * s)⁻¹ * (A z - B z) with hh
  have haa : a ≠ -a := by
    intro hcon; exact ha (by linear_combination (1/2 : ℂ) * hcon)
  have h2as : 2 * a * s ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero ha) hs
  -- The partial-fraction numerator identity `(ζ²-a²)(A ζ - B ζ) = 2 a P ζ`.
  have hkey : ∀ z, (z ^ 2 - a ^ 2) * (A z - B z) = 2 * a * P z := by
    intro z
    rcases eq_or_ne z a with rfl | hza
    · rw [hPa]; ring
    · rcases eq_or_ne z (-a) with rfl | hzna
      · rw [hPna]; ring
      · have hzA : A z = (P z - P a) / (z - a) := by
          rw [hA]
          exact Function.update_of_ne (β := fun _ => ℂ) hza (deriv P a)
            (fun z => (P z - P a) / (z - a))
        have hzB : B z = (P z - P (-a)) / (z - (-a)) := by
          rw [hB]
          exact Function.update_of_ne (β := fun _ => ℂ) hzna (deriv P (-a))
            (fun z => (P z - P (-a)) / (z - (-a)))
        rw [hzA, hzB, hPa, hPna]
        have h1 : z - a ≠ 0 := sub_ne_zero.mpr hza
        have h2 : z - (-a) ≠ 0 := sub_ne_zero.mpr hzna
        field_simp; ring
  have hsc : s * (2 * a * s)⁻¹ * (2 * a) = 1 := by
    rw [show s * (2 * a * s)⁻¹ * (2 * a) = (2 * a) * s * (2 * a * s)⁻¹ by ring]
    rw [mul_inv_cancel₀ h2as]
  -- The defining identity of `h`.
  have hmain : ∀ z, s * (z ^ 2 - a ^ 2) * h z = P z := by
    intro z
    calc s * (z ^ 2 - a ^ 2) * h z
        = s * (z ^ 2 - a ^ 2) * ((2 * a * s)⁻¹ * (A z - B z)) := by simp only [hh]
      _ = s * (2 * a * s)⁻¹ * ((z ^ 2 - a ^ 2) * (A z - B z)) := by ring
      _ = s * (2 * a * s)⁻¹ * (2 * a * P z) := by rw [hkey z]
      _ = (s * (2 * a * s)⁻¹ * (2 * a)) * P z := by ring
      _ = P z := by rw [hsc, one_mul]
  refine ⟨h, ?_, ?_, ?_⟩
  · have hcont : Continuous h := by
      simp only [hh]; exact (hAcont.sub hBcont).const_mul ((2 * a * s)⁻¹)
    exact hcont.continuousOn
  · intro ζ _
    have hval : F (m + s * ζ) = P ζ + (m + s * ζ) := by simp only [hPdef]; ring
    rw [hval]
    rw [show s * (ζ + (ζ ^ 2 - a ^ 2) * h ζ) = s * ζ + s * (ζ ^ 2 - a ^ 2) * h ζ by ring,
        hmain ζ]
    ring
  · intro _
    have hAa : A a = deriv P a := by rw [hA]; simp
    have hBa : B a = 0 := by
      rw [hB, Function.update_of_ne (β := fun _ => ℂ) haa (deriv P (-a))
        (fun z => (P z - P (-a))/(z - (-a)))]
      rw [hPa, hPna]; ring
    have hA_na : A (-a) = 0 := by
      rw [hA, Function.update_of_ne (β := fun _ => ℂ) (Ne.symm haa) (deriv P a)
        (fun z => (P z - P a)/(z - a))]
      rw [hPa, hPna]; ring
    have hB_na : B (-a) = deriv P (-a) := by rw [hB]; simp
    refine ⟨?_, ?_⟩
    · rw [show h a = (2 * a * s)⁻¹ * deriv P a by simp only [hh, hAa, hBa]; ring]
      exact mul_ne_zero (inv_ne_zero h2as) hdPa
    · rw [show h (-a) = (2 * a * s)⁻¹ * (-(deriv P (-a))) by
            simp only [hh, hA_na, hB_na]; ring]
      exact mul_ne_zero (inv_ne_zero h2as) (neg_ne_zero.mpr hdPna)

end Work.PARIMPL.ParSplit
