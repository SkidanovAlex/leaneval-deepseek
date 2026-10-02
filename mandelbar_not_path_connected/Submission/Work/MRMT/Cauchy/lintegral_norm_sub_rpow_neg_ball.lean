import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Set ENNReal Complex
open scoped ENNReal Topology

/-- The `ℝ≥0∞`-norm of a complex number is `ofReal` of its usual norm. -/
private lemma enorm_ofReal_norm (x : ℂ) : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  simp [enorm_eq_nnnorm]

/-- Pulling a (finite) constant out of a set-`lintegral`. -/
private lemma setLIntegral_mul_const' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (c : ℝ≥0∞) (hc : c ≠ ∞) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x * c ∂μ = (∫⁻ x in s, f x ∂μ) * c := by
  rw [← lintegral_indicator hs (fun x => f x * c) (μ := μ)]
  have h1 : (fun x => s.indicator (fun x => f x * c) x) = fun x => s.indicator f x * c := by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem, hx]
    · simp [Set.indicator_of_notMem, hx]
  rw [h1, lintegral_mul_const' c _ hc, lintegral_indicator hs f]

/-- **Radial integral of a real power.**  For `a > -1` and `r > 0`,
`∫⁻ x in (0,r), (ofReal x)^a = ofReal (r^(a+1)/(a+1))`. -/
private lemma lintegral_ofReal_rpow_Ioo (a r : ℝ) (ha : -1 < a) (hr : 0 < r) :
    ∫⁻ x in Set.Ioo (0:ℝ) r, (ENNReal.ofReal x) ^ a
      = ENNReal.ofReal (r ^ (a + 1) / (a + 1)) := by
  have hInt : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioo (0:ℝ) r) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr ha
  have hnonneg : 0 ≤ᵐ[volume] (Set.Ioo (0:ℝ) r).indicator (fun x : ℝ => x ^ a) := by
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioo (0:ℝ) r
    · rw [Set.indicator_of_mem hx]; exact Real.rpow_nonneg hx.1.le a
    · simp [Set.indicator_of_notMem hx]
  have hkey := ofReal_integral_eq_lintegral_ofReal (μ := volume)
      (f := (Set.Ioo (0:ℝ) r).indicator (fun x : ℝ => x ^ a))
      (hInt.integrable_indicator measurableSet_Ioo) hnonneg
  rw [integral_indicator measurableSet_Ioo] at hkey
  have hcongr : (fun x => ENNReal.ofReal ((Set.Ioo (0:ℝ) r).indicator (fun x : ℝ => x ^ a) x))
      = (Set.Ioo (0:ℝ) r).indicator (fun x => ENNReal.ofReal (x^a)) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (0:ℝ) r
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [hcongr, lintegral_indicator measurableSet_Ioo] at hkey
  rw [setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ENNReal.ofReal_rpow_of_pos hx.1)]
  rw [← hkey]
  congr 1
  have h1 : ∫ x in Set.Ioo (0:ℝ) r, x ^ a = ∫ x in Set.Ioc (0:ℝ) r, x ^ a :=
    (integral_Ioc_eq_integral_Ioo).symm
  rw [h1, ← intervalIntegral.integral_of_le hr.le, integral_rpow (Or.inl ha),
    Real.zero_rpow (by linarith : a + 1 ≠ 0), sub_zero]

/-- **The planar integral of `‖w - z‖^{-q}` over a disc, `1 < q < 2`.**  In polar coordinates
around `z` the integrand pulls back to `ρ^{1-q}`, whose radial integral on `(0,r)` is
`r^{2-q}/(2-q)`; multiplying by the angular length `2π` gives the stated value. -/
theorem lintegral_norm_sub_rpow_neg_ball (z : ℂ) {q r : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hr : 0 < r) :
    (∫⁻ w in Metric.ball z r, ‖w - z‖ₑ ^ (-q)) =
      ENNReal.ofReal (2 * Real.pi * r ^ (2 - q) / (2 - q)) := by
  classical
  have _hq1 : (0 : ℝ) < q := by linarith
  -- Step 1: translate the disc so that it is centred at the origin.
  have htrans : ∫⁻ w in Metric.ball z r, ‖w - z‖ₑ ^ (-q)
      = ∫⁻ v in Metric.ball (0:ℂ) r, ‖v‖ₑ ^ (-q) := by
    have hmem : ∀ w : ℂ, w - z ∈ Metric.ball (0:ℂ) r ↔ w ∈ Metric.ball z r := by
      intro w; simp [Metric.mem_ball, dist_eq_norm]
    have hind : (Metric.ball z r).indicator (fun w => ‖w - z‖ₑ ^ (-q))
        = fun w => ((Metric.ball (0:ℂ) r).indicator (fun v => ‖v‖ₑ ^ (-q))) (w - z) := by
      funext w
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hw : w ∈ Metric.ball z r
      · rw [ite_eq_left hw, ite_eq_left ((hmem w).mpr hw)]
      · rw [ite_eq_right hw, ite_eq_right (fun h => hw ((hmem w).mp h))]
    calc ∫⁻ w in Metric.ball z r, ‖w - z‖ₑ ^ (-q)
        = ∫⁻ w, (Metric.ball z r).indicator (fun w => ‖w - z‖ₑ ^ (-q)) w :=
          (lintegral_indicator Metric.isOpen_ball.measurableSet _).symm
      _ = ∫⁻ w, ((Metric.ball (0:ℂ) r).indicator (fun v => ‖v‖ₑ ^ (-q))) (w - z) := by rw [hind]
      _ = ∫⁻ w, (Metric.ball (0:ℂ) r).indicator (fun v => ‖v‖ₑ ^ (-q)) w :=
          lintegral_sub_right_eq_self _ z
      _ = ∫⁻ w in Metric.ball (0:ℂ) r, ‖w‖ₑ ^ (-q) :=
          lintegral_indicator Metric.isOpen_ball.measurableSet _
  rw [htrans]
  -- Step 2: change to polar coordinates (valid because the exceptional point `v = 0` has
  -- measure zero and the target of `polarCoord` avoids it).
  set f : ℂ → ℝ≥0∞ := (Metric.ball (0:ℂ) r).indicator (fun v => ‖v‖ₑ ^ (-q)) with hf
  have hpolar := Complex.lintegral_comp_polarCoord_symm f
  have hL : ∫⁻ v in Metric.ball (0:ℂ) r, ‖v‖ₑ ^ (-q) = ∫⁻ v, f v := by
    rw [hf]
    exact (lintegral_indicator Metric.isOpen_ball.measurableSet _).symm
  rw [hL, ← hpolar]
  have hTmeas : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  have hSmeas : MeasurableSet (Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hST : Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
    intro p hp
    rw [polarCoord_target, Set.mem_prod]
    rw [Set.mem_prod] at hp
    exact ⟨Set.Ioo_subset_Ioi_self hp.1, hp.2⟩
  -- The pulled-back integrand is `ρ^{1-q}` on the polar rectangle and `0` elsewhere.
  have hkey : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)
      = (Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun p : ℝ × ℝ => ENNReal.ofReal p.1 ^ (1 - q)) p := by
    intro p hp
    rw [polarCoord_target, Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : 0 < p.1 := hp1
    have hnorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
      rw [enorm_ofReal_norm, Complex.norm_polarCoord_symm, abs_of_pos hp1']
    have hsymm : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r ↔ p.1 < r := by
      rw [Metric.mem_ball, dist_zero_right,
        show ‖Complex.polarCoord.symm p‖ = p.1 by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1']]
    have hfval : f (Complex.polarCoord.symm p)
        = if p.1 < r then ENNReal.ofReal p.1 ^ (-q) else 0 := by
      rw [hf, Set.indicator_apply]
      by_cases hpr : p.1 < r
      · rw [ite_eq_left (hsymm.mpr hpr), ite_eq_left hpr, hnorm]
      · rw [ite_eq_right (fun h => hpr (hsymm.mp h)), ite_eq_right hpr]
    rw [smul_eq_mul, hfval]
    by_cases hpr : p.1 < r
    · rw [ite_eq_left hpr, Set.indicator_of_mem]
      · have hx0 : ENNReal.ofReal p.1 ≠ 0 := (ENNReal.ofReal_pos.mpr hp1').ne'
        have hxtop : ENNReal.ofReal p.1 ≠ ∞ := ENNReal.ofReal_ne_top
        have hrp := ENNReal.rpow_add (x := ENNReal.ofReal p.1) 1 (-q) hx0 hxtop
        rw [ENNReal.rpow_one, show (1:ℝ) + -q = 1 - q by ring] at hrp
        exact hrp.symm
      · rw [Set.mem_prod]; exact ⟨⟨hp1', hpr⟩, hp2⟩
    · rw [ite_eq_right hpr, mul_zero, Set.indicator_of_notMem]
      intro hpS
      rw [Set.mem_prod, Set.mem_Ioo] at hpS
      exact absurd hpS.1.2 hpr
  rw [setLIntegral_congr_fun hTmeas hkey]
  rw [setLIntegral_indicator (s := Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi) hSmeas]
  rw [Set.inter_eq_left.mpr hST]
  -- Step 3: Tonelli, then the one-dimensional radial integral.
  have hmeasF : Measurable fun p : ℝ × ℝ => (ENNReal.ofReal p.1) ^ (1 - q) :=
    ENNReal.continuous_rpow_const.measurable.comp (Measurable.ennreal_ofReal measurable_fst)
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => (ENNReal.ofReal p.1) ^ (1 - q))
      ((volume.prod volume).restrict (Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi)) :=
    hmeasF.aemeasurable.restrict
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hmeas]
  simp_rw [setLIntegral_const, Real.volume_Ioo, show Real.pi - -Real.pi = 2 * Real.pi by ring]
  rw [setLIntegral_mul_const' measurableSet_Ioo _ ENNReal.ofReal_ne_top]
  rw [lintegral_ofReal_rpow_Ioo (1 - q) r (by linarith) hr,
    show (1:ℝ) - q + 1 = 2 - q by ring]
  rw [← ENNReal.ofReal_mul
    (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hr (2 - q))) (by linarith))]
  congr 1
  field_simp

end Work.MRMT.Cauchy
