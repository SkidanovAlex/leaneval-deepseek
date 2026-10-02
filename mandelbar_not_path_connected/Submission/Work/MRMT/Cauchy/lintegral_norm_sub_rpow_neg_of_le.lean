import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Set ENNReal
open scoped ENNReal Topology

/-- The improper integral `∫_t^∞ r ^ a dr = -t ^ (a+1) / (a+1)` for `a < -1` and `t > 0`,
expressed as an `ℝ≥0∞`-valued Lebesgue integral. -/
private lemma lintegral_ofReal_rpow_Ioi (t : ℝ) (ht : 0 < t) {a : ℝ} (ha : a < -1) :
    ∫⁻ r in Set.Ioi t, ENNReal.ofReal (r ^ a) = ENNReal.ofReal (-t ^ (a + 1) / (a + 1)) := by
  have hint : IntegrableOn (fun r : ℝ => r ^ a) (Set.Ioi t) := integrableOn_Ioi_rpow_of_lt ha ht
  have hFint : Integrable ((Set.Ioi t).indicator (fun r : ℝ => r ^ a)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr hint
  have hnonneg : 0 ≤ᵐ[volume] ((Set.Ioi t).indicator (fun r : ℝ => r ^ a)) := by
    filter_upwards with r
    by_cases hr : r ∈ Set.Ioi t
    · rw [Set.indicator_of_mem hr]
      exact Real.rpow_nonneg (le_of_lt (ht.trans hr)) a
    · rw [Set.indicator_of_notMem hr]
      exact le_rfl
  have key := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFint hnonneg
  have h1 : ∫⁻ r in Set.Ioi t, ENNReal.ofReal (r ^ a)
      = ∫⁻ r, ENNReal.ofReal (((Set.Ioi t).indicator (fun r : ℝ => r ^ a)) r) := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi (fun r : ℝ => ENNReal.ofReal (r ^ a))]
    apply MeasureTheory.lintegral_congr
    intro r
    by_cases hr : r ∈ Set.Ioi t
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, ENNReal.ofReal_zero]
  rw [h1, ← key]
  congr 1
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  exact integral_Ioi_rpow_of_lt ha ht

/-- Pulling a constant factor out of an `ℝ≥0∞`-valued set integral. -/
private lemma setLIntegral_mul_const {α : Type*} [MeasureSpace α]
    {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞) :
    ∫⁻ x in s, f x * c = (∫⁻ x in s, f x) * c := by
  calc ∫⁻ x in s, f x * c = ∫⁻ x, s.indicator (fun x => f x * c) x :=
        (MeasureTheory.lintegral_indicator hs (fun x => f x * c)).symm
    _ = ∫⁻ x, s.indicator f x * c := by
        apply MeasureTheory.lintegral_congr
        intro x
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    _ = (∫⁻ x, s.indicator f x) * c := MeasureTheory.lintegral_mul_const c (hf.indicator hs)
    _ = (∫⁻ x in s, f x) * c := by rw [MeasureTheory.lintegral_indicator hs f]

/-- **Radial integral over the complement of a disc in `ℂ`.**
For `a < -2` and `t > 0`,
`∫_{‖v‖ ≥ t} ‖v‖ ^ a dv = 2π · t ^ (a+2) / (-(a+2))`. -/
private lemma lintegral_radial_Ioi (t : ℝ) (ht : 0 < t) {a : ℝ} (ha : a < -2) :
    ∫⁻ v in {v : ℂ | t ≤ ‖v‖}, ENNReal.ofReal (‖v‖ ^ a) =
      ENNReal.ofReal (2 * Real.pi * t ^ (a + 2) / (-(a + 2))) := by
  set U : Set (ℝ × ℝ) := Set.Ici t ×ˢ Set.Ioo (-Real.pi) Real.pi with hUdef
  set g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (1 + a)) with hg
  have hS : MeasurableSet {v : ℂ | t ≤ ‖v‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hU : MeasurableSet U := by
    rw [hUdef]; exact measurableSet_Ici.prod measurableSet_Ioo
  have hpT : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  have hmeasg : Measurable g := by
    rw [hg]
    exact ENNReal.measurable_ofReal.comp
      (Measurable.pow (measurable_fst : Measurable (fun p : ℝ × ℝ => p.1)) measurable_const)
  have hf1 : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ (1 + a))) :=
    ENNReal.measurable_ofReal.comp
      (Measurable.pow (measurable_id : Measurable (fun r : ℝ => r)) measurable_const)
  -- Step 1: polar coordinates
  have hmain : ∫⁻ v in {v : ℂ | t ≤ ‖v‖}, ENNReal.ofReal (‖v‖ ^ a)
      = ∫⁻ p in polarCoord.target, U.indicator g p := by
    rw [← MeasureTheory.lintegral_indicator hS]
    rw [← Complex.lintegral_comp_polarCoord_symm
      (({v : ℂ | t ≤ ‖v‖}.indicator (fun v => ENNReal.ofReal (‖v‖ ^ a))))]
    apply MeasureTheory.setLIntegral_congr_fun hpT
    intro p hp
    beta_reduce
    rw [polarCoord_target] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hpt : t ≤ p.1
    · have hmem : Complex.polarCoord.symm p ∈ {v : ℂ | t ≤ ‖v‖} := by
        simp only [Set.mem_setOf_eq, hnorm]
        exact hpt
      rw [Set.indicator_of_mem hmem]
      rw [Set.indicator_of_mem (show p ∈ U by rw [hUdef]; exact ⟨hpt, hp2⟩)]
      change ENNReal.ofReal p.1 • ENNReal.ofReal (‖Complex.polarCoord.symm p‖ ^ a)
        = ENNReal.ofReal (p.1 ^ (1 + a))
      rw [smul_eq_mul, hnorm, ← ENNReal.ofReal_mul (le_of_lt hp1)]
      congr 1
      rw [Real.rpow_add hp1 1 a, Real.rpow_one]
    · have hmem : Complex.polarCoord.symm p ∉ {v : ℂ | t ≤ ‖v‖} := by
        simp only [Set.mem_setOf_eq, hnorm, not_le]
        exact lt_of_not_ge hpt
      rw [Set.indicator_of_notMem hmem]
      rw [Set.indicator_of_notMem (show p ∉ U by rw [hUdef]; exact fun h => hpt h.1)]
      rw [smul_zero]
  -- Step 2: the polar integrand only depends on the radius
  have hstep4 : ∫⁻ p in polarCoord.target, U.indicator g p = ∫⁻ p in U, g p := by
    rw [← MeasureTheory.lintegral_indicator hpT (U.indicator g),
        ← MeasureTheory.lintegral_indicator hU g]
    apply MeasureTheory.lintegral_congr
    intro p
    by_cases hp : p ∈ polarCoord.target
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem]
      intro hU'
      rw [hUdef] at hU'
      exact hp (by rw [polarCoord_target]; exact ⟨lt_of_lt_of_le ht hU'.1, hU'.2⟩)
  have hstep5 : ∫⁻ p in U, g p
      = (∫⁻ r in Set.Ici t, ENNReal.ofReal (r ^ (1 + a))) * ENNReal.ofReal (2 * Real.pi) := by
    rw [hUdef, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
    rw [MeasureTheory.setLIntegral_prod g hmeasg.aemeasurable]
    have hinner : ∀ r : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (r, θ)
        = ENNReal.ofReal (r ^ (1 + a)) * ENNReal.ofReal (2 * Real.pi) := by
      intro r
      simp only [hg]
      rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo,
          show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
    simp_rw [hinner]
    rw [setLIntegral_mul_const measurableSet_Ici
      (fun r : ℝ => ENNReal.ofReal (r ^ (1 + a))) hf1 (ENNReal.ofReal (2 * Real.pi))]
  have hstep6 : ∫⁻ r in Set.Ici t, ENNReal.ofReal (r ^ (1 + a))
      = ENNReal.ofReal (-t ^ (a + 2) / (a + 2)) := by
    rw [MeasureTheory.setLIntegral_congr
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := t)).symm]
    have h := lintegral_ofReal_rpow_Ioi t ht (a := 1 + a) (by linarith)
    rw [show (1 : ℝ) + a + 1 = a + 2 by ring] at h
    exact h
  have hnn : 0 ≤ -t ^ (a + 2) / (a + 2) := by
    rw [neg_div, ← div_neg]
    exact div_nonneg (le_of_lt (Real.rpow_pos_of_pos ht _)) (by linarith)
  calc ∫⁻ v in {v : ℂ | t ≤ ‖v‖}, ENNReal.ofReal (‖v‖ ^ a)
      = ∫⁻ p in polarCoord.target, U.indicator g p := hmain
    _ = ∫⁻ p in U, g p := hstep4
    _ = (∫⁻ r in Set.Ici t, ENNReal.ofReal (r ^ (1 + a))) * ENNReal.ofReal (2 * Real.pi) := hstep5
    _ = ENNReal.ofReal (-t ^ (a + 2) / (a + 2)) * ENNReal.ofReal (2 * Real.pi) := by rw [hstep6]
    _ = ENNReal.ofReal ((-t ^ (a + 2) / (a + 2)) * (2 * Real.pi)) := by
          rw [← ENNReal.ofReal_mul hnn]
    _ = ENNReal.ofReal (2 * Real.pi * t ^ (a + 2) / (-(a + 2))) := by
          congr 1
          rw [neg_div, ← div_neg]
          ring

theorem lintegral_norm_sub_rpow_neg_of_le (z : ℂ) {q t : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (ht : 0 < t) :
    (∫⁻ w in {w : ℂ | t ≤ ‖w - z‖}, ‖w - z‖ₑ ^ (-(2 * q))) =
      ENNReal.ofReal (2 * Real.pi * t ^ (2 - 2 * q) / (2 * q - 2)) := by
  have ha : -(2 * q) < -2 := by linarith
  have hS : MeasurableSet {v : ℂ | t ≤ ‖v‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hSz : MeasurableSet {w : ℂ | t ≤ ‖w - z‖} :=
    (isClosed_le continuous_const
      (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet
  have htrans : ∫⁻ w in {w : ℂ | t ≤ ‖w - z‖}, ‖w - z‖ₑ ^ (-(2 * q))
      = ∫⁻ v in {v : ℂ | t ≤ ‖v‖}, ‖v‖ₑ ^ (-(2 * q)) := by
    rw [← MeasureTheory.lintegral_indicator hSz]
    rw [← MeasureTheory.lintegral_add_right_eq_self
      (fun w : ℂ => ({w : ℂ | t ≤ ‖w - z‖}.indicator (fun w => ‖w - z‖ₑ ^ (-(2 * q))) w)) z]
    rw [← MeasureTheory.lintegral_indicator hS]
    apply MeasureTheory.lintegral_congr
    intro w
    have hmem : (w + z) ∈ {w : ℂ | t ≤ ‖w - z‖} ↔ t ≤ ‖w‖ := by
      show t ≤ ‖(w + z) - z‖ ↔ t ≤ ‖w‖
      rw [add_sub_cancel_right]
    by_cases hw : t ≤ ‖w‖
    · rw [Set.indicator_of_mem (show (w + z) ∈ {w : ℂ | t ≤ ‖w - z‖} from hmem.mpr hw),
          Set.indicator_of_mem (s := {v : ℂ | t ≤ ‖v‖}) hw, add_sub_cancel_right]
    · rw [Set.indicator_of_notMem (s := {w : ℂ | t ≤ ‖w - z‖}) (fun h => hw (hmem.mp h)),
          Set.indicator_of_notMem (s := {v : ℂ | t ≤ ‖v‖}) hw]
  have hconv : ∫⁻ v in {v : ℂ | t ≤ ‖v‖}, ‖v‖ₑ ^ (-(2 * q))
      = ∫⁻ v in {v : ℂ | t ≤ ‖v‖}, ENNReal.ofReal (‖v‖ ^ (-(2 * q))) := by
    apply MeasureTheory.setLIntegral_congr_fun hS
    intro v hv
    have hvpos : 0 < ‖v‖ := lt_of_lt_of_le ht hv
    show ‖v‖ₑ ^ (-(2 * q)) = ENNReal.ofReal (‖v‖ ^ (-(2 * q)))
    rw [show ‖v‖ₑ = ENNReal.ofReal ‖v‖ by simp only [ofReal_norm],
        ENNReal.ofReal_rpow_of_pos hvpos]
  rw [htrans, hconv]
  have hmain := lintegral_radial_Ioi t ht (a := -(2 * q)) ha
  rw [hmain]
  rw [show -(-(2 * q) + 2) = 2 * q - 2 by ring,
      show -(2 * q) + 2 = 2 - 2 * q by ring]

end Work.MRMT.Cauchy
