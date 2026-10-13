import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- `AEMeasurable` on a restricted measure upgrades to `AEMeasurable` of the indicator. -/
private lemma aemeasurable_indicator_of_restrict {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {f : α → ENNReal}
    (h : AEMeasurable f (μ.restrict s)) : AEMeasurable (s.indicator f) μ := by
  obtain ⟨g, hg, hfg⟩ := h
  exact ⟨s.indicator g, hg.indicator hs, (ae_eq_restrict_iff_indicator_ae_eq hs).mp hfg⟩

/-- Uncurried form of the region `a < t < z`: the `t`-indicator of `(a,z)` agrees with the
`(a,b)`-indicator times the step function `t ↦ 1_{t < z}`, provided `z ∈ (a,b)`. -/
private lemma tri_key_left {a b z : ℝ} (hz : z ∈ Set.Ioo a b) (G : ℝ → ENNReal) (t : ℝ) :
    (if t < z then (1 : ENNReal) else 0) * (Set.Ioo a b).indicator G t
      = (Set.Ioo a z).indicator G t := by
  by_cases h : t ∈ Set.Ioo a z
  · have hb : t ∈ Set.Ioo a b := ⟨h.1, lt_trans h.2 hz.2⟩
    rw [ite_eq_left h.2, one_mul, indicator_of_mem hb, indicator_of_mem h]
  · by_cases h2 : t < z
    · have hnb : t ∉ Set.Ioo a b := fun hb => h ⟨hb.1, h2⟩
      rw [ite_eq_left h2, one_mul, indicator_of_notMem hnb, indicator_of_notMem h]
    · rw [ite_eq_right h2, zero_mul, indicator_of_notMem h]

/-- The companion identity for the region `t < z < b`: the `z`-indicator of `(t,b)` agrees with
the `(a,b)`-indicator times the step function `z ↦ 1_{t < z}`, provided `t ∈ (a,b)`. -/
private lemma tri_key_right {a b t : ℝ} (ht : t ∈ Set.Ioo a b) (F : ℝ → ENNReal) (z : ℝ) :
    (Set.Ioo a b).indicator F z * (if t < z then (1 : ENNReal) else 0)
      = (Set.Ioo t b).indicator F z := by
  by_cases h : z ∈ Set.Ioo t b
  · have hb : z ∈ Set.Ioo a b := ⟨lt_trans ht.1 h.1, h.2⟩
    rw [indicator_of_mem hb, ite_eq_left h.1, mul_one, indicator_of_mem h]
  · by_cases h2 : t < z
    · have hnb : z ∉ Set.Ioo a b := fun hb => h ⟨h2, hb.2⟩
      rw [indicator_of_notMem hnb, ite_eq_left h2, mul_one, indicator_of_notMem h]
    · rw [ite_eq_right h2, mul_zero, indicator_of_notMem h]

/-- Tonelli/Fubini for the triangular region `a < t < z < b`: the iterated integral over
`z ∈ (a,b)`, `t ∈ (a,z)` equals the iterated integral over `t ∈ (a,b)`, `z ∈ (t,b)`.

Both sides compute the integral of `F z * G t` over the triangle in the two possible orders.
The proof encodes the triangle as the product-measure integral of
`Ψ z t = 1_{(a,b)}(z) · 1_{(a,b)}(t) · 1_{t<z}` (manifestly a.e. measurable on
`volume.prod volume`, being a product of `AEMeasurable` one-variable factors and a Borel step
function), swaps the iterated integrals with `lintegral_lintegral_swap`, and identifies each
iterated integral with the corresponding restricted integral using the two key identities
above. -/
theorem lintegral_Ioo_triangle {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ENNReal}
    (hF : AEMeasurable F (MeasureTheory.volume.restrict (Set.Ioo a b)))
    (hG : AEMeasurable G (MeasureTheory.volume.restrict (Set.Ioo a b))) :
    (∫⁻ z in Set.Ioo a b, F z * ∫⁻ t in Set.Ioo a z, G t)
      = ∫⁻ t in Set.Ioo a b, G t * ∫⁻ z in Set.Ioo t b, F z := by
  have hab0 : a ≤ b := hab
  have hs : MeasurableSet (Set.Ioo a b) := measurableSet_Ioo
  have hA : AEMeasurable (fun z : ℝ => (Set.Ioo a b).indicator F z) volume :=
    aemeasurable_indicator_of_restrict hs hF
  have hB : AEMeasurable (fun t : ℝ => (Set.Ioo a b).indicator G t) volume :=
    aemeasurable_indicator_of_restrict hs hG
  have hstep : ∀ z : ℝ, Measurable (fun t : ℝ => (if t < z then (1 : ENNReal) else 0)) :=
    fun z => Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hstep' : ∀ t : ℝ, Measurable (fun z : ℝ => (if t < z then (1 : ENNReal) else 0)) :=
    fun t => Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hstep2 : Measurable (fun p : ℝ × ℝ => (if p.2 < p.1 then (1 : ENNReal) else 0)) :=
    Measurable.ite (isOpen_lt continuous_snd continuous_fst).measurableSet measurable_const
      measurable_const
  have hA' : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioo a b).indicator F p.1)
      (volume.prod volume) := hA.comp_fst
  have hB' : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioo a b).indicator G p.2)
      (volume.prod volume) := hB.comp_snd
  set Ψ : ℝ → ℝ → ENNReal := fun z t =>
    (Set.Ioo a b).indicator F z
      * ((if t < z then (1 : ENNReal) else 0) * (Set.Ioo a b).indicator G t) with hΨ
  have hAE : AEMeasurable (Function.uncurry Ψ) (volume.prod volume) := by
    rw [hΨ]
    exact AEMeasurable.mul hA' (hstep2.aemeasurable.mul hB')
  have h1 : (∫⁻ z, ∫⁻ t, Ψ z t)
      = ∫⁻ z in Set.Ioo a b, F z * ∫⁻ t in Set.Ioo a z, G t := by
    have hpt : ∀ z : ℝ,
        ∫⁻ t, Ψ z t
          = (Set.Ioo a b).indicator (fun z => F z * ∫⁻ t in Set.Ioo a z, G t) z := by
      intro z
      by_cases hz : z ∈ Set.Ioo a b
      · have hinner : AEMeasurable
            (fun t : ℝ => (if t < z then (1 : ENNReal) else 0) * (Set.Ioo a b).indicator G t)
            volume := (hstep z).aemeasurable.mul hB
        calc ∫⁻ t, Ψ z t
            = (Set.Ioo a b).indicator F z *
                ∫⁻ t, (if t < z then (1 : ENNReal) else 0) * (Set.Ioo a b).indicator G t := by
                simp only [hΨ]
                exact lintegral_const_mul'' _ hinner
          _ = (Set.Ioo a b).indicator F z * ∫⁻ t, (Set.Ioo a z).indicator G t := by
                congr 1
                exact lintegral_congr (fun t => tri_key_left hz G t)
          _ = (Set.Ioo a b).indicator F z * ∫⁻ t in Set.Ioo a z, G t := by
                rw [lintegral_indicator measurableSet_Ioo G]
          _ = F z * ∫⁻ t in Set.Ioo a z, G t := by
                rw [indicator_of_mem hz F]
          _ = (Set.Ioo a b).indicator (fun z => F z * ∫⁻ t in Set.Ioo a z, G t) z := by
                rw [indicator_of_mem hz]
      · have hzF : (Set.Ioo a b).indicator F z = 0 := indicator_of_notMem hz F
        rw [indicator_of_notMem hz]
        simp only [hΨ, hzF, zero_mul, lintegral_zero]
    calc ∫⁻ z, ∫⁻ t, Ψ z t
        = ∫⁻ z, (Set.Ioo a b).indicator (fun z => F z * ∫⁻ t in Set.Ioo a z, G t) z :=
          lintegral_congr hpt
      _ = ∫⁻ z in Set.Ioo a b, F z * ∫⁻ t in Set.Ioo a z, G t := by
          rw [lintegral_indicator measurableSet_Ioo
            (fun z => F z * ∫⁻ t in Set.Ioo a z, G t)]
  have h2 : (∫⁻ t, ∫⁻ z, Ψ z t)
      = ∫⁻ t in Set.Ioo a b, G t * ∫⁻ z in Set.Ioo t b, F z := by
    have hpt : ∀ t : ℝ,
        ∫⁻ z, Ψ z t
          = (Set.Ioo a b).indicator (fun t => G t * ∫⁻ z in Set.Ioo t b, F z) t := by
      intro t
      by_cases ht : t ∈ Set.Ioo a b
      · have hinner : AEMeasurable
            (fun z : ℝ => (Set.Ioo a b).indicator F z * (if t < z then (1 : ENNReal) else 0))
            volume := hA.mul (hstep' t).aemeasurable
        calc ∫⁻ z, Ψ z t
            = ∫⁻ z, (Set.Ioo a b).indicator F z * (if t < z then (1 : ENNReal) else 0)
                * (Set.Ioo a b).indicator G t := by
                apply lintegral_congr
                intro z
                simp only [hΨ]
                exact (mul_assoc _ _ _).symm
          _ = (∫⁻ z, (Set.Ioo a b).indicator F z * (if t < z then (1 : ENNReal) else 0))
                * (Set.Ioo a b).indicator G t := by
                exact lintegral_mul_const'' _ hinner
          _ = (∫⁻ z, (Set.Ioo t b).indicator F z) * (Set.Ioo a b).indicator G t := by
                congr 1
                exact lintegral_congr (fun z => tri_key_right ht F z)
          _ = (∫⁻ z in Set.Ioo t b, F z) * G t := by
                rw [lintegral_indicator measurableSet_Ioo F, indicator_of_mem ht G]
          _ = G t * ∫⁻ z in Set.Ioo t b, F z := by
                rw [mul_comm]
          _ = (Set.Ioo a b).indicator (fun t => G t * ∫⁻ z in Set.Ioo t b, F z) t := by
                rw [indicator_of_mem ht]
      · have htG : (Set.Ioo a b).indicator G t = 0 := indicator_of_notMem ht G
        rw [indicator_of_notMem ht]
        simp only [hΨ, htG, mul_zero, lintegral_zero]
    calc ∫⁻ t, ∫⁻ z, Ψ z t
        = ∫⁻ t, (Set.Ioo a b).indicator (fun t => G t * ∫⁻ z in Set.Ioo t b, F z) t :=
          lintegral_congr hpt
      _ = ∫⁻ t in Set.Ioo a b, G t * ∫⁻ z in Set.Ioo t b, F z := by
          rw [lintegral_indicator measurableSet_Ioo
            (fun t => G t * ∫⁻ z in Set.Ioo t b, F z)]
  have hswap : (∫⁻ z, ∫⁻ t, Ψ z t) = ∫⁻ t, ∫⁻ z, Ψ z t :=
    lintegral_lintegral_swap (f := Ψ) hAE
  rw [← h1, hswap, h2]

end Work.FTS.PhiStar.Honesty
