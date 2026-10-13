import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.EllipticEst.InteriorRegularity

/-- For a Haar measure `volume` on a finite-dimensional real inner product space `E`, the
difference map `(x, y) ↦ x - y` pulls back null sets to null sets for the product measure
`volume.prod volume`.  Concretely: if `N` is `volume`-null then
`{p : E × E | p.1 - p.2 ∈ N}` is null for `volume.prod volume`.

This is the measure-theoretic ingredient that turns a.e. equality of a function on `E` into
a.e. equality of its composition with `(x, y) ↦ x - y`, and hence is what makes the
"convolution" integrand a.e. measurable on the product. -/
private lemma prod_preimage_sub_null {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N : Set E} (hN : (volume : Measure E) N = 0) :
    ((volume : Measure E).prod (volume : Measure E)) {p : E × E | p.1 - p.2 ∈ N} = 0 := by
  -- Replace `N` by a *measurable* null superset, so that the relevant sets are measurable and
  -- Tonelli's theorem applies.
  obtain ⟨t, hNt, ht_meas, ht0⟩ := exists_measurable_superset_of_null hN
  have hQt : MeasurableSet {p : E × E | p.1 - p.2 ∈ t} :=
    ht_meas.preimage (measurable_fst.sub measurable_snd)
  -- Every `x`-section of `{p | p.1 - p.2 ∈ t}` is a translate of `t`, hence null.
  have hsec : ∀ y : E,
      (volume : Measure E) ((fun x : E => (x, y)) ⁻¹' {p : E × E | p.1 - p.2 ∈ t}) = 0 := by
    intro y
    have hset : (fun x : E => (x, y)) ⁻¹' {p : E × E | p.1 - p.2 ∈ t}
        = (fun h : E => h + (-y)) ⁻¹' t := by
      ext x; simp [sub_eq_add_neg]
    rw [hset, measure_preimage_add_right, ht0]
  have hQt0 : ((volume : Measure E).prod (volume : Measure E)) {p : E × E | p.1 - p.2 ∈ t} = 0 := by
    rw [Measure.prod_apply_symm hQt]
    simp only [hsec, lintegral_zero]
  exact measure_mono_null (fun p hp => hNt hp) hQt0

theorem lintegral_lintegral_conv_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFm : AEMeasurable F MeasureTheory.volume)
    (hum : AEMeasurable u MeasureTheory.volume) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
  -- A measurable representative of `F`; its null difference set propagates to the product.
  obtain ⟨F', hF'm, hFF'⟩ := hFm
  have hN0 : (volume : Measure E) {x : E | F x ≠ F' x} = 0 := MeasureTheory.ae_iff.mp hFF'
  have hpre : ((volume : Measure E).prod (volume : Measure E))
      {p : E × E | p.1 - p.2 ∈ {x : E | F x ≠ F' x}} = 0 := prod_preimage_sub_null hN0
  have hae : ∀ᵐ p ∂((volume : Measure E).prod (volume : Measure E)),
      F (p.1 - p.2) = F' (p.1 - p.2) := by
    rw [MeasureTheory.ae_iff]
    exact measure_mono_null (fun p hp => hp) hpre
  have hA : AEMeasurable (fun p : E × E => ENNReal.ofReal (F (p.1 - p.2)))
      ((volume : Measure E).prod (volume : Measure E)) := by
    refine ⟨fun p : E × E => ENNReal.ofReal (F' (p.1 - p.2)), ?_, ?_⟩
    · exact hF'm.ennreal_ofReal.comp (measurable_fst.sub measurable_snd)
    · filter_upwards [hae] with p hp
      exact congrArg ENNReal.ofReal hp
  have hB : AEMeasurable (fun p : E × E => ENNReal.ofReal (u p.2 ^ 2))
      ((volume : Measure E).prod (volume : Measure E)) :=
    ((hum.comp_snd (ν := (volume : Measure E))).pow_const 2).ennreal_ofReal
  -- A.e. measurability of the uncurried integrand, which is what Tonelli's theorem needs.
  have hAB : AEMeasurable (Function.uncurry fun x y : E =>
      ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
      ((volume : Measure E).prod (volume : Measure E)) := hA.mul hB
  calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) := by
        refine lintegral_congr fun x => lintegral_congr fun y => ?_
        exact ENNReal.ofReal_mul (hF (x - y))
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) := by
        exact lintegral_lintegral_swap hAB
    -- pull out the `y`-dependent factor from the inner integral (no measurability needed,
    -- since `ENNReal.ofReal _` is never `⊤`)
    _ = ∫⁻ y, (∫⁻ x, ENNReal.ofReal (F (x - y))) * ENNReal.ofReal (u y ^ 2) := by
        refine lintegral_congr fun y => ?_
        exact lintegral_mul_const' (ENNReal.ofReal (u y ^ 2))
          (fun x : E => ENNReal.ofReal (F (x - y))) ENNReal.ofReal_ne_top
    -- translation invariance of Haar measure
    _ = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) := by
        refine lintegral_congr fun y => ?_
        have hsub : (∫⁻ x, ENNReal.ofReal (F (x - y))) = ∫⁻ z, ENNReal.ofReal (F z) :=
          lintegral_sub_right_eq_self (fun z : E => ENNReal.ofReal (F z)) y
        rw [hsub]
    _ = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) :=
        lintegral_const_mul'' _ ((hum.pow_const 2).ennreal_ofReal)

end Work.EllipticEst.InteriorRegularity
