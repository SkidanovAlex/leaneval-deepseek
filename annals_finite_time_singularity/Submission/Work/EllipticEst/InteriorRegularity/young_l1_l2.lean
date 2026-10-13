import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity

open MeasureTheory ENNReal

/-- Young's convolution inequality in the case `L¹ * L² → L²`:
the convolution `x ↦ ∫ y, F (x - y) * u y` of an integrable nonnegative `F` with an
`L²` (nonnegative) `u` is square integrable, with
`‖F * u‖₂ ≤ ‖F‖₁ ‖u‖₂`.

Proof: for each `x` the completion-of-squares/weighted Cauchy–Schwarz inequality
`(∫ y, F(x-y) u(y))² ≤ (∫ y, F(x-y)) (∫ y, F(x-y) u(y)²)` (obtained from Hölder with
exponents `2,2` against the weight `√(F(x-y))`), followed by Tonelli and translation
invariance of `volume`:
`∫ x, ∫ y, F(x-y) u(y)² = (∫ z, F z) (∫ y, u(y)²)`. -/
theorem young_l1_l2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : MeasureTheory.Integrable F MeasureTheory.volume)
    (huM : MeasureTheory.MemLp u 2 MeasureTheory.volume) :
    MeasureTheory.MemLp (fun x => ∫ y, F (x - y) * u y) 2 MeasureTheory.volume ∧
    MeasureTheory.eLpNorm (fun x => ∫ y, F (x - y) * u y) 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (∫ z, F z) * MeasureTheory.eLpNorm u 2 MeasureTheory.volume := by
  set G : E → ℝ := fun x => ∫ y, F (x - y) * u y with hGdef
  have hFm : AEMeasurable F (volume : Measure E) := hFi.aemeasurable
  have hum : AEMeasurable u (volume : Measure E) := huM.aemeasurable
  -- `∫⁻` of `ofReal F` is `ofReal` of the integral
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  have hAlt : (∫⁻ z, ENNReal.ofReal (F z)) ≠ ∞ := by
    rw [← hAeq]; exact ENNReal.ofReal_ne_top
  -- `G` is the convolution `F * u`, hence a.e. strongly measurable
  have hGconv : G = MeasureTheory.convolution F u (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure E) := by
    rw [hGdef]
    funext x
    rw [convolution_lsmul_swap]
    simp only [smul_eq_mul]
  have hG_aesm : AEStronglyMeasurable G (volume : Measure E) := by
    rw [hGconv]
    exact hFi.aestronglyMeasurable.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      huM.aestronglyMeasurable
  -- pointwise bound of `‖G x‖ₑ` by the lintegral of the (nonnegative) integrand
  have hpt : ∀ x : E, ‖G x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (F (x - y) * u y) := by
    intro x
    rw [hGdef]
    have h1 := enorm_integral_le_lintegral_enorm (μ := (volume : Measure E))
      (fun y : E => F (x - y) * u y)
    have h2 : ∀ y : E, ‖F (x - y) * u y‖ₑ = ENNReal.ofReal (F (x - y) * u y) := by
      intro y
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg (hF _) (hu _))]
    simpa only [h2] using h1
  -- Cauchy–Schwarz in `y` with weight `√(F (x - y))`, for each `x`
  have hcs : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (F (x - y)))
        * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
    intro x
    have hFmeas : AEMeasurable (fun y : E => F (x - y)) (volume : Measure E) :=
      hFm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    set phi : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.sqrt (F (x - y))) with hphidef
    set psi : E → ℝ≥0∞ := fun y => phi y * ENNReal.ofReal (u y) with hsidef
    have hphim : AEMeasurable phi (volume : Measure E) := by
      rw [hphidef]
      exact ((ENNReal.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp_aemeasurable
        hFmeas)
    have humeas : AEMeasurable (fun y : E => ENNReal.ofReal (u y)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hum
    have hpsim : AEMeasurable psi (volume : Measure E) := by
      rw [hsidef]; exact hphim.mul humeas
    have hphiphi : ∀ y, phi y * phi y = ENNReal.ofReal (F (x - y)) := by
      intro y
      rw [hphidef]; simp only
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hF _)]
    have hpsipsi : ∀ y, psi y * psi y = ENNReal.ofReal (F (x - y) * u y ^ 2) := by
      intro y
      have h1 : psi y = phi y * ENNReal.ofReal (u y) := rfl
      calc psi y * psi y
          = (phi y * phi y) * (ENNReal.ofReal (u y) * ENNReal.ofReal (u y)) := by
            rw [h1]; ring
        _ = ENNReal.ofReal (F (x - y)) * (ENNReal.ofReal (u y) * ENNReal.ofReal (u y)) := by
            rw [hphiphi y]
        _ = ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) := by
            rw [← pow_two, ← ENNReal.ofReal_pow (hu y) 2]
        _ = ENNReal.ofReal (F (x - y) * u y ^ 2) := by rw [← ENNReal.ofReal_mul (hF _)]
    have hphis : ∀ y, phi y * psi y = ENNReal.ofReal (F (x - y) * u y) := by
      intro y
      have h1 : psi y = phi y * ENNReal.ofReal (u y) := rfl
      calc phi y * psi y = (phi y * phi y) * ENNReal.ofReal (u y) := by rw [h1]; ring
        _ = ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y) := by rw [hphiphi y]
        _ = ENNReal.ofReal (F (x - y) * u y) := by rw [← ENNReal.ofReal_mul (hF _)]
    have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure E) (p := 2) (q := 2)
      (⟨by norm_num, by norm_num, by norm_num⟩ : (2:ℝ).HolderConjugate 2) hphim hpsim
    have hH : (∫⁻ y, ENNReal.ofReal (F (x - y) * u y))
        ≤ (∫⁻ y, ENNReal.ofReal (F (x - y))) ^ ((1:ℝ)/2)
          * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) ^ ((1:ℝ)/2) := by
      have h1 : (∫⁻ y, phi y * psi y) = ∫⁻ y, ENNReal.ofReal (F (x - y) * u y) :=
        lintegral_congr (fun y => hphis y)
      have h2 : (∫⁻ y, phi y ^ (2:ℝ)) = ∫⁻ y, ENNReal.ofReal (F (x - y)) :=
        lintegral_congr (fun y => by rw [ENNReal.rpow_two, pow_two, hphiphi y])
      have h3 : (∫⁻ y, psi y ^ (2:ℝ)) = ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
        lintegral_congr (fun y => by rw [ENNReal.rpow_two, pow_two, hpsipsi y])
      rw [show (∫⁻ a : E, (phi * psi) a) = ∫⁻ y, phi y * psi y from rfl, h1, h2, h3] at hHold
      exact hHold
    have hH2 := ENNReal.rpow_le_rpow hH (by norm_num : (0:ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at hH2
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hH2
    norm_num at hH2
    simpa using hH2
  -- translation invariance in `x`
  have htrans : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y))) = ∫⁻ z, ENNReal.ofReal (F z) := by
    intro x
    exact lintegral_sub_left_eq_self (μ := (volume : Measure E))
      (fun z : E => ENNReal.ofReal (F z)) x
  -- Tonelli + translation invariance, computing the double integral of the `u ^ 2`-term
  have hK : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    have hFm' : AEMeasurable (fun z : E => ENNReal.ofReal (F z)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hFm
    have hMm : AEMeasurable (fun y : E => ENNReal.ofReal (u y ^ 2)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hum.pow_const 2)
    have h1 : AEMeasurable (fun w : E × E => ENNReal.ofReal (F w.1))
        ((volume : Measure E).prod volume) := hFm'.comp_fst
    have h2 : AEMeasurable (fun w : E × E => ENNReal.ofReal (u w.2 ^ 2))
        ((volume : Measure E).prod volume) := hMm.comp_snd
    have h3 : AEMeasurable
        (fun w : E × E => ENNReal.ofReal (F w.1) * ENNReal.ofReal (u w.2 ^ 2))
        ((volume : Measure E).prod volume) := h1.mul h2
    -- the shear `(x,y) ↦ (x-y,y)` is measure preserving, which gives the joint measurability
    have hS : Measure.QuasiMeasurePreserving (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
      (measurePreserving_sub_prod (volume : Measure E) volume).quasiMeasurePreserving
    have hjoint : AEMeasurable
        (fun p : E × E => ENNReal.ofReal (F (p.1 - p.2)) * ENNReal.ofReal (u p.2 ^ 2))
        ((volume : Measure E).prod volume) := by
      have hcomp : (fun p : E × E =>
            ENNReal.ofReal (F (p.1 - p.2)) * ENNReal.ofReal (u p.2 ^ 2))
          = (fun w : E × E => ENNReal.ofReal (F w.1) * ENNReal.ofReal (u w.2 ^ 2))
            ∘ (fun z : E × E => (z.1 - z.2, z.2)) := by
        funext p; simp
      rw [hcomp]; exact h3.comp_quasiMeasurePreserving hS
    rw [show (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) from
          lintegral_congr (fun x => lintegral_congr (fun y => ENNReal.ofReal_mul (hF _)))]
    have hjoint' : AEMeasurable (Function.uncurry fun x y : E =>
        ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        ((volume : Measure E).prod volume) := hjoint
    rw [lintegral_lintegral_swap (μ := (volume : Measure E)) (ν := (volume : Measure E))
      (f := fun x y : E => ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2)) hjoint']
    have hinner : ∀ y : E, (∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        = (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) := by
      intro y
      calc (∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
          = ∫⁻ x, (fun z => ENNReal.ofReal (F z) * ENNReal.ofReal (u y ^ 2)) (x - y) := rfl
        _ = ∫⁻ x, ENNReal.ofReal (F x) * ENNReal.ofReal (u y ^ 2) :=
              lintegral_sub_right_eq_self (μ := (volume : Measure E))
                (fun z : E => ENNReal.ofReal (F z) * ENNReal.ofReal (u y ^ 2)) y
        _ = (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) :=
              lintegral_mul_const'' _ hFm'
    rw [show (∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) from
          lintegral_congr hinner]
    exact lintegral_const_mul'' _ hMm
  -- the bound on the `L²` (squared) mass of `G`
  have hkey1 : (∫⁻ x, ‖G x‖ₑ ^ (2:ℝ))
      ≤ (∫⁻ z, ENNReal.ofReal (F z))
        * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    calc (∫⁻ x, ‖G x‖ₑ ^ (2:ℝ))
        ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ) :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num))
      _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y)))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) :=
          lintegral_mono (fun x => hcs x)
      _ = ∫⁻ x, (∫⁻ z, ENNReal.ofReal (F z))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
          refine lintegral_congr (fun x => ?_)
          rw [htrans x]
      _ = (∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
          lintegral_const_mul' _ _ hAlt
      _ = (∫⁻ z, ENNReal.ofReal (F z))
            * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
          rw [hK]
  have hGnorm : eLpNorm G (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ x, ‖G x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hG_aesm,
      eLpNorm'_eq_lintegral_enorm]
    norm_num
  have hunorm : eLpNorm u (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
        huM.aestronglyMeasurable,
      eLpNorm'_eq_lintegral_enorm]
    norm_num
    congr 1
    refine lintegral_congr (fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu y)]
    exact (ENNReal.ofReal_pow (hu y) 2).symm
  have hfinal : eLpNorm G (2:ℝ≥0∞) (volume : Measure E)
      ≤ ENNReal.ofReal (∫ z, F z) * eLpNorm u (2:ℝ≥0∞) (volume : Measure E) := by
    rw [hGnorm, hunorm, hAeq]
    calc (∫⁻ x, ‖G x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)
        ≤ ((∫⁻ z, ENNReal.ofReal (F z))
            * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2))) ^ ((1:ℝ)/2) :=
          ENNReal.rpow_le_rpow hkey1 (by norm_num)
      _ = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
          rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
            ← ENNReal.rpow_mul]
          norm_num
  refine ⟨?_, ?_⟩
  · rw [memLp_iff]
    exact lt_of_le_of_lt hfinal (ENNReal.mul_lt_top ENNReal.ofReal_lt_top huM.eLpNorm_lt_top)
  · exact hfinal

end Work.EllipticEst.InteriorRegularity
