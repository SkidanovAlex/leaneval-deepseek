import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseFixB1.BoxTauGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.D1InputsB1` — two (of the three) inputs of the localised D1 chain

The localised D1 pairing payment (`Work.BoseFixB1S.boxSimpleA2TwoWindowSharp`) is assembled in
`Work.BoseFixB1S.chainCore` (`chain_localised`, `sharp_of_chain`: both PROVED) from three inputs:

* the **window-mass bound** `winMode_mass_le` (`hXq`) — PROVED here;
* the **`𝓑²`-Plancherel bound** `integral_pairW_sq_le` (the credit bound `hcredit`) — PROVED here;
* the **frame bound** (`hframe`) — `Work.BoseFixB1.boxFramePGen` (PROVED, in the corpus).

This module holds the two rungs proved here so that the D1 assembly can import them without
importing the (still open) target module.

* `winMode_mass_le`: `∫_A (boxWinModeReGen …)² + ∫_A (boxWinModeImGen …)² ≤ ∫ χ²`
  (the mean-free part is the `L²`-projection off the constants; `cos² + sin² = 1`).
* `integral_pairW_sq_le`: `(2π)⁻³∫_q (pairW W q)² ≤ ∫_x (W x)²` for `W ∈ L²`
  (Plancherel for `W ∈ L¹`, junk-`0` for `W ∉ L¹`).
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The window-mass bound of the localised D1 chain

FS's windowed `q`-mode mass `∫_{B}(1_B χ e^{i⟪q,·⟫} − its box mean)²` is at most
`∫ χ²`: the mean-free part is the `L²`-orthogonal projection off the constants, hence a
contraction. -/

/-- **The window-mass bound** (`Work.BoseFixB1S.winMode_mass_le`, proved here): for a
box-supported `χ`,

`∫_A (boxWinModeReGen …)² + ∫_A (boxWinModeImGen …)² ≤ ∫ χ²` .

This is the `hXq` input of `Work.BoseFixB1S.chain_localised`: it is the *variance* bound
`∫_A (f − ⦵_A f)² ≤ ∫_A f²` applied to `f = χ cos⟪q,·⟫` and `f = χ sin⟪q,·⟫`, summed with
`cos² + sin² = 1`. -/
theorem winMode_mass_le {volA : ℝ} {Ac : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet Ac) (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
        + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2)
      ≤ ∫ z, (χ z) ^ 2 := by
  classical
  -- the box is finite (from `0 < volA = (volume Ac).toReal`)
  have hfin : (MeasureTheory.volume Ac) ≠ ⊤ := by
    intro h
    rw [h] at hvol
    simp at hvol
    linarith [hvolpos]
  -- the two windowed profiles and their box means
  set f : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => χ z * Real.cos (inner ℝ q z) with hfdef
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => χ z * Real.sin (inner ℝ q z) with hgdef
  set mf : ℝ := volA⁻¹ * ∫ z in Ac, f z with hmfdef
  set mg : ℝ := volA⁻¹ * ∫ z in Ac, g z with hmgdef
  have hfcont : Continuous f :=
    hχc.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  have hgcont : Continuous g :=
    hχc.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))
  have hfsupp : HasCompactSupport f :=
    hχs.mul_right (f' := fun z => Real.cos (inner ℝ q z))
  have hgsupp : HasCompactSupport g :=
    hχs.mul_right (f' := fun z => Real.sin (inner ℝ q z))
  have hffeq : f * f = fun z => (f z) ^ 2 := funext fun z => by simp [Pi.mul_apply, pow_two]
  have hggeq : g * g = fun z => (g z) ^ 2 := funext fun z => by simp [Pi.mul_apply, pow_two]
  have hf2supp : HasCompactSupport (fun z => (f z) ^ 2) := by
    rw [← hffeq]; exact hfsupp.mul_right (f' := f)
  have hg2supp : HasCompactSupport (fun z => (g z) ^ 2) := by
    rw [← hggeq]; exact hgsupp.mul_right (f' := g)
  have hfint : IntegrableOn f Ac :=
    (hfcont.integrable_of_hasCompactSupport hfsupp).integrableOn
  have hgint : IntegrableOn g Ac :=
    (hgcont.integrable_of_hasCompactSupport hgsupp).integrableOn
  have hf2int : IntegrableOn (fun z => (f z) ^ 2) Ac :=
    ((hfcont.pow 2).integrable_of_hasCompactSupport hf2supp).integrableOn
  have hg2int : IntegrableOn (fun z => (g z) ^ 2) Ac :=
    ((hgcont.pow 2).integrable_of_hasCompactSupport hg2supp).integrableOn
  have hffint : IntegrableOn (fun z => (2 * mf) * f z) Ac := hfint.const_mul _
  have hggint : IntegrableOn (fun z => (2 * mg) * g z) Ac := hgint.const_mul _
  have hcintf : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => mf ^ 2) Ac :=
    integrableOn_const hfin
  have hcintg : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => mg ^ 2) Ac :=
    integrableOn_const hfin
  -- the box mean identity: `mf * volA = ∫_A f`
  have hmeanf : mf * volA = ∫ z in Ac, f z := by
    rw [hmfdef]
    field_simp
  have hmeang : mg * volA = ∫ z in Ac, g z := by
    rw [hmgdef]
    field_simp
  have hvol1 : (∫ _z in Ac, (1 : ℝ)) = volA := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, ← hvol, smul_eq_mul, mul_one]
  -- the variance bound for one windowed profile
  have hvar : ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ) (m : ℝ), IntegrableOn u Ac →
      IntegrableOn (fun z => (u z) ^ 2) Ac → m * volA = ∫ z in Ac, u z →
      (∫ z in Ac, (u z - m) ^ 2) ≤ ∫ z in Ac, (u z) ^ 2 := by
    intro u m hint hu2 hm
    have hmu : IntegrableOn (fun z => (2 * m) * u z) Ac := hint.const_mul _
    have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => m ^ 2) Ac :=
      integrableOn_const hfin
    have hExp : (fun z => (u z - m) ^ 2)
        = (fun z => ((u z) ^ 2 - (2 * m) * u z) + m ^ 2) := by
      funext z; ring
    have h2 : (∫ z in Ac, ((u z) ^ 2 - (2 * m) * u z))
        = (∫ z in Ac, (u z) ^ 2) - 2 * m * (∫ z in Ac, u z) := by
      rw [integral_sub hu2 hmu, integral_const_mul]
    have h3 : (∫ _z in Ac, m ^ 2) = volA * m ^ 2 := by
      rw [setIntegral_const, MeasureTheory.Measure.real_def, ← hvol, smul_eq_mul]
    calc (∫ z in Ac, (u z - m) ^ 2)
        = (∫ z in Ac, ((u z) ^ 2 - (2 * m) * u z)) + ∫ _z in Ac, m ^ 2 := by
          rw [hExp]
          exact integral_add (hu2.sub hmu) hc
      _ = ((∫ z in Ac, (u z) ^ 2) - 2 * m * (∫ z in Ac, u z)) + volA * m ^ 2 := by
          rw [h2, h3]
      _ = ((∫ z in Ac, (u z) ^ 2) - 2 * m * (m * volA)) + volA * m ^ 2 := by rw [hm]
      _ ≤ ∫ z in Ac, (u z) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg m) hvolpos.le]
  -- the two unfolded window words
  have hRef : ∀ z, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
      = (Ac.indicator (fun _ => (1 : ℝ)) z) * (f z - mf) := by
    intro z
    simp only [Work.BoseFixB1.boxWinModeReGen, hfdef, hmfdef]
  have hImf : ∀ z, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
      = -((Ac.indicator (fun _ => (1 : ℝ)) z) * (g z - mg)) := by
    intro z
    simp only [Work.BoseFixB1.boxWinModeImGen, hgdef, hmgdef]
  have hRe : (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
      = ∫ z in Ac, (f z - mf) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
    rw [hRef z, Set.indicator_of_mem hz, one_mul]
  have hIm : (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2)
      = ∫ z in Ac, (g z - mg) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
    rw [hImf z, Set.indicator_of_mem hz, one_mul]
    ring
  -- the `cos² + sin²` collapse on the box
  have hsum : (∫ z in Ac, (f z) ^ 2) + (∫ z in Ac, (g z) ^ 2) = ∫ z in Ac, (χ z) ^ 2 := by
    rw [← integral_add hf2int hg2int]
    apply integral_congr_ae
    filter_upwards with z
    simp only [hfdef, hgdef]
    nlinarith [Real.cos_sq_add_sin_sq (inner ℝ q z)]
  -- `χ = 1_A χ`, so the box integral is the full integral
  have hchi : (∫ z, (χ z) ^ 2) = ∫ z in Ac, (χ z) ^ 2 := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Ac
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hχsupp z hz]; ring
  calc (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
        + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2)
      = (∫ z in Ac, (f z - mf) ^ 2) + (∫ z in Ac, (g z - mg) ^ 2) := by rw [hRe, hIm]
    _ ≤ (∫ z in Ac, (f z) ^ 2) + (∫ z in Ac, (g z) ^ 2) :=
        add_le_add (hvar f mf hfint hf2int hmeanf) (hvar g mg hgint hg2int hmeang)
    _ = ∫ z in Ac, (χ z) ^ 2 := hsum
    _ = ∫ z, (χ z) ^ 2 := hchi.symm


/-! ## 2. The `𝓑²`-Plancherel bound of the localised D1 chain

`Work.BoseFixB1S.integral_pairW_sq_le` (proved here): the `L²`-norm of the D1 pairing weight
`𝓑(q) = Re 𝓕W((2π)⁻¹q)` is at most the `L²`-norm of `W`.  This is the Plancherel input of the
D1 chain's credit bound (`chainCore.sharp_of_chain`'s `hcredit`).

The proof splits on `W ∈ L¹`:

* `W ∈ L¹ ∩ L²`: Plancherel (`Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2`), the
  measure-scaling identity `∫ q, g((2π)⁻¹q) = (2π)³∫ g` and the pointwise `(Re z)² ≤ ‖z‖²`;
* `W ∉ L¹`: `𝓕` is the *junk* (`0`) Bochner integral
  (`VectorFourier.fourierIntegral_convergent_iff` + `integral_undef`), so the left side is `0`.
-/

/-- **The `𝓑²`-Plancherel bound.** -/
theorem integral_pairW_sq_le {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.MemLp W 2) :
    (2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.pairW W q) ^ 2
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), (W x) ^ 2 := by
  classical
  set Fc : EuclideanSpace ℝ (Fin 3) → ℂ :=
    FourierTransform.fourier (fun x => (W x : ℂ)) with hFc
  have hpair : ∀ q : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.pairW W q = (Fc (((2 * Real.pi)⁻¹) • q)).re := by
    intro q
    simp only [Submission.BoseGases.pairW, hFc]
  have hpt : ∀ z : ℂ, z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hWsq : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (W x) ^ 2) :=
    hW.integrable_sq
  by_cases hInt : MeasureTheory.Integrable W
  · have h1 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) :=
      hInt.ofReal
    have h2 : MeasureTheory.MemLp (fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) 2 :=
      hW.ofReal
    have hFc_cont : Continuous Fc := by
      rw [hFc]
      exact VectorFourier.fourierIntegral_continuous (μ := MeasureTheory.volume)
        Real.continuous_fourierChar (innerSL ℝ).continuous₂ h1
    have hpl := Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
      (f := fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) h1 h2
    have hplF : (∫ ξ : EuclideanSpace ℝ (Fin 3), ‖Fc ξ‖ ^ 2)
        = ∫ x : EuclideanSpace ℝ (Fin 3), (W x) ^ 2 := by
      rw [show (fun ξ => ‖Fc ξ‖ ^ 2) = (fun ξ => ‖FourierTransform.fourier
          (fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) ξ‖ ^ 2) from by
        simp only [hFc]]
      rw [hpl]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    -- the measure-scaling identity
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hscale : (∫ q : EuclideanSpace ℝ (Fin 3), (Fc (((2 * Real.pi)⁻¹) • q)).re ^ 2)
        = (2 * Real.pi) ^ 3 * ∫ ξ : EuclideanSpace ℝ (Fin 3), (Fc ξ).re ^ 2 := by
      have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
        (fun q : EuclideanSpace ℝ (Fin 3) => (Fc q).re ^ 2)
        (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      simpa only [smul_eq_mul, hfin] using h
    -- the comparison `∫ (Re z)² ≤ ∫ ‖z‖²`
    have hcmp : (∫ ξ : EuclideanSpace ℝ (Fin 3), (Fc ξ).re ^ 2)
        ≤ ∫ ξ : EuclideanSpace ℝ (Fin 3), ‖Fc ξ‖ ^ 2 := by
      have hA : (∫ ξ : EuclideanSpace ℝ (Fin 3), (Fc ξ).re ^ 2)
          = (∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal ((Fc ξ).re ^ 2)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
          ((Complex.continuous_re.comp hFc_cont).aestronglyMeasurable.pow 2)
      have hB : (∫ ξ : EuclideanSpace ℝ (Fin 3), ‖Fc ξ‖ ^ 2)
          = (∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (‖Fc ξ‖ ^ 2)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
          (hFc_cont.norm.aestronglyMeasurable.pow 2)
      rw [hA, hB]
      have hmono : (∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal ((Fc ξ).re ^ 2))
          ≤ (∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (‖Fc ξ‖ ^ 2)) :=
        MeasureTheory.lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpt (Fc ξ))
      by_cases htop : (∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (‖Fc ξ‖ ^ 2)) = ⊤
      · have hFc0 : Fc = 0 := by
          have hc0 : (∫ x : EuclideanSpace ℝ (Fin 3), (W x) ^ 2) = 0 := by
            rw [← hplF, hB, htop, ENNReal.toReal_top]
          have hae0 : (fun x : EuclideanSpace ℝ (Fin 3) => (W x) ^ 2) =ᵐ[MeasureTheory.volume] 0 :=
            (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hWsq).mp hc0
          have hae : W =ᵐ[MeasureTheory.volume] 0 := by
            filter_upwards [hae0] with x hx
            simpa using (sq_eq_zero_iff.mp hx)
          funext ξ
          rw [hFc, Real.fourier_eq]
          exact MeasureTheory.integral_eq_zero_of_ae (by
            filter_upwards [hae] with v hv
            simp [hv])
        have ha : (∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal ((Fc ξ).re ^ 2)) = 0 := by
          rw [hFc0]; simp
        rw [ha, htop, ENNReal.toReal_top]
        simp
      · exact ENNReal.toReal_mono htop hmono
    calc (2 * Real.pi) ^ (-(3 : ℤ))
          * ∫ q : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.pairW W q) ^ 2
        = (2 * Real.pi) ^ (-(3 : ℤ))
          * ∫ q : EuclideanSpace ℝ (Fin 3), (Fc (((2 * Real.pi)⁻¹) • q)).re ^ 2 := by
          simp only [hpair]
      _ = (2 * Real.pi) ^ (-(3 : ℤ))
          * ((2 * Real.pi) ^ 3 * ∫ ξ : EuclideanSpace ℝ (Fin 3), (Fc ξ).re ^ 2) := by
          rw [hscale]
      _ = ∫ ξ : EuclideanSpace ℝ (Fin 3), (Fc ξ).re ^ 2 := by
          have hz : (2 * Real.pi : ℝ) ^ (-(3 : ℤ)) * (2 * Real.pi) ^ 3 = 1 := by
            rw [zpow_neg]
            exact inv_mul_cancel₀ (pow_ne_zero 3 (show (2 * Real.pi : ℝ) ≠ 0 by positivity))
          rw [← mul_assoc, hz, one_mul]
      _ ≤ ∫ ξ : EuclideanSpace ℝ (Fin 3), ‖Fc ξ‖ ^ 2 := hcmp
      _ = ∫ x : EuclideanSpace ℝ (Fin 3), (W x) ^ 2 := hplF
  · -- `W ∉ L¹`: the pointwise Fourier transform is the junk (`0`) Bochner integral
    have hzero : ∀ q : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.pairW W q = 0 := by
      intro q
      have hnc : ¬ MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) := by
        intro hc
        exact hInt (by simpa using hc.re)
      have hconv : ¬ MeasureTheory.Integrable
          (fun v : EuclideanSpace ℝ (Fin 3) =>
            Real.fourierChar (-(inner ℝ v (((2 * Real.pi)⁻¹) • q))) • ((W v : ℂ))) :=
        fun hc => hnc ((Real.fourierIntegral_convergent_iff (μ := MeasureTheory.volume)
          (f := fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) (((2 * Real.pi)⁻¹) • q)).mp hc)
      rw [Submission.BoseGases.pairW, Real.fourier_eq]
      rw [MeasureTheory.integral_undef hconv, Complex.zero_re]
    have hz : (∫ q : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.pairW W q) ^ 2) = 0 := by
      simp [hzero]
    rw [hz, mul_zero]
    exact integral_nonneg fun x => sq_nonneg _


end

end Work.BoseFixB1S
