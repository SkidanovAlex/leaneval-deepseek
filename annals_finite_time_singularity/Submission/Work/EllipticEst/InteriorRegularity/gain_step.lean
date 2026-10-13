/-
Interior regularity: the **gain step** for a second-order elliptic equation

`Δ u = G + b·∂_e u + b'·∂_{e'} u + c·u` with `G ∈ H^σ`, `u ∈ H^σ` and `b, b', c` compactly
supported `C^∞`, implies `u ∈ H^{σ+2}` (`H^s = TemperedDistribution.MemSobolev s 2`, the
Bessel-potential Sobolev space).

The proof is the classical two-round bootstrap, using that
* the directional derivative drops one order (`MemSobolev.lineDerivOp`, Mathlib),
* multiplication by a compactly supported `C^∞` function preserves `H^s`
  (`gainStep_smul_memSobolev` below, proved here from the Fourier-side estimate
  `gainStep_phiEstimate`),
* the Laplacian gains two orders (`gain_two`, `SobolevCalc.lean`).

Round 1: the right-hand side of the equation lies in `H^{σ-1}` (each `b·∂_e u` is in `H^{σ-1}`
since `∂_e u ∈ H^{σ-1}`), and `u ∈ H^{σ-1}`, so `gain_two` at `σ-1` gives `u ∈ H^{σ+1}`.
Round 2: now the right-hand side lies in `H^σ` (and `u ∈ H^σ`), so `gain_two` at `σ` gives the
claim.
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Submission.Work.EllipticEst.InteriorRegularity.SobolevCalc
import Submission.Work.EllipticEst.InteriorRegularity.MulSobolevDefs
import Submission.Work.EllipticEst.InteriorRegularity.mms_Phi_estimate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Filter LineDeriv ENNReal
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology LineDeriv

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Young's inequality in `eLpNorm` form

The form of Young's convolution inequality `L¹ ∗ L² → L²` needed for the Fourier-side estimate:
a function `f` that is pointwise dominated (in `enorm`) by the `ℝ≥0∞`-integral of
`F (x - y) * u y`, with `F ∈ L¹` nonnegative and `u ∈ L²` nonnegative, has
`eLpNorm f 2 ≤ (∫ F) · eLpNorm u 2`.

The proof is that of `young_l1_l2` (same directory) with the convolution replaced by an arbitrary
dominated function; it is the only ingredient of the Fourier estimate that is not covered by
`young_l1_l2`. -/

/-- Young's inequality in `eLpNorm` form, with a pointwise `enorm` domination hypothesis. -/
theorem gainStep_young_eLpNorm {F u : E → ℝ} {f : E → ℂ}
    (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : Integrable F (volume : Measure E)) (huM : MemLp u 2 (volume : Measure E))
    (hfm : AEStronglyMeasurable f (volume : Measure E))
    (hpt : ∀ x, ‖f x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) :
    eLpNorm f 2 (volume : Measure E)
      ≤ ENNReal.ofReal (∫ z, F z) * eLpNorm u 2 (volume : Measure E) := by
  have hFm : AEMeasurable F (volume : Measure E) := hFi.aemeasurable
  have hum : AEMeasurable u (volume : Measure E) := huM.aemeasurable
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  have hAlt : (∫⁻ z, ENNReal.ofReal (F z)) ≠ ∞ := by
    rw [← hAeq]; exact ENNReal.ofReal_ne_top
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
  -- the `L²` (squared) mass of `f`
  have hkey : (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
      ≤ (∫⁻ z, ENNReal.ofReal (F z))
        * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    calc (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
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
  have hfnorm : eLpNorm f (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hfm,
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
  rw [hfnorm, hAeq, hunorm]
  calc (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)
      ≤ ((∫⁻ z, ENNReal.ofReal (F z))
          * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2))) ^ ((1:ℝ)/2) :=
        ENNReal.rpow_le_rpow hkey (by norm_num)
    _ = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
        rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
          ← ENNReal.rpow_mul]
        norm_num

/-! ## The analytic estimate: `Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded on `L²`

This is the missing estimate in the classical proof that multiplication by a compactly supported
smooth function preserves `H^s = MemSobolev s 2` (Mathlib has no product machinery for Sobolev
spaces). -/

/-- **The key estimate.**  The Schwartz-level operator `Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded for the
`L²` norm, with the constant `∫ ξ, ‖2^{|s|/2} ⟨ξ⟩^{|s|} 𝓕γ(ξ)‖`. -/
theorem gainStep_phiEstimate (s : ℝ) (γS k : 𝓢(E, ℂ)) :
    ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      ≤ (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * (𝓕 γS) ξ)‖) *
          ‖k.toLp 2 (volume : Measure E)‖ := by
  have hFnn : ∀ z : E, 0 ≤ ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖ := fun _ => norm_nonneg _
  have hun : ∀ y : E, 0 ≤ ‖FourierTransform.fourier k y‖ := fun _ => norm_nonneg _
  have hFi : Integrable (fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖) (volume : Measure E) := by
    have hSint : Integrable (fun z : E =>
        ‖⇑(SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) |s|)
          (FourierTransform.fourier γS : 𝓢(E, ℂ))) z‖) (volume : Measure E) :=
      (SchwartzMap.integrable _).norm
    refine (hSint.mul_const (2 ^ (|s| / 2))).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (E := E) |s|), smul_eq_mul,
      norm_mul, norm_mul, norm_mul, norm_ofReal_complex,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) (|s| / 2))]
    ring
  have huM : MemLp (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier k) 2 (volume : Measure E)).norm
  have hfm : AEStronglyMeasurable
      (⇑(FourierTransform.fourier (mms_Phi s γS k))) (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier (mms_Phi s γS k)) 2
      (volume : Measure E)).aestronglyMeasurable
  have hpt : ∀ ξ : E, ‖(⇑(FourierTransform.fourier (mms_Phi s γS k))) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal ((‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
          (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier γS (ξ - y))‖) *
          ‖FourierTransform.fourier k y‖) ∂(volume : Measure E) :=
    fun ξ => mms_Phi_enorm_le s γS k ξ
  have hmain := gainStep_young_eLpNorm
    (F := fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖)
    (u := fun y : E => ‖FourierTransform.fourier k y‖)
    (f := ⇑(FourierTransform.fourier (mms_Phi s γS k))) hFnn hun hFi huM hfm hpt
  have hPhi : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal := by
    have h1 : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier (mms_Phi s γS k)).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq ((mms_Phi s γS k).toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hk : ‖k.toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
    have h1 : ‖k.toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier k).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq (k.toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hnormu : eLpNorm (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E)
      = eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) :=
    eLpNorm_norm _ (SchwartzMap.memLp (FourierTransform.fourier k) 2
      (volume : Measure E)).aestronglyMeasurable
  have hne : ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
        (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
        * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (SchwartzMap.memLp
      (FourierTransform.fourier k) 2 (volume : Measure E)).eLpNorm_lt_top)
  rw [hPhi, hk]
  calc (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal
      ≤ (ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_mono hne (by rw [← hnormu]; exact hmain)
    _ = (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

/-! ## Extension from Schwartz functions to `L²`

If `Λ^s u = U ∈ L²` then `Λ^s(γu) ∈ L²`, i.e. `γu ∈ H^s`: approximate `U` in `L²` by Schwartz
functions; the images under `Λ^s ∘ M_γ ∘ Λ^{-s}` form a Cauchy sequence in `L²` by the estimate,
and the limit agrees with `Λ^s(γu)` because that operator is continuous on `𝓢'`.
-/

theorem gainStep_main {s : ℝ} (γS : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) (U : Lp ℂ 2 (volume : Measure E))
    (hU : besselPotential E ℂ s u = (U : 𝓢'(E, ℂ))) :
    MemSobolev s 2 (smulLeftCLM ℂ (⇑γS) u) := by
  set C : ℝ := ∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| ξ * (𝓕 γS) ξ)‖ with hCdef
  have hC_nonneg : 0 ≤ C := by
    rw [hCdef]
    exact integral_nonneg fun ξ => norm_nonneg _
  have hu_eq : u = besselPotential E ℂ (-s) (U : 𝓢'(E, ℂ)) := by
    rw [← mms_bessel_neg_bessel s u, hU]
  -- the embedding of Schwartz functions into `L²`
  let e : 𝓢(E, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure E) := SchwartzMap.toLpCLM ℂ ℂ 2 volume
  have hdense : DenseRange e := by
    show DenseRange fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)
    have h := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := E) (p := 2)
      (μ := (volume : Measure E)) (by norm_num)
    have hfe : (fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)) =
        ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) := by
      funext f
      rw [SchwartzMap.toLpCLM_apply]
    rw [hfe]
    exact h
  have hseq : ∀ n : ℕ, ∃ k : 𝓢(E, ℂ), dist U (e k) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (Metric.denseRange_iff.mp hdense) U _ (by positivity)
  choose f hf using hseq
  have hnorm : ∀ n : ℕ, ‖U - e (f n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h := hf n
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have hzero : Tendsto (fun n : ℕ => U - e (f n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hh := Nat.add_le_add_right hn 1
      exact_mod_cast hh
    have h2 : 1 / ((N : ℝ) + 1) < ε := by
      have h3 : (1 : ℝ) < ((N : ℝ) + 1) * ε := by
        have hN' : (1 : ℝ) / ε < (N : ℝ) + 1 := by
          have : (N : ℝ) < (N : ℝ) + 1 := by linarith
          linarith
        exact (div_lt_iff₀ hε).mp hN'
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith [h3]
    calc dist (U - e (f n)) 0 = ‖U - e (f n)‖ := by rw [dist_zero_right]
      _ ≤ 1 / ((n : ℝ) + 1) := hnorm n
      _ ≤ 1 / ((N : ℝ) + 1) := h1
      _ < ε := h2
  have hftend : Tendsto (fun n : ℕ => e (f n)) atTop (𝓝 U) := by
    have h1 : Tendsto (fun n : ℕ => U - (U - e (f n))) atTop (𝓝 (U - 0)) := hzero.const_sub U
    simpa using h1
  -- the images in `L²`
  let v : ℕ → Lp ℂ 2 (volume : Measure E) := fun n => (mms_Phi s γS (f n)).toLp 2 volume
  have hv_lip : ∀ m n : ℕ, dist (v m) (v n) ≤ C * dist (e (f m)) (e (f n)) := by
    intro m n
    have hL : mms_Phi s γS (f m) - mms_Phi s γS (f n) = mms_Phi s γS (f m - f n) := by
      simp only [mms_Phi, map_sub]
    have hA' : v m - v n = (mms_Phi s γS (f m - f n)).toLp 2 (volume : Measure E) := by
      rw [show v m = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f m))
            from rfl,
        show v n = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f n))
            from rfl,
        ← map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)), hL]
      rfl
    have hB' : e (f m) - e (f n) = (f m - f n).toLp 2 (volume : Measure E) := by
      show e (f m) - e (f n) = _
      rw [← map_sub e]
      rfl
    rw [dist_eq_norm, dist_eq_norm, hA', hB', hCdef]
    exact gainStep_phiEstimate s γS (f m - f n)
  have hv_cauchy : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hce : CauchySeq fun n : ℕ => e (f n) := hftend.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hce) (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hC1 : 0 < C + 1 := by linarith
    have h1 := hv_lip m n
    have h2 := hN m hm n hn
    have h3 : C * dist (e (f m)) (e (f n)) ≤ (C + 1) * dist (e (f m)) (e (f n)) := by
      have hd : 0 ≤ dist (e (f m)) (e (f n)) := dist_nonneg
      nlinarith
    have h4 : (C + 1) * dist (e (f m)) (e (f n)) < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left h2 hC1
    have h5 : (C + 1) * (ε / (C + 1)) = ε := by
      field_simp
    linarith [h1, h3, h4, h5.le, h5.ge]
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hv_cauchy
  -- the limiting distribution: apply the (continuous) operator to the `L²` limit
  let A : Lp ℂ 2 (volume : Measure E) →L[ℂ] 𝓢'(E, ℂ) :=
    (besselPotential E ℂ s).comp ((smulLeftCLM ℂ (⇑γS)).comp
      ((besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2)))
  have hAapply : ∀ W : Lp ℂ 2 (volume : Measure E), A W = besselPotential E ℂ s
      (smulLeftCLM ℂ (⇑γS) (besselPotential E ℂ (-s) (W : 𝓢'(E, ℂ)))) := by
    intro W
    rfl
  have hA : ∀ n : ℕ, A (e (f n)) = (v n : 𝓢'(E, ℂ)) := by
    intro n
    rw [hAapply]
    have h1 : ((e (f n) : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) = (f n : 𝓢'(E, ℂ)) :=
      Lp.toTemperedDistribution_toLp_eq (f n)
    rw [h1, ← mms_Phi_toTempered s γS (f n)]
    exact (Lp.toTemperedDistribution_toLp_eq (mms_Phi s γS (f n))).symm
  have hAU : A U = besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u) := by
    rw [hAapply, ← hU, mms_bessel_neg_bessel]
  have h1 : Tendsto (fun n : ℕ => (v n : 𝓢'(E, ℂ))) atTop
      (𝓝 (besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u))) := by
    have hcomp : Tendsto (fun n : ℕ => A (e (f n))) atTop (𝓝 (A U)) :=
      (A.continuous.tendsto U).comp hftend
    rw [← hAU]
    simpa only [hA] using hcomp
  have h2 : Tendsto (fun n : ℕ => (v n : 𝓢'(E, ℂ))) atTop (𝓝 (V : 𝓢'(E, ℂ))) :=
    ((Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2).continuous.tendsto V).comp hV
  exact ⟨V, tendsto_nhds_unique h1 h2⟩

/-! ## Multiplication preserves `H^s` -/

/-- Multiplication by a compactly supported `C^∞` function preserves every Bessel potential
space `H^s = MemSobolev s 2`, `s ∈ ℝ`. -/
theorem gainStep_smul_memSobolev {s : ℝ} {γ : E → ℂ} (hγc : HasCompactSupport γ)
    (hγs : ∀ n : ℕ, ContDiff ℝ n γ) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    MemSobolev s 2 (smulLeftCLM ℂ γ u) := by
  have hγS_smooth : ContDiff ℝ (⊤ : ℕ∞) γ := contDiff_infty.mpr hγs
  let γS : 𝓢(E, ℂ) := hγc.toSchwartzMap hγS_smooth
  obtain ⟨U, hU⟩ := hu
  exact gainStep_main γS u U hU

/-! ## The gain step -/

theorem gain_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {σ : ℝ} {u G : 𝓢'(E, ℂ)} {b b' c : E → ℂ} (e e' : E)
    (hb : HasCompactSupport b) (hbs : ∀ n : ℕ, ContDiff ℝ n b)
    (hb' : HasCompactSupport b') (hb's : ∀ n : ℕ, ContDiff ℝ n b')
    (hc : HasCompactSupport c) (hcs : ∀ n : ℕ, ContDiff ℝ n c)
    (hG : TemperedDistribution.MemSobolev σ 2 G)
    (hu : TemperedDistribution.MemSobolev σ 2 u)
    (heq : Laplacian.laplacian u
      = G + TemperedDistribution.smulLeftCLM ℂ b (LineDeriv.lineDerivOp e u)
        + TemperedDistribution.smulLeftCLM ℂ b' (LineDeriv.lineDerivOp e' u)
        + TemperedDistribution.smulLeftCLM ℂ c u) :
    TemperedDistribution.MemSobolev (σ+2) 2 u := by
  -- ## Round 1: the right-hand side lies in `H^{σ-1}`
  have hde : MemSobolev (σ - 1) 2 (LineDeriv.lineDerivOp e u) :=
    MemSobolev.lineDerivOp (m := e) hu
  have hde' : MemSobolev (σ - 1) 2 (LineDeriv.lineDerivOp e' u) :=
    MemSobolev.lineDerivOp (m := e') hu
  have hb1 : MemSobolev (σ - 1) 2 (smulLeftCLM ℂ b (LineDeriv.lineDerivOp e u)) :=
    gainStep_smul_memSobolev hb hbs hde
  have hb1' : MemSobolev (σ - 1) 2 (smulLeftCLM ℂ b' (LineDeriv.lineDerivOp e' u)) :=
    gainStep_smul_memSobolev hb' hb's hde'
  have hu1 : MemSobolev (σ - 1) 2 u := hu.mono (by linarith)
  have hc1 : MemSobolev (σ - 1) 2 (smulLeftCLM ℂ c u) := gainStep_smul_memSobolev hc hcs hu1
  have hG1 : MemSobolev (σ - 1) 2 G := hG.mono (by linarith)
  have hΔ1 : MemSobolev (σ - 1) 2 (Laplacian.laplacian u) := by
    rw [heq]
    exact ((hG1.add hb1).add hb1').add hc1
  have hu2 : MemSobolev (σ + 1) 2 u :=
    (gain_two (σ - 1) u hu1 hΔ1).mono (by linarith)
  -- ## Round 2: the right-hand side lies in `H^σ`
  have hde2 : MemSobolev σ 2 (LineDeriv.lineDerivOp e u) :=
    (MemSobolev.lineDerivOp (m := e) hu2).mono (by linarith)
  have hde2' : MemSobolev σ 2 (LineDeriv.lineDerivOp e' u) :=
    (MemSobolev.lineDerivOp (m := e') hu2).mono (by linarith)
  have hb2 : MemSobolev σ 2 (smulLeftCLM ℂ b (LineDeriv.lineDerivOp e u)) :=
    gainStep_smul_memSobolev hb hbs hde2
  have hb2' : MemSobolev σ 2 (smulLeftCLM ℂ b' (LineDeriv.lineDerivOp e' u)) :=
    gainStep_smul_memSobolev hb' hb's hde2'
  have hc2 : MemSobolev σ 2 (smulLeftCLM ℂ c u) := gainStep_smul_memSobolev hc hcs hu
  have hΔ2 : MemSobolev σ 2 (Laplacian.laplacian u) := by
    rw [heq]
    exact ((hG.add hb2).add hb2').add hc2
  exact gain_two σ u hu hΔ2

end Work.EllipticEst.InteriorRegularity
