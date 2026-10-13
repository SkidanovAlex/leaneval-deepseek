import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch._scratch.AeSigmaCleanCopy
import Submission.Work.FTS.EllipticEst.Dispatch.aeTruncSigmaIdD
import Submission.Work.FTS.EllipticEst.Mine.zcutFam
import Submission.Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.Prop.Ang2.Sig2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.H2W.Ae

namespace Work.FTS.EllipticEst.Dispatch.SigmaRad

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "σw" => Work.FTS.EllipticEst.sEta

/-!
# The `σ`-weighted radial energy inequality of Step 1 of `prop:H2`

`α² HkSq α 0 (z∂_zu) ≤ C (HkSq α 0 G + HkSq α 0 u)` for data in the almost-everywhere class
`Work.FTS.EllipticEst.H2W.Ae.AeData`, together with the honesty of `z∂_zu`.

The proof is the main body of `Work.FTS.EllipticEst.H2W.Ae.aeSigmaEnergyH2`
(`H2W/AeStepOneAux/aeSigmaEnergyClean.lean`), with two substitutions:

* the truncated `σ`-energy identity `Work.FTS.EllipticEst.H2W.Ae.aeTruncSigmaIdAe` (currently a
  `sorry`) is replaced by the proved `Work.FTS.EllipticEst.Dispatch.aeTruncSigmaIdD` (the
  `G`-form of the proved `Dispatch.truncRadialIbpTheta`);
* the cutoff family `Work.FTS.EllipticEst.H2W.Ae.aeSigmaCutoffSeq` (currently a `sorry`) is
  replaced by the proved `Work.FTS.EllipticEst.Mine.zcutFam` together with the weighted
  derivative bounds `Honest.omegaW_deriv_bounds` + `AeStepOneAux.chi_second_le`.
-/

theorem aeSigmaEnergyD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨K, hKpos, hKslice⟩ := aeSigmaSliceLower
  -- the cutoff family with the weighted derivative bounds
  obtain ⟨χ, C₁, C₂, hC₁pos, hC₂pos, hχsm, hχ01, hχleft, hχmid, hχright, hχd1, hχd2, hχlim⟩ :=
    Work.FTS.EllipticEst.Mine.zcutFam
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hchi2 : ∀ n z, |z ^ 2 * deriv (deriv (χ n)) z| ≤ C₂ + C₁ := fun n z =>
    Work.FTS.EllipticEst.AeStepOneAux.Sig2.chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n) z
  have hC₂nn : 0 ≤ C₂ + C₁ := by linarith
  have hχabs : ∀ n z, |χ n z| ≤ 1 := fun n z => by
    rw [abs_of_nonneg (hχ01 n z).1]; exact (hχ01 n z).2
  have hχdiff : ∀ n, ContDiff ℝ 2 (χ n) := fun n => hχsm n 2
  have hχsupp : ∀ (n : ℕ) (z : ℝ),
      z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) → χ n z = 0 := by
    intro n z hz
    rcases lt_or_ge z (1 / ((n : ℝ) + 1)) with h | h
    · exact hχleft n z (le_of_lt h)
    · have h2 : 2 * ((n : ℝ) + 1) < z := by
        rcases lt_or_ge (2 * ((n : ℝ) + 1)) z with h2 | h2
        · exact h2
        · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hz
      exact hχright n z (le_of_lt h2)
  set C0 : ℝ := max (3 + C₁) (6 + 4 * C₁ + (C₂ + C₁)) with hC0def
  have hC0pos : 0 < C0 := by
    rw [hC0def]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hmm1 : ∀ n, ∀ z, 0 < z → |deriv (fun y : ℝ => y * (Work.Spaces.w y ^ 2 * χ n y)) z|
      ≤ (3 + C₁) * (Work.Spaces.w z) ^ 2 := fun n =>
    (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n) (hchi2 n)
      (hχabs n) hC₁nn hC₂nn).1
  have hmm2 : ∀ n, ∀ z, 0 < z →
      |deriv (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x ^ 2 * χ n x)) y) z|
      ≤ (6 + 4 * C₁ + (C₂ + C₁)) * (Work.Spaces.w z) ^ 2 := fun n =>
    (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n) (hchi2 n)
      (hχabs n) hC₁nn hC₂nn).2
  have hχbd2 : ∀ n z, 0 < z → |deriv (fun z' : ℝ => χ n z' * phiW z' * z') z| ≤ C0 * phiW z := by
    intro n z hz
    have h := hmm1 n z hz
    have hfun : (fun y : ℝ => y * (Work.Spaces.w y ^ 2 * χ n y))
        = fun y : ℝ => χ n y * phiW y * y := by
      funext y; simp only [phiW]; ring
    rw [hfun] at h
    calc |deriv (fun z' : ℝ => χ n z' * phiW z' * z') z|
        ≤ (3 + C₁) * phiW z := h
      _ ≤ C0 * phiW z := by
          refine mul_le_mul_of_nonneg_right ?_ (by simp only [phiW]; positivity)
          rw [hC0def]; exact le_max_left _ _
  have hχbd1 : ∀ n z, 0 < z →
      |deriv (deriv (fun z' : ℝ => χ n z' * phiW z' * z' ^ 2)) z| ≤ C0 * phiW z := by
    intro n z hz
    have h := hmm2 n z hz
    have hfe : (fun x : ℝ => x ^ 2 * (Work.Spaces.w x ^ 2 * χ n x))
        = fun x : ℝ => χ n x * phiW x * x ^ 2 := by
      funext x; simp only [phiW]; ring
    have hfun : (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x ^ 2 * χ n x)) y)
        = fun y : ℝ => deriv (fun x : ℝ => χ n x * phiW x * x ^ 2) y := by
      rw [hfe]
    rw [hfun] at h
    calc |deriv (deriv (fun z' : ℝ => χ n z' * phiW z' * z' ^ 2)) z|
        ≤ (6 + 4 * C₁ + (C₂ + C₁)) * phiW z := h
      _ ≤ C0 * phiW z := by
          refine mul_le_mul_of_nonneg_right ?_ (by simp only [phiW]; positivity)
          rw [hC0def]; exact le_max_right _ _
  refine ⟨3 + K + 2 * C0, by positivity, ?_⟩
  intro α u G hA
  refine ⟨l2mem_grad_profile hA, ?_⟩
  have hα0 : (0 : ℝ) ≤ α := le_of_lt (AeData.hα hA)
  have hα4 : α ≤ 1 / 4 := AeData.hα4 hA
  have hmemU : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hmemX : Work.Spaces.HkMem α 0 (grad u) := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hmemG : Work.Spaces.HkMem α 0 G := AeData.memG hA
  have hmemR : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    AeData.memRad2 hA
  have hUslice : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2 * σw θ) Work.Spaces.Iθ :=
    (integrableOn_of_HkMem_zero hmemU).1
  have hGslice : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * σw θ) Work.Spaces.Iθ :=
    (integrableOn_of_HkMem_zero hmemG).1
  have hUint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
    weighted_slice_integrable hmemU
  have hGint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
    weighted_slice_integrable hmemG
  have hXint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
      Work.Spaces.Iz := weighted_slice_integrable hmemX
  have hRint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * σw θ))
      Work.Spaces.Iz := weighted_slice_integrable hmemR
  -- the slice mass and the two scalars
  set U : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ with hUdef
  set UU : ℝ := ∫ z in Work.Spaces.Iz, phiW z * U z with hUUdef
  set GG : ℝ := ∫ z in Work.Spaces.Iz,
    phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) with hGGdef
  have hUnn : ∀ z, 0 ≤ U z := fun z => by rw [hUdef]; exact uMass_nonneg u z
  have hUint' : MeasureTheory.IntegrableOn (fun z => phiW z * U z) Work.Spaces.Iz := by
    simpa only [hUdef] using hUint
  have hUUnn : 0 ≤ UU := by
    rw [hUUdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with z
    exact mul_nonneg (phiW_nonneg z) (hUnn z)
  have hGGnn : 0 ≤ GG := by
    rw [hGGdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with z
    exact mul_nonneg (phiW_nonneg z) (uMass_nonneg G z)
  -- the a.e. slice lower bound, transferred to `Iz`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      -(K * U z) ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero u z θ * u z θ * σw θ := by
    have h0 := hKslice α u G hA
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    filter_upwards [h0] with z hz
    have hL1 : Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ)
        = fun θ => Work.Elliptic.Lzero u z θ := by
      funext θ
      simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero,
        Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hL1] at hz
    have hUz : U z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ := rfl
    rw [hUz]
    simpa using hz
  -- ## (1) the source pairing
  have hB1 : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, χ n z * phiW z *
      (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)) ≤ (1 / 2) * (GG + UU) := by
    intro n
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |χ n z * phiW z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)|
          ≤ (1 / 2) * (phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)
              + phiW z * U z) := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      have hτ := theta_pairing_le (f := fun θ => G z θ) (g := fun θ => u z θ)
        (hGslice z hz) (hUslice z hz)
      have hφ : 0 ≤ phiW z := phiW_nonneg z
      have hχ0 : 0 ≤ χ n z := (hχ01 n z).1
      have hχ1 : χ n z ≤ 1 := (hχ01 n z).2
      rw [abs_mul, abs_mul, abs_of_nonneg hφ, abs_of_nonneg hχ0]
      have hUeq : U z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ := by rw [hUdef]
      rw [hUeq]
      calc χ n z * phiW z * |∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ|
          ≤ (1 * phiW z) * ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)
              + (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ))) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hχ1 hφ) hτ
              (abs_nonneg _) (mul_nonneg zero_le_one hφ)
        _ = (1 / 2) * (phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)
              + phiW z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) := by ring
    have hmono : (∫ z in Work.Spaces.Iz, |χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)|)
        ≤ ∫ z in Work.Spaces.Iz, (1 / 2) * (phiW z *
            (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) := by
      have hsum : MeasureTheory.IntegrableOn (fun z => phiW z *
          (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) Work.Spaces.Iz :=
        hGint.add hUint'
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => abs_nonneg _) (hsum.const_mul (1 / 2)) hpt
    have hval : (∫ z in Work.Spaces.Iz, (1 / 2) * (phiW z *
          (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z))
        = (1 / 2) * (GG + UU) := by
      rw [zIntegral_const_mul (1 / 2), MeasureTheory.integral_add hGint hUint',
        hGGdef, hUUdef]
    have h1 : (∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ))
        ≤ |∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)| := le_abs_self _
    have h2 : |∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)|
        ≤ ∫ z in Work.Spaces.Iz, |χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm (fun z => χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ))
    linarith [h1, h2, hmono, hval]
  -- ## (2) the angular self-form term
  have hB2 : ∀ n : ℕ, -(∫ z in Work.Spaces.Iz, χ n z * phiW z *
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ * σw θ)) ≤ K * UU := by
    intro n
    set σterm : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Lzero u z θ * u z θ * σw θ with hσterm
    by_cases hint : MeasureTheory.Integrable (fun z => χ n z * phiW z * σterm z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
    · have hneg : MeasureTheory.Integrable
          (fun z => -(χ n z * phiW z * σterm z))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := hint.neg
      have hKint : MeasureTheory.Integrable
          (fun z => χ n z * phiW z * (K * U z))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        have haesm : MeasureTheory.AEStronglyMeasurable
            (fun z => χ n z * phiW z * (K * U z))
            (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
          have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => χ n z)
              (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
            ((hχdiff n).continuous).aestronglyMeasurable
          have h2 : MeasureTheory.AEStronglyMeasurable phiW
              (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
            aestronglyMeasurable_phiW
          have h3 : MeasureTheory.AEStronglyMeasurable U
              (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
            have hUU : AEMeasurable (fun z => phiW z * U z)
                (MeasureTheory.volume.restrict Work.Spaces.Iz) := hUint'.aemeasurable
            have hφm : AEMeasurable phiW
                (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
              aemeasurable_phiW
            have hquot : AEMeasurable (fun z => (phiW z * U z) / phiW z)
                (MeasureTheory.volume.restrict Work.Spaces.Iz) := hUU.div hφm
            refine hquot.aestronglyMeasurable.congr ?_
            filter_upwards [ae_pos_of_mem_Iz] with z hz
            have hφz : phiW z ≠ 0 := by
              rw [phiW]
              exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (by linarith))
                (pow_ne_zero 2 hz.ne'))
            rw [mul_div_cancel_left₀ _ hφz]
          exact ((h1.mul h2).mul (h3.const_mul K))
        have hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
            ‖χ n z * phiW z * (K * U z)‖ ≤ K * (phiW z * U z) := by
          filter_upwards with z
          have hφ : 0 ≤ phiW z := phiW_nonneg z
          have hK0 : 0 ≤ K := le_of_lt hKpos
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hχ01 n z).1,
            abs_of_nonneg hφ, abs_of_nonneg (mul_nonneg hK0 (hUnn z))]
          calc χ n z * phiW z * (K * U z) ≤ 1 * phiW z * (K * U z) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 (hUnn z))
                exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
            _ = K * (phiW z * U z) := by ring
        exact Integrable.mono' (hUint'.const_mul K) haesm hbdd
      have hmono : (∫ z in Work.Spaces.Iz, -(χ n z * phiW z * σterm z))
          ≤ ∫ z in Work.Spaces.Iz, χ n z * phiW z * (K * U z) := by
        refine MeasureTheory.integral_mono_ae hneg hKint ?_
        filter_upwards [hslice] with z hz
        have hφ : 0 ≤ phiW z := phiW_nonneg z
        have hχ0 : 0 ≤ χ n z := (hχ01 n z).1
        have hprod : 0 ≤ χ n z * phiW z := mul_nonneg hχ0 hφ
        have hz' : -σterm z ≤ K * U z := by
          have hσz : σterm z = ∫ θ in Work.Spaces.Iθ,
              Work.Elliptic.Lzero u z θ * u z θ * σw θ := by simp only [hσterm]
          rw [hσz]; linarith [hz]
        calc -(χ n z * phiW z * σterm z) = χ n z * phiW z * (-σterm z) := by ring
          _ ≤ χ n z * phiW z * (K * U z) := mul_le_mul_of_nonneg_left hz' hprod
      have hval : (∫ z in Work.Spaces.Iz, χ n z * phiW z * (K * U z)) ≤ K * UU := by
        have h1 : (∫ z in Work.Spaces.Iz, χ n z * phiW z * (K * U z))
            ≤ ∫ z in Work.Spaces.Iz, K * (phiW z * U z) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z =>
              mul_nonneg (mul_nonneg (hχ01 n z).1 (phiW_nonneg z))
                (mul_nonneg (le_of_lt hKpos) (hUnn z)))
            (hUint'.const_mul K) ?_
          filter_upwards with z
          have hφ : 0 ≤ phiW z := phiW_nonneg z
          have hK0 : 0 ≤ K := le_of_lt hKpos
          calc χ n z * phiW z * (K * U z) ≤ 1 * phiW z * (K * U z) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 (hUnn z))
                exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
            _ = K * (phiW z * U z) := by ring
        have h2 : (∫ z in Work.Spaces.Iz, K * (phiW z * U z)) = K * UU := by
          rw [zIntegral_const_mul K (fun z => phiW z * U z), hUUdef]
        linarith [h1, h2]
      have h3 : -(∫ z in Work.Spaces.Iz, χ n z * phiW z * σterm z)
          = ∫ z in Work.Spaces.Iz, -(χ n z * phiW z * σterm z) := by
        rw [MeasureTheory.integral_neg]
      linarith [hmono, hval, h3]
    · have hzero : (∫ z in Work.Spaces.Iz, χ n z * phiW z * σterm z) = 0 :=
        MeasureTheory.integral_undef hint
      have hpos : 0 ≤ K * UU := mul_nonneg (le_of_lt hKpos) hUUnn
      rw [hzero]; linarith [hpos]
  -- ## (3) the `(z²w²)''` term
  have hB3 : ∀ n : ℕ, (∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z) ≤ C0 * UU := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z| ≤ C0 * phiW z := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      simpa only [phiW] using hχbd1 n z hz
    have h := weighted_le_of_bound
      (c := fun z => deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z)
      (m := U) (C := C0) (le_of_lt hC0pos) hUint' hUnn hb
    have h2 : |∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z| ≤ C0 * UU := by
      simpa only [hUUdef] using h
    linarith [le_abs_self (∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z), h2]
  -- ## (4) the `(zw²)'` term
  have hB4 : ∀ n : ℕ, -(∫ z in Work.Spaces.Iz,
      deriv (fun z => χ n z * phiW z * z) z * U z) ≤ C0 * UU := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |deriv (fun z => χ n z * phiW z * z) z| ≤ C0 * phiW z := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      simpa only [phiW] using hχbd2 n z hz
    have h := weighted_le_of_bound (c := fun z => deriv (fun z => χ n z * phiW z * z) z)
      (m := U) (C := C0) (le_of_lt hC0pos) hUint' hUnn hb
    have h2 : |∫ z in Work.Spaces.Iz,
        deriv (fun z => χ n z * phiW z * z) z * U z| ≤ C0 * UU := by
      simpa only [hUUdef] using h
    linarith [neg_le_abs (∫ z in Work.Spaces.Iz,
      deriv (fun z => χ n z * phiW z * z) z * U z), h2]
  -- ## the truncated identity
  have hident : ∀ n : ℕ,
      (∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * phiW z *
              (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
          + (∫ z in Work.Spaces.Iz, χ n z * phiW z *
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ * σw θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ))
          + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => χ n z * phiW z * z) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) := by
    intro n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2n : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
    have h1 := aeTruncSigmaIdD α u G hA (χ n) (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1))
      (by positivity)
      (by
        have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one h2n]; linarith
        linarith)
      (hχdiff n) (hχsupp n) (fun z => hχ01 n z)
    simpa only [phiW] using h1
  -- ## combining into a uniform bound
  have hkey : ∀ n : ℕ, α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
      ≤ (1 / 2) * (GG + UU) + K * UU + (α ^ 2 / 2) * (C0 * UU)
        + ((α * (5 + α)) / 2) * (C0 * UU) := by
    intro n
    have hid := hident n
    have h1 := hB1 n
    have h2 := hB2 n
    have h3 := hB3 n
    have h4 := hB4 n
    have hc1 : 0 ≤ α ^ 2 / 2 := by positivity
    have hc2 : 0 ≤ (α * (5 + α)) / 2 := by nlinarith [hα0]
    have h3' : (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) ≤ (α ^ 2 / 2) * (C0 * UU) :=
      mul_le_mul_of_nonneg_left h3 hc1
    have h4' : ((α * (5 + α)) / 2) * (-(∫ z in Work.Spaces.Iz,
        deriv (fun z => χ n z * phiW z * z) z
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ))) ≤ ((α * (5 + α)) / 2) * (C0 * UU) :=
      mul_le_mul_of_nonneg_left h4 hc2
    linarith [hid, h1, h2, h3', h4']
  -- ## the limit and the conclusion
  have hXeq : Work.Spaces.HkSq α 0 (grad u)
      = ∫ z in Work.Spaces.Iz, phiW z *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ) := by
    simpa only [grad, phiW] using HkSq_eq_weighted α (grad u)
  have hlim : Filter.Tendsto (fun n => α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)))
      Filter.atTop (nhds (α ^ 2 * Work.Spaces.HkSq α 0 (grad u))) := by
    rw [hXeq]
    exact (tendsto_radial_energy α u hA.smooth hXint χ hχdiff hχ01 hχlim).const_mul (α ^ 2)
  have hupper : α ^ 2 * Work.Spaces.HkSq α 0 (grad u)
      ≤ (1 / 2) * (GG + UU) + K * UU + (α ^ 2 / 2) * (C0 * UU)
        + ((α * (5 + α)) / 2) * (C0 * UU) :=
    le_of_tendsto' hlim hkey
  -- ## rewriting the two auxiliary scalars
  have hGGeq : GG = Work.Spaces.HkSq α 0 G := by
    rw [hGGdef, HkSq_eq_weighted α G]
  have hUUeq : UU = Work.Spaces.HkSq α 0 u := by
    rw [hUUdef, hUdef, ← HkSq_eq_weighted α u]
  have hGnn : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hUnn'' : 0 ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  rw [hGGeq, hUUeq] at hupper
  -- ## the constant
  have hα2le : α ^ 2 ≤ 1 / 16 := by
    have h := mul_le_mul hα4 hα4 hα0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [pow_two]
    calc α * α ≤ (1 / 4 : ℝ) * (1 / 4) := h
      _ = 1 / 16 := by norm_num
  have hC1 : (α ^ 2 / 2) * (C0 * Work.Spaces.HkSq α 0 u)
      ≤ (1 / 2) * (C0 * Work.Spaces.HkSq α 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hC0pos) hUnn'')
    linarith
  have hC2 : ((α * (5 + α)) / 2) * (C0 * Work.Spaces.HkSq α 0 u)
      ≤ 1 * (C0 * Work.Spaces.HkSq α 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hC0pos) hUnn'')
    nlinarith [hα4, hα0]
  nlinarith [hupper, hC1, hC2, hGnn, hUnn'', hKpos, hC0pos, hα0, hα2le]

end Work.FTS.EllipticEst.Dispatch.SigmaRad

namespace Work.FTS.EllipticEst.Dispatch

/-- **The `σ`-weighted radial energy inequality of Step 1 of `prop:H2`** (Elgindi, Annals
194 (2021)) in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData`, together with
the honesty of `z ∂_z u`:

`α² HkSq α 0 (z∂_zu) ≤ C (HkSq α 0 G + HkSq α 0 u)`.

This is the declaration of the required name `Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD`;
it is the `SigmaRad` theorem proved above in this file. -/
theorem aeSigmaEnergyD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
  Work.FTS.EllipticEst.Dispatch.SigmaRad.aeSigmaEnergyD

end Work.FTS.EllipticEst.Dispatch
