/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Dispatch._scratch.AeSigmaCleanCopy` — self-contained copy of the slice helpers

A copy of the helper lemmas of
`Submission/Work/FTS/EllipticEst/H2W/AeStepOneAux/aeSigmaEnergyClean.lean` (lines 1–334
there), with the import of `H2W.Ae.aeSigmaCutoffSeq` (whose cone now contains the
work-in-progress `H2W.Ae.SigmaCutWeight`) dropped.  The main theorem `aeSigmaEnergyH2` of the
original is *not* copied: its cutoff family is replaced by `Mine.zcutFam` in
`Dispatch.aeSigmaEnergyD`, which consumes these helpers.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.H2W.Ae.aesliceU
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The angular weight `sin(2θ)^{-η}` of the level-`0` estimate. -/
local notation "σw" => Work.FTS.EllipticEst.sEta

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem θIntegral_const_mul (c : ℝ) (h : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, c * h θ) = c * ∫ θ in Work.Spaces.Iθ, h θ :=
  MeasureTheory.integral_const_mul c h

theorem zIntegral_const_mul (c : ℝ) (h : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, c * h z) = c * ∫ z in Work.Spaces.Iz, h z :=
  MeasureTheory.integral_const_mul c h

/-! ## The weighted profile and the level-`0` integrand -/

/-- The squared radial weight `w(z)^2` of the level-`0` `z`-weight. -/
def phiW (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

theorem phiW_nonneg (z : ℝ) : 0 ≤ phiW z := by
  rw [phiW]; exact sq_nonneg _

theorem continuousOn_phiW_Ioi : ContinuousOn phiW (Set.Ioi 0) := by
  rw [show phiW = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 by
    funext z; rw [phiW]; simp [Work.Spaces.w]]
  refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

theorem aestronglyMeasurable_phiW :
    MeasureTheory.AEStronglyMeasurable phiW
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h : MeasureTheory.AEStronglyMeasurable phiW
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    continuousOn_phiW_Ioi.aestronglyMeasurable measurableSet_Ioi
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h

theorem aemeasurable_phiW :
    AEMeasurable phiW (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  aestronglyMeasurable_phiW.aemeasurable

/-- **The level-`0` integrand is the square of the weighted profile.** -/
theorem hkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.range_one, Finset.sum_singleton]
  norm_num

/-- On `Iθ` the level-`0` integrand is `w(z)² · (g z θ)² · σ θ`. -/
theorem hkIntegrand_eq_phiW_mul (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ = phiW z * ((g z θ) ^ 2 * σw θ) := by
  rw [hkIntegrand_zero_eq, phiW, Work.FTS.EllipticEst.sEta, div_eq_mul_inv, sq]
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hsin with h0 | hpos
  · rw [← h0]
    have h1 : Work.Spaces.eta / 2 ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have h2 : -(Work.Spaces.eta) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    rw [Real.zero_rpow h1, Real.zero_rpow h2]
    ring
  · have hsq : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_add hpos,
        show -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -(Work.Spaces.eta) by ring]
    rw [← Real.rpow_neg hpos.le (Work.Spaces.eta / 2)]
    rw [show g z θ * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
          * (g z θ * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))))
        = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) by ring]
    rw [hsq]; ring

/-- **`HkSq α 0` in weighted-slice form**: `∫_z w(z)² ∫_θ (g z θ)² σ θ`. -/
theorem HkSq_eq_weighted (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ) := by
  rw [Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [← θIntegral_const_mul (phiW z) (fun θ => (g z θ) ^ 2 * σw θ)]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_eq_phiW_mul α g hθ)

/-- **The weighted slice data of an honest function.** -/
theorem integrableOn_of_HkMem_zero {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    (∀ z, 0 < z →
        MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * σw θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z =>
        phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ)) Work.Spaces.Iz := by
  constructor
  · intro z hz
    have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have h1 : MeasureTheory.IntegrableOn (fun θ => phiW z * ((g z θ) ^ 2 * σw θ))
        Work.Spaces.Iθ :=
      (hg.1 z hzI).congr_fun_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hkIntegrand_eq_phiW_mul α g hθ)
    have hφz : phiW z ≠ 0 := by
      rw [phiW]
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith :
        (0 : ℝ) < 1 + z))) (pow_ne_zero 2 (ne_of_gt hz)))
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (phiW z)⁻¹ * (phiW z * ((g z θ) ^ 2 * σw θ))) Work.Spaces.Iθ :=
      h1.const_mul _
    refine h2.congr_fun ?_ measurableSet_Icc
    intro θ hθ
    show (phiW z)⁻¹ * (phiW z * ((g z θ) ^ 2 * σw θ)) = (g z θ) ^ 2 * σw θ
    rw [← mul_assoc, inv_mul_cancel₀ hφz, one_mul]
  · refine hg.2.congr_fun ?_ measurableSet_Ici
    intro z hz
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        = phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ)
    rw [← θIntegral_const_mul (phiW z) (fun θ => (g z θ) ^ 2 * σw θ)]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_eq_phiW_mul α g hθ)

/-- The weighted slice integrability in the shape used below. -/
theorem weighted_slice_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
  (integrableOn_of_HkMem_zero hg).2

/-- The slice mass `z ↦ ∫_θ (u z θ)² σ θ` is nonnegative. -/
theorem uMass_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) ?_)
  exact Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ

/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_pos_of_mem_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The first conjunct: the weighted radial profile is square integrable -/

/-- **`L2Mem` of the weighted radial first derivative**, from the honesty of `grad u`. -/
theorem l2mem_grad_profile {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  have hmem : Work.Spaces.HkMem α 0 (grad u) := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  have hgrad : grad u = fun z θ => z * Work.Spaces.pz u z θ := rfl
  constructor
  · intro z hz
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ)
        Work.Spaces.Iθ := hmem.1 z hz
    refine h1.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hkIntegrand_zero_eq α (fun z θ => z * Work.Spaces.pz u z θ) z θ
  · have h2 : MeasureTheory.IntegrableOn (fun z => phiW z * (∫ θ in Work.Spaces.Iθ,
        ((fun z θ => z * Work.Spaces.pz u z θ) z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
      weighted_slice_integrable hmem
    refine h2.congr_fun ?_ measurableSet_Ici
    intro z _
    show phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
      = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    rw [← θIntegral_const_mul (phiW z) (fun θ => (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [← hkIntegrand_zero_eq α (fun z θ => z * Work.Spaces.pz u z θ) z θ,
      hkIntegrand_eq_phiW_mul α (fun z θ => z * Work.Spaces.pz u z θ) hθ]

/-! ## Comparison lemmas -/

/-- **The angular AM–GM pairing bound.** -/
theorem theta_pairing_le {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * σw θ) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * σw θ) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, f θ * g θ * σw θ|
      ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σw θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σw θ)) := by
  have hstep1 : |∫ θ in Work.Spaces.Iθ, f θ * g θ * σw θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |f θ * g θ * σw θ| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun θ => f θ * g θ * σw θ)
  have hint : MeasureTheory.IntegrableOn (fun θ => (1 / 2) *
      ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ)) Work.Spaces.Iθ :=
    (hf.add hg).const_mul _
  have hstep2 : (∫ θ in Work.Spaces.Iθ, |f θ * g θ * σw θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hint ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show |f θ * g θ * σw θ| ≤ (1 / 2) * (f θ ^ 2 * σw θ + g θ ^ 2 * σw θ)
    have hσ : 0 ≤ σw θ := Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
    have hkey : |f θ| * |g θ| ≤ (1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2) := by
      have h := abs_mul (f θ) (g θ)
      nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ), h]
    rw [abs_mul, abs_mul, abs_of_nonneg hσ]
    calc |f θ| * |g θ| * σw θ ≤ ((1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2)) * σw θ :=
          mul_le_mul_of_nonneg_right hkey hσ
      _ = (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ) := by ring
  have hsplit : (∫ θ in Work.Spaces.Iθ, (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ))
      = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σw θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σw θ)) := by
    rw [θIntegral_const_mul (1 / 2), MeasureTheory.integral_add hf hg]
  linarith [hstep1, hstep2, hsplit]

/-- **A weighted comparison bound**: a function bounded by `C φ` integrates against a nonnegative
slice mass against `C φ · mass`. -/
theorem weighted_le_of_bound {c m : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmint : MeasureTheory.IntegrableOn (fun z => phiW z * m z) Work.Spaces.Iz)
    (hmnn : ∀ z, 0 ≤ m z)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), |c z| ≤ C * phiW z) :
    |∫ z in Work.Spaces.Iz, c z * m z| ≤ C * (∫ z in Work.Spaces.Iz, phiW z * m z) := by
  have hstep1 : |∫ z in Work.Spaces.Iz, c z * m z|
      ≤ ∫ z in Work.Spaces.Iz, |c z * m z| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun z => c z * m z)
  have hint : MeasureTheory.IntegrableOn (fun z => C * (phiW z * m z)) Work.Spaces.Iz :=
    hmint.const_mul C
  have hstep2 : (∫ z in Work.Spaces.Iz, |c z * m z|)
      ≤ ∫ z in Work.Spaces.Iz, C * (phiW z * m z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hint ?_
    filter_upwards [hbound] with z hz
    rw [abs_mul]
    calc |c z| * |m z| ≤ (C * phiW z) * m z :=
          mul_le_mul hz (by rw [abs_of_nonneg (hmnn z)]) (abs_nonneg _)
            (mul_nonneg hC (phiW_nonneg z))
      _ = C * (phiW z * m z) := by ring
  have hsplit : (∫ z in Work.Spaces.Iz, C * (phiW z * m z))
      = C * (∫ z in Work.Spaces.Iz, phiW z * m z) :=
    zIntegral_const_mul C (fun z => phiW z * m z)
  linarith [hstep1, hstep2, hsplit]

/-- **The monotone-cutoff limit of the radial energy term.** -/
theorem tendsto_radial_energy (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hXint : MeasureTheory.IntegrableOn (fun z => phiW z *
      (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)) Work.Spaces.Iz)
    (χ : ℕ → ℝ → ℝ) (hχdiff : ∀ n, ContDiff ℝ 2 (χ n))
    (hχ01 : ∀ n z, 0 ≤ χ n z ∧ χ n z ≤ 1)
    (hχlim : ∀ z, 0 < z → Filter.Tendsto (fun n => χ n z) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => ∫ z in Work.Spaces.Iz, χ n z * phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun z => phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
    ?_ hXint ?_ ?_
  · intro n
    have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => χ n z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      ((hχdiff n).continuous).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable phiW
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      aestronglyMeasurable_phiW
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * σw p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have hpz : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          ((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pz.forall 1).continuousOn
        have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
            (Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
        have hsE : ContinuousOn (fun θ : ℝ => σw θ) (Set.Ioo 0 (Real.pi / 2)) :=
          hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt
            (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
              (by linarith [hθ.2, Real.pi_pos]))))
        have hz : ContinuousOn (fun p : ℝ × ℝ => p.1)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_fst
        have hθ : ContinuousOn (fun p : ℝ × ℝ => p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_snd
        exact ((hz.mul hpz).pow 2).mul (hsE.comp hθ (fun p hp => hp.2))
      exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      exact (h1.mul h2).mul h3
    exact hprod
  · intro n
    filter_upwards with z
    have hφ : 0 ≤ phiW z := phiW_nonneg z
    have hmi : 0 ≤ ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) ?_)
      exact Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hχ01 n z).1 hφ) hmi)]
    calc χ n z * phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
        ≤ 1 * phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ) := by
          refine mul_le_mul_of_nonneg_right ?_ hmi
          exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
      _ = phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ) := by ring
  · filter_upwards [ae_pos_of_mem_Iz] with z hz
    have h1 : Filter.Tendsto (fun n => χ n z * phiW z) Filter.atTop (nhds (1 * phiW z)) :=
      (hχlim z hz).mul tendsto_const_nhds
    have h2 := h1.mul_const (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
    simpa only [one_mul] using h2

/-! ## The main theorem -/

