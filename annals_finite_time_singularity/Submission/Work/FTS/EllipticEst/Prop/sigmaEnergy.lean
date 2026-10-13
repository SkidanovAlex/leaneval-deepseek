/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Prop.sigmaEnergy` — the `σ`-weighted radial energy inequality in the `AeData` class

This module proves

`∃ C > 0, ∀ α u G, AeData α u G → α² · HkSq α 0 (z ∂_z u) ≤ C · (HkSq α 0 G + HkSq α 0 u)`

(Elgindi, Annals **194** (2021), Step 1 of Proposition `prop:H2`, in the almost-everywhere class
`Work.FTS.EllipticEst.H2W.Ae.AeData`).

## Route

For the cut-off family `χ n = Work.FTS.EllipticEst.cut n` (vanishing for `z ≤ 1/(n+1)` and for
`z ≥ 3(n+1)`, equal to `1` on `[2/(n+1), 2(n+1)]`) the `σ`-weighted *truncated radial energy
identity*

  `∫ χ w² (G·u) σ = α² ∫ χ w² z² (∂_zu)² σ + ∫ χ w² (L₀u·u) σ
      − (α²/2) ∫ (χ w² z²)'' (u²σ) + (α(5+α)/2) ∫ (χ w² z)' (u²σ)`

is the proved `Dispatch.sigTruncIdentD` (with the five joint-integrability hypotheses supplied by
the proved `Dispatch.sigJointD`).  The four terms are then bounded by:

* `G·u` pairing: AM–GM in `θ` ⟹ `(1/2)(‖G‖² + ‖u‖²)`;
* `L₀u·u` pairing: the a.e. slice coercivity `Frontier.aeSigmaSliceLowerFts`
  ⟹ `−∫ χ w² (L₀u·u) σ ≤ K ‖u‖²`;
* the two cut-off error terms: the uniform weighted derivative bounds `cutWeightBounds`
  ⟹ `≤ C₀ ‖u‖²` each.

Letting `n → ∞` by dominated convergence (`tendsto_radial_energy`, with the weight
`χ n w² → w²` pointwise and the dominating function `w² (z ∂_zu)²σ ∈ L¹` supplied by the
honesty `Dispatch.hkMem_gradUD`) and rewriting `HkSq α 0` in weighted-slice form
(`Honest.hksq_eq_w2_sliceIntegral`) gives the claim.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.sigJointD
import Submission.Work.FTS.EllipticEst.Frontier.aeSigmaSliceLowerFts
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ
local notation "σw" => Work.FTS.EllipticEst.sEta
local notation "Lz" => Work.Elliptic.Lzero

/-! ## Elementary facts about the weights -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ σw θ :=
  Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθ

/-- The `θ`-slice of `Work.Elliptic.Lzero` is `Lzero1`. -/
theorem Lzero1_slice_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Lz u z θ = Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-! ## The radial weight `w²` and its basic properties -/

/-- The squared radial weight `w(z)²`. -/
def phiW (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

theorem phiW_nonneg (z : ℝ) : 0 ≤ phiW z := by rw [phiW]; exact sq_nonneg _

theorem continuousOn_phiW_Ioi : ContinuousOn phiW (Set.Ioi 0) := by
  rw [show phiW = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 by
    funext z; rw [phiW]; simp [Work.Spaces.w]]
  refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

theorem aestronglyMeasurable_phiW :
    MeasureTheory.AEStronglyMeasurable phiW
      (MeasureTheory.volume.restrict Iz) := by
  have h : MeasureTheory.AEStronglyMeasurable phiW
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    continuousOn_phiW_Ioi.aestronglyMeasurable measurableSet_Ioi
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h

theorem aemeasurable_phiW : AEMeasurable phiW (MeasureTheory.volume.restrict Iz) :=
  aestronglyMeasurable_phiW.aemeasurable

theorem θIntegral_const_mul (c : ℝ) (h : ℝ → ℝ) :
    (∫ θ in Iθ, c * h θ) = c * ∫ θ in Iθ, h θ :=
  MeasureTheory.integral_const_mul c h

theorem zIntegral_const_mul (c : ℝ) (h : ℝ → ℝ) :
    (∫ z in Iz, c * h z) = c * ∫ z in Iz, h z :=
  MeasureTheory.integral_const_mul c h

/-! ## The level-`0` integrand -/

/-- **The level-`0` integrand is the square of the weighted profile.** -/
theorem hkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.range_one, Finset.sum_singleton]
  norm_num

/-- On `Iθ` the level-`0` integrand is `w(z)² · (g z θ)² · σ θ`. -/
theorem hkIntegrand_eq_phiW_mul (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
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
      = ∫ z in Iz, phiW z * (∫ θ in Iθ, (g z θ) ^ 2 * σw θ) := by
  rw [Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [← θIntegral_const_mul (phiW z) (fun θ => (g z θ) ^ 2 * σw θ)]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_eq_phiW_mul α g hθ)

/-- **The weighted slice data of an honest function.** -/
theorem integrableOn_of_HkMem_zero {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    (∀ z, 0 < z →
        MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * σw θ) Iθ) ∧
      MeasureTheory.IntegrableOn (fun z =>
        phiW z * (∫ θ in Iθ, (g z θ) ^ 2 * σw θ)) Iz := by
  constructor
  · intro z hz
    have hzI : z ∈ Iz := Set.mem_Ici.mpr hz.le
    have h1 : MeasureTheory.IntegrableOn (fun θ => phiW z * ((g z θ) ^ 2 * σw θ)) Iθ :=
      (hg.1 z hzI).congr_fun_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hkIntegrand_eq_phiW_mul α g hθ)
    have hφz : phiW z ≠ 0 := by
      rw [phiW]
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith :
        (0 : ℝ) < 1 + z))) (pow_ne_zero 2 (ne_of_gt hz)))
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (phiW z)⁻¹ * (phiW z * ((g z θ) ^ 2 * σw θ))) Iθ :=
      h1.const_mul _
    refine h2.congr_fun ?_ measurableSet_Icc
    intro θ hθ
    show (phiW z)⁻¹ * (phiW z * ((g z θ) ^ 2 * σw θ)) = (g z θ) ^ 2 * σw θ
    rw [← mul_assoc, inv_mul_cancel₀ hφz, one_mul]
  · refine hg.2.congr_fun ?_ measurableSet_Ici
    intro z hz
    show (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        = phiW z * (∫ θ in Iθ, (g z θ) ^ 2 * σw θ)
    rw [← θIntegral_const_mul (phiW z) (fun θ => (g z θ) ^ 2 * σw θ)]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_eq_phiW_mul α g hθ)

/-- The weighted slice integrability in the shape used below. -/
theorem weighted_slice_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Iθ, (g z θ) ^ 2 * σw θ)) Iz :=
  (integrableOn_of_HkMem_zero hg).2

/-- The slice mass `z ↦ ∫_θ (u z θ)² σ θ` is nonnegative. -/
theorem uMass_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Iθ, (u z θ) ^ 2 * σw θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))

/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_pos_of_mem_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- Pulling `z²` out of the `σ`-weighted angular square. -/
theorem mul_sq_slice (z : ℝ) (f : ℝ → ℝ) :
    z ^ 2 * (∫ θ in Iθ, σw θ * (f θ) ^ 2) = ∫ θ in Iθ, σw θ * (z * f θ) ^ 2 := by
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

/-! ## Comparison lemmas -/

/-- **The angular AM–GM pairing bound.** -/
theorem theta_pairing_le {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * σw θ) Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * σw θ) Iθ) :
    |∫ θ in Iθ, σw θ * (f θ * g θ)|
      ≤ (1 / 2) * ((∫ θ in Iθ, (f θ) ^ 2 * σw θ)
        + (∫ θ in Iθ, (g θ) ^ 2 * σw θ)) := by
  have hstep1 : |∫ θ in Iθ, σw θ * (f θ * g θ)|
      ≤ ∫ θ in Iθ, |σw θ * (f θ * g θ)| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun θ => σw θ * (f θ * g θ))
  have hint : MeasureTheory.IntegrableOn (fun θ => (1 / 2) *
      ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ)) Iθ :=
    (hf.add hg).const_mul _
  have hstep2 : (∫ θ in Iθ, |σw θ * (f θ * g θ)|)
      ≤ ∫ θ in Iθ, (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hint ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show |σw θ * (f θ * g θ)| ≤ (1 / 2) * (f θ ^ 2 * σw θ + g θ ^ 2 * σw θ)
    have hσ : 0 ≤ σw θ := sEta_nonneg_Iθ hθ
    have hkey : |f θ| * |g θ| ≤ (1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2) := by
      have h := abs_mul (f θ) (g θ)
      nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ), h]
    rw [abs_mul, abs_mul, abs_of_nonneg hσ]
    calc σw θ * (|f θ| * |g θ|) ≤ σw θ * ((1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hkey hσ
      _ = (1 / 2) * (f θ ^ 2 * σw θ + g θ ^ 2 * σw θ) := by ring
  have hsplit : (∫ θ in Iθ, (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ))
      = (1 / 2) * ((∫ θ in Iθ, (f θ) ^ 2 * σw θ) + (∫ θ in Iθ, (g θ) ^ 2 * σw θ)) := by
    rw [θIntegral_const_mul (1 / 2), MeasureTheory.integral_add hf hg]
  linarith [hstep1, hstep2, hsplit]

/-- **A weighted comparison bound**: a function bounded by `C φ` integrates against a nonnegative
slice mass against `C φ · mass`. -/
theorem weighted_le_of_bound {c m : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmint : MeasureTheory.IntegrableOn (fun z => phiW z * m z) Iz)
    (hmnn : ∀ z, 0 ≤ m z)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), |c z| ≤ C * phiW z) :
    |∫ z in Iz, c z * m z| ≤ C * (∫ z in Iz, phiW z * m z) := by
  have hstep1 : |∫ z in Iz, c z * m z|
      ≤ ∫ z in Iz, |c z * m z| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun z => c z * m z)
  have hint : MeasureTheory.IntegrableOn (fun z => C * (phiW z * m z)) Iz :=
    hmint.const_mul C
  have hstep2 : (∫ z in Iz, |c z * m z|)
      ≤ ∫ z in Iz, C * (phiW z * m z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hint ?_
    filter_upwards [hbound] with z hz
    rw [abs_mul]
    calc |c z| * |m z| ≤ (C * phiW z) * m z :=
          mul_le_mul hz (by rw [abs_of_nonneg (hmnn z)]) (abs_nonneg _)
            (mul_nonneg hC (phiW_nonneg z))
      _ = C * (phiW z * m z) := by ring
  have hsplit : (∫ z in Iz, C * (phiW z * m z))
      = C * (∫ z in Iz, phiW z * m z) :=
    zIntegral_const_mul C (fun z => phiW z * m z)
  linarith [hstep1, hstep2, hsplit]

/-- **The monotone-cutoff limit of the radial energy term.** -/
theorem tendsto_radial_energy (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hXint : MeasureTheory.IntegrableOn (fun z => phiW z *
      (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)) Iz)
    (χ : ℕ → ℝ → ℝ) (hχdiff : ∀ n, ContDiff ℝ 2 (χ n))
    (hχ01 : ∀ n z, 0 ≤ χ n z ∧ χ n z ≤ 1)
    (hχlim : ∀ z, 0 < z → Filter.Tendsto (fun n => χ n z) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => ∫ z in Iz, χ n z * phiW z *
        (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)) Filter.atTop
      (nhds (∫ z in Iz, phiW z *
        (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2))) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun z => phiW z * (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2))
    ?_ hXint ?_ ?_
  · intro n
    have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => χ n z)
        (MeasureTheory.volume.restrict Iz) :=
      ((hχdiff n).continuous).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable phiW
        (MeasureTheory.volume.restrict Iz) :=
      aestronglyMeasurable_phiW
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)
        (MeasureTheory.volume.restrict Iz) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          σw p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
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
        exact (hsE.comp hθ (fun p hp => hp.2)).mul ((hz.mul hpz).pow 2)
      exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    exact (h1.mul h2).mul h3
  · intro n
    filter_upwards with z
    have hφ : 0 ≤ phiW z := phiW_nonneg z
    have hmi : 0 ≤ ∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2 := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sEta_nonneg_Iθ hθ) (sq_nonneg _))
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hχ01 n z).1 hφ) hmi)]
    calc χ n z * phiW z * (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)
        ≤ 1 * phiW z * (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hmi
          exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
      _ = phiW z * (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2) := by ring
  · filter_upwards [ae_pos_of_mem_Iz] with z hz
    have h1 : Filter.Tendsto (fun n => χ n z * phiW z) Filter.atTop (nhds (1 * phiW z)) :=
      (hχlim z hz).mul tendsto_const_nhds
    have h2 := h1.mul_const (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)
    simpa only [one_mul] using h2

/-! ## Uniform weighted derivative bounds for the cut-off family -/

/-- **Uniform weighted derivative bounds for `cut n`.**  The two composites
`z ↦ cut n z · w(z)² · z` and `z ↦ cut n z · w(z)² · z²` have derivatives bounded by a constant,
independent of `n`, times `w(z)²` on `z > 0`.

Proof: `AngSecond.cut_deriv_uniform` gives `K` with `|z (cut n)'(z)| ≤ K` and
`AngularW.cutZ2Deriv2` gives `K₂` with `|z² (cut n)''(z)| ≤ K₂`; the product rule plus
`weight_algebra_fts` (the explicit derivatives of `z w² = (1+z)⁴/z³` and
`z² w² = (1+z)⁴/z²`) give the bound with `C := K₂ + 5K + 9`. -/
theorem cutWeightBounds : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ z : ℝ, 0 < z →
      |deriv (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z') z|
          ≤ C * (Work.Spaces.w z) ^ 2 ∧
      |deriv (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
          * (Work.Spaces.w z') ^ 2 * z' ^ 2)) z| ≤ C * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨K, hKpos, hK1, _hK2, _hK3⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  obtain ⟨K2, hK2pos, hK2⟩ := Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
  obtain ⟨hFa, hFb, hFc, hFd, hFe, hFf, hFg, hFh, hFi, hFj, hFk⟩ :=
    Work.FTS.EllipticEst.weight_algebra_fts
  refine ⟨K2 + 5 * K + 9, by linarith, fun n z hz => ⟨?_, ?_⟩⟩
  · -- the first composite
    have hz' : z ≠ 0 := ne_of_gt hz
    have hCdiff : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) := by
      have h := Work.FTS.EllipticEst.cut_contDiff n
      rw [Work.Stability.smoothOrder] at h
      exact h.of_le (WithTop.coe_le_coe.mpr le_top)
    have hcutD : DifferentiableAt ℝ (Work.FTS.EllipticEst.cut n) z :=
      (hCdiff.differentiable (by norm_num)).differentiableAt
    have hratD : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z := by
      have hcd : ContDiffOn ℝ 2 (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) (Set.Ioi 0) :=
        ((contDiff_const.add contDiff_id).pow 4).contDiffOn.div
          ((contDiff_id.pow 3).contDiffOn) (fun y hy => pow_ne_zero 3 (ne_of_gt hy))
      exact (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
    have hgD : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z :=
      hratD.congr_of_eventuallyEq (by
        filter_upwards [isOpen_ne.mem_nhds hz'] with y hy
        exact hFb y hy)
    have hder : deriv (fun y : ℝ => Work.FTS.EllipticEst.cut n y
          * (y * (Work.Spaces.w y) ^ 2)) z
        = deriv (Work.FTS.EllipticEst.cut n) z * (z * (Work.Spaces.w z) ^ 2)
          + Work.FTS.EllipticEst.cut n z * ((z - 3) * (1 + z) ^ 3 / z ^ 4) := by
      have h1 : deriv (fun y : ℝ => Work.FTS.EllipticEst.cut n y
            * (y * (Work.Spaces.w y) ^ 2)) z
          = deriv (Work.FTS.EllipticEst.cut n) z * (z * (Work.Spaces.w z) ^ 2)
            + Work.FTS.EllipticEst.cut n z
                * deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z :=
        deriv_mul hcutD hgD
      rw [h1, hFd z hz']
    rw [show (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z')
        = (fun y : ℝ => Work.FTS.EllipticEst.cut n y * (y * (Work.Spaces.w y) ^ 2)) from by
      funext y; ring, hder]
    have hb1 : |deriv (Work.FTS.EllipticEst.cut n) z * (z * (Work.Spaces.w z) ^ 2)|
        ≤ K * (Work.Spaces.w z) ^ 2 := by
      rw [show deriv (Work.FTS.EllipticEst.cut n) z * (z * (Work.Spaces.w z) ^ 2)
          = (z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2 from by ring,
        abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      exact mul_le_mul_of_nonneg_right (hK1 n z) (sq_nonneg _)
    have hb2 : |Work.FTS.EllipticEst.cut n z * ((z - 3) * (1 + z) ^ 3 / z ^ 4)|
        ≤ 3 * (Work.Spaces.w z) ^ 2 := by
      rw [abs_mul]
      have hcut : |Work.FTS.EllipticEst.cut n z| ≤ 1 := by
        rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)]
        exact Work.FTS.EllipticEst.cut_le_one n z
      have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [Work.Spaces.w, div_pow]; ring
      calc |Work.FTS.EllipticEst.cut n z| * |(z - 3) * (1 + z) ^ 3 / z ^ 4|
          ≤ 1 * |(z - 3) * (1 + z) ^ 3 / z ^ 4| :=
            mul_le_mul_of_nonneg_right hcut (abs_nonneg _)
        _ ≤ 3 * (Work.Spaces.w z) ^ 2 := by
            rw [one_mul, hw, abs_div, abs_mul,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+z)^3),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ z^4)]
            rw [div_le_iff₀ (by positivity : (0:ℝ) < z^4)]
            have hz3 : |z - 3| ≤ 3 * (1 + z) := by rw [abs_le]; constructor <;> linarith
            have h13 : (0:ℝ) < (1+z)^3 := by positivity
            calc |z - 3| * (1 + z) ^ 3 ≤ 3 * (1 + z) * (1 + z) ^ 3 :=
                  mul_le_mul_of_nonneg_right hz3 (le_of_lt h13)
              _ = 3 * ((1 + z) ^ 4 / z ^ 4) * z ^ 4 := by field_simp
    calc |deriv (Work.FTS.EllipticEst.cut n) z * (z * (Work.Spaces.w z) ^ 2)
          + Work.FTS.EllipticEst.cut n z * ((z - 3) * (1 + z) ^ 3 / z ^ 4)|
        ≤ |deriv (Work.FTS.EllipticEst.cut n) z * (z * (Work.Spaces.w z) ^ 2)|
          + |Work.FTS.EllipticEst.cut n z * ((z - 3) * (1 + z) ^ 3 / z ^ 4)| := abs_add_le _ _
      _ ≤ K * (Work.Spaces.w z) ^ 2 + 3 * (Work.Spaces.w z) ^ 2 := add_le_add hb1 hb2
      _ ≤ (K2 + 5 * K + 9) * (Work.Spaces.w z) ^ 2 := by
          have h0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          nlinarith [hKpos, hK2pos]
  · -- the second composite
    have hz' : z ≠ 0 := ne_of_gt hz
    have hFcd : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) (Set.Ioi 0) := by
      have h1 : ContDiffOn ℝ 2 (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) (Set.Ioi 0) :=
        ((contDiff_const.add contDiff_id).pow 4).contDiffOn.div
          ((contDiff_id.pow 2).contDiffOn) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))
      refine h1.congr (fun y hy => ?_)
      rw [hFa y (ne_of_gt hy)]
    have hcdχ2 : ContDiffOn ℝ 2 (Work.FTS.EllipticEst.cut n) (Set.Ioi 0) :=
      ((Work.FTS.EllipticEst.cut_contDiff n).of_le (by norm_num)).contDiffOn
    have hder2 : deriv (deriv (fun y : ℝ =>
          Work.FTS.EllipticEst.cut n y * (y ^ 2 * (Work.Spaces.w y) ^ 2))) z
        = deriv (deriv (Work.FTS.EllipticEst.cut n)) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          + 2 * deriv (Work.FTS.EllipticEst.cut n) z
              * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
          + Work.FTS.EllipticEst.cut n z
              * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z := by
      have heq2 : (fun y => deriv (fun w : ℝ =>
            Work.FTS.EllipticEst.cut n w * (w ^ 2 * (Work.Spaces.w w) ^ 2)) y)
          =ᶠ[𝓝 z] (fun y => deriv (Work.FTS.EllipticEst.cut n) y
              * (y ^ 2 * (Work.Spaces.w y) ^ 2)
            + Work.FTS.EllipticEst.cut n y
              * deriv (fun w : ℝ => w ^ 2 * (Work.Spaces.w w) ^ 2) y) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        have hdy : DifferentiableAt ℝ (Work.FTS.EllipticEst.cut n) y :=
          (hcdχ2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hy)
        have hdFy : DifferentiableAt ℝ (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) y :=
          (hFcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hy)
        exact deriv_mul hdy hdFy
      change deriv (fun y => deriv (fun w : ℝ =>
        Work.FTS.EllipticEst.cut n w * (w ^ 2 * (Work.Spaces.w w) ^ 2)) y) z = _
      rw [Filter.EventuallyEq.deriv_eq heq2]
      have hsum : (fun y => deriv (Work.FTS.EllipticEst.cut n) y * (y ^ 2 * (Work.Spaces.w y) ^ 2)
            + Work.FTS.EllipticEst.cut n y * deriv (fun w : ℝ => w ^ 2 * (Work.Spaces.w w) ^ 2) y)
          = (fun y => deriv (Work.FTS.EllipticEst.cut n) y * (y ^ 2 * (Work.Spaces.w y) ^ 2))
            + (fun y => Work.FTS.EllipticEst.cut n y
                * deriv (fun w : ℝ => w ^ 2 * (Work.Spaces.w w) ^ 2) y) := rfl
      rw [hsum]
      have h1 : HasDerivAt (fun y => deriv (Work.FTS.EllipticEst.cut n) y
            * (y ^ 2 * (Work.Spaces.w y) ^ 2))
          (deriv (deriv (Work.FTS.EllipticEst.cut n)) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
            + deriv (Work.FTS.EllipticEst.cut n) z
              * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z) z :=
        (((hcdχ2.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
            (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt.mul
          ((hFcd.differentiableOn (by norm_num)).differentiableAt
            (isOpen_Ioi.mem_nhds hz)).hasDerivAt
      have h2 : HasDerivAt (fun y => Work.FTS.EllipticEst.cut n y
            * deriv (fun w : ℝ => w ^ 2 * (Work.Spaces.w w) ^ 2) y)
          (deriv (Work.FTS.EllipticEst.cut n) z
              * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
            + Work.FTS.EllipticEst.cut n z
              * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z) z :=
        ((hcdχ2.differentiableOn (by norm_num)).differentiableAt
            (isOpen_Ioi.mem_nhds hz)).hasDerivAt.mul
          (((hFcd.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
            (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
      rw [(h1.add h2).deriv]; ring
    have hfun2 : (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z' ^ 2)
        = (fun y : ℝ => Work.FTS.EllipticEst.cut n y * (y ^ 2 * (Work.Spaces.w y) ^ 2)) := by
      funext y; ring
    rw [hfun2, hder2]
    have hb1 : |deriv (deriv (Work.FTS.EllipticEst.cut n)) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)|
        ≤ K2 * (Work.Spaces.w z) ^ 2 := by
      rw [show deriv (deriv (Work.FTS.EllipticEst.cut n)) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          = (z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.cut n)) z) * (Work.Spaces.w z) ^ 2
            from by ring,
        abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      exact mul_le_mul_of_nonneg_right (hK2 n z) (sq_nonneg _)
    have hb2 : |2 * deriv (Work.FTS.EllipticEst.cut n) z
          * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        ≤ 4 * K * (Work.Spaces.w z) ^ 2 := by
      have hFder : deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
          = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 := hFc z hz'
      have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [Work.Spaces.w, div_pow]; ring
      have h2 : |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z / z|
          ≤ 2 * (Work.Spaces.w z) ^ 2 := by
        rw [hFder, hw]
        rw [show 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 / z
            = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 4 from by field_simp]
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+z)^3),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ z^4)]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < z^4)]
        have hz1 : |z - 1| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
        have h13 : (0:ℝ) < (1+z)^3 := by positivity
        calc 2 * |z - 1| * (1 + z) ^ 3 ≤ 2 * (1 + z) * (1 + z) ^ 3 :=
              mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h13)
          _ = 2 * ((1 + z) ^ 4 / z ^ 4) * z ^ 4 := by field_simp
      calc |2 * deriv (Work.FTS.EllipticEst.cut n) z
            * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          = 2 * |z * deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z / z| := by
            rw [show 2 * deriv (Work.FTS.EllipticEst.cut n) z
                * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
                = 2 * (z * deriv (Work.FTS.EllipticEst.cut n) z)
                  * (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z / z)
                from by field_simp]
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        _ ≤ 2 * K * (2 * (Work.Spaces.w z) ^ 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hK1 n z) (by norm_num)) h2
              (abs_nonneg _) (by positivity)
        _ = 4 * K * (Work.Spaces.w z) ^ 2 := by ring
    have hb3 : |Work.FTS.EllipticEst.cut n z
          * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z|
        ≤ 6 * (Work.Spaces.w z) ^ 2 := by
      have hcut : |Work.FTS.EllipticEst.cut n z| ≤ 1 := by
        rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)]
        exact Work.FTS.EllipticEst.cut_le_one n z
      rw [abs_mul]
      calc |Work.FTS.EllipticEst.cut n z|
            * |deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z|
          ≤ 1 * (6 * (Work.Spaces.w z) ^ 2) := by
            refine mul_le_mul hcut ?_ (abs_nonneg _) (by norm_num)
            rw [abs_of_nonneg (hFh z hz)]
            exact hFf z hz
        _ = 6 * (Work.Spaces.w z) ^ 2 := by ring
    calc |deriv (deriv (Work.FTS.EllipticEst.cut n)) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          + 2 * deriv (Work.FTS.EllipticEst.cut n) z
              * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
          + Work.FTS.EllipticEst.cut n z
              * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z|
        ≤ |deriv (deriv (Work.FTS.EllipticEst.cut n)) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)|
          + |2 * deriv (Work.FTS.EllipticEst.cut n) z
              * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          + |Work.FTS.EllipticEst.cut n z
              * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z| := by
          linarith [abs_add_le (deriv (deriv (Work.FTS.EllipticEst.cut n)) z
              * (z ^ 2 * (Work.Spaces.w z) ^ 2)
              + 2 * deriv (Work.FTS.EllipticEst.cut n) z
                * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)
            (Work.FTS.EllipticEst.cut n z
              * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z),
            abs_add_le (deriv (deriv (Work.FTS.EllipticEst.cut n)) z
              * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            (2 * deriv (Work.FTS.EllipticEst.cut n) z
              * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)]
      _ ≤ K2 * (Work.Spaces.w z) ^ 2 + 4 * K * (Work.Spaces.w z) ^ 2
            + 6 * (Work.Spaces.w z) ^ 2 := by linarith [hb1, hb2, hb3]
      _ ≤ (K2 + 5 * K + 9) * (Work.Spaces.w z) ^ 2 := by
          have h0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          nlinarith [hKpos, hK2pos]

/-! ## The main estimate -/

theorem sigmaEnergy : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨K, hKpos, hKslice⟩ := Work.FTS.EllipticEst.Frontier.aeSigmaSliceLowerFts
  obtain ⟨C0, hC0pos, hC0⟩ := cutWeightBounds
  obtain ⟨Kc, hKcpos, _hcutd, hcutlim, _⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  refine ⟨3 + K + 2 * C0, by linarith, ?_⟩
  intro α u G hA
  set χ : ℕ → ℝ → ℝ := fun n => Work.FTS.EllipticEst.cut n with hχdef
  have hχdiff : ∀ n : ℕ, ContDiff ℝ 2 (χ n) := by
    intro n
    have h := Work.FTS.EllipticEst.cut_contDiff n
    rw [Work.Stability.smoothOrder] at h
    exact h.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχ01 : ∀ (n : ℕ) (z : ℝ), 0 ≤ χ n z ∧ χ n z ≤ 1 := by
    intro n z
    exact ⟨Work.FTS.EllipticEst.cut_nonneg n z, Work.FTS.EllipticEst.cut_le_one n z⟩
  have hχlim : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun n => χ n z) Filter.atTop (nhds 1) := by
    intro z hz
    exact hcutlim z hz
  have hχcpt : ∀ n : ℕ, HasCompactSupport (χ n) := by
    intro n
    have hsub : Function.support (χ n) ⊆
        Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) := by
      intro z hz
      simp only [Function.mem_support] at hz
      rw [Set.mem_Icc]
      constructor
      · by_contra h
        exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt (not_le.mp h)))
      · by_contra h
        exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt (not_le.mp h)))
    have hts : tsupport (χ n) ⊆
        Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) :=
      closure_minimal hsub isClosed_Icc
    exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts
  have hχ0 : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → χ n z = 0 := by
    intro n
    exact ⟨1 / ((n : ℝ) + 1), by positivity,
      fun z hz => Work.FTS.EllipticEst.cut_apply_zero_of_le n hz⟩
  have hχbd1 : ∀ n : ℕ, ∀ z : ℝ, 0 < z →
      |deriv (deriv (fun z' => χ n z' * phiW z' * z' ^ 2)) z| ≤ C0 * phiW z := by
    intro n z hz
    have h := (hC0 n z hz).2
    have hfun : (fun z' => χ n z' * phiW z' * z' ^ 2)
        = (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z' ^ 2) := by
      funext y; rw [hχdef]; simp only [phiW]
    rw [hfun, phiW]
    exact h
  have hχbd2 : ∀ n : ℕ, ∀ z : ℝ, 0 < z →
      |deriv (fun z' => χ n z' * phiW z' * z') z| ≤ C0 * phiW z := by
    intro n z hz
    have h := (hC0 n z hz).1
    have hfun : (fun z' => χ n z' * phiW z' * z')
        = (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z') := by
      funext y; rw [hχdef]; simp only [phiW]
    rw [hfun, phiW]
    exact h
  have hα0 : 0 ≤ α := le_of_lt (Work.FTS.EllipticEst.H2W.Ae.AeData.hα hA)
  have hα4 : α ≤ 1 / 4 := Work.FTS.EllipticEst.H2W.Ae.AeData.hα4 hA
  have hmemU : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hmemX : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hmemG : Work.Spaces.HkMem α 0 G := Work.FTS.EllipticEst.H2W.Ae.AeData.memG hA
  have hUint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Iθ, (u z θ) ^ 2 * σw θ)) Iz := weighted_slice_integrable hmemU
  have hGint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Iθ, (G z θ) ^ 2 * σw θ)) Iz := weighted_slice_integrable hmemG
  have hXint : MeasureTheory.IntegrableOn (fun z => phiW z *
      (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)) Iz := by
    refine (weighted_slice_integrable hmemX).congr_fun ?_ measurableSet_Ici
    intro z hz
    exact congrArg (fun t => phiW z * t)
      (setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [Work.FTS.EllipticEst.H2W.Ae.grad]; ring))
  have hUslice : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * σw θ) Iθ := (integrableOn_of_HkMem_zero hmemU).1
  have hGslice : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (G z θ) ^ 2 * σw θ) Iθ := (integrableOn_of_HkMem_zero hmemG).1
  -- the a.e. slice coercivity, transported to `Iz`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      -K * (∫ θ in Iθ, (u z θ) ^ 2 * σw θ)
        ≤ ∫ θ in Iθ, σw θ * (Lz u z θ * u z θ) := by
    have h0 := hKslice α u G hA
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    filter_upwards [h0] with z hz
    have hL1 : Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ) = fun θ => Lz u z θ := by
      funext θ
      rw [Lzero1_slice_eq]
    rw [hL1] at hz
    have hswap : (∫ θ in Iθ, Lz u z θ * u z θ * σw θ)
        = ∫ θ in Iθ, σw θ * (Lz u z θ * u z θ) :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hswap] at hz
    exact hz
  -- scalars
  set U : ℝ → ℝ := fun z => ∫ θ in Iθ, (u z θ) ^ 2 * σw θ with hUdef
  set UU : ℝ := ∫ z in Iz, phiW z * U z with hUUdef
  set GG : ℝ := ∫ z in Iz, phiW z * (∫ θ in Iθ, (G z θ) ^ 2 * σw θ) with hGGdef
  have hUnn : ∀ z, 0 ≤ U z := fun z => by rw [hUdef]; exact uMass_nonneg u z
  have hUint' : MeasureTheory.IntegrableOn (fun z => phiW z * U z) Iz := by
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
  -- ## (1) the source pairing
  have hB1 : ∀ n : ℕ, (∫ z in Iz, χ n z * phiW z *
      (∫ θ in Iθ, σw θ * (G z θ * u z θ))) ≤ (1 / 2) * (GG + UU) := by
    intro n
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
        |χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ))|
          ≤ (1 / 2) * (phiW z * (∫ θ in Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      have hτ := theta_pairing_le (f := fun θ => G z θ) (g := fun θ => u z θ)
        (hGslice z hz) (hUslice z hz)
      have hφ : 0 ≤ phiW z := phiW_nonneg z
      have hχ0 : 0 ≤ χ n z := (hχ01 n z).1
      have hχ1 : χ n z ≤ 1 := (hχ01 n z).2
      have hUeq : U z = ∫ θ in Iθ, (u z θ) ^ 2 * σw θ := by rw [hUdef]
      rw [abs_mul, abs_mul, abs_of_nonneg hφ, abs_of_nonneg hχ0, hUeq]
      calc χ n z * phiW z * |∫ θ in Iθ, σw θ * (G z θ * u z θ)|
          ≤ (1 * phiW z) * ((1 / 2) * ((∫ θ in Iθ, (G z θ) ^ 2 * σw θ)
              + (∫ θ in Iθ, (u z θ) ^ 2 * σw θ))) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hχ1 hφ) hτ
              (abs_nonneg _) (mul_nonneg zero_le_one hφ)
        _ = (1 / 2) * (phiW z * (∫ θ in Iθ, (G z θ) ^ 2 * σw θ)
              + phiW z * (∫ θ in Iθ, (u z θ) ^ 2 * σw θ)) := by ring
    have hmono : (∫ z in Iz, |χ n z * phiW z *
          (∫ θ in Iθ, σw θ * (G z θ * u z θ))|)
        ≤ ∫ z in Iz, (1 / 2) * (phiW z *
            (∫ θ in Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) := by
      have hsum : MeasureTheory.IntegrableOn (fun z => phiW z *
          (∫ θ in Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) Iz :=
        hGint.add hUint'
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => abs_nonneg _) (hsum.const_mul (1 / 2)) hpt
    have hval : (∫ z in Iz, (1 / 2) * (phiW z *
          (∫ θ in Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z))
        = (1 / 2) * (GG + UU) := by
      rw [zIntegral_const_mul (1 / 2), MeasureTheory.integral_add hGint hUint',
        hGGdef, hUUdef]
    have h1 : (∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ)))
        ≤ |∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ))| :=
      le_abs_self _
    have h2 : |∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ))|
        ≤ ∫ z in Iz, |χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ))| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm (fun z => χ n z * phiW z *
          (∫ θ in Iθ, σw θ * (G z θ * u z θ)))
    linarith [h1, h2, hmono, hval]
  -- ## (2) the angular self-form term
  have hB2 : ∀ n : ℕ, -(∫ z in Iz, χ n z * phiW z *
      (∫ θ in Iθ, σw θ * (Lz u z θ * u z θ))) ≤ K * UU := by
    intro n
    set σterm : ℝ → ℝ := fun z => ∫ θ in Iθ, σw θ * (Lz u z θ * u z θ) with hσterm
    by_cases hint : MeasureTheory.Integrable (fun z => χ n z * phiW z * σterm z)
        (MeasureTheory.volume.restrict Iz)
    · have hneg : MeasureTheory.Integrable
          (fun z => -(χ n z * phiW z * σterm z))
          (MeasureTheory.volume.restrict Iz) := hint.neg
      have hKint : MeasureTheory.Integrable
          (fun z => χ n z * phiW z * (K * U z))
          (MeasureTheory.volume.restrict Iz) := by
        have haesm : MeasureTheory.AEStronglyMeasurable
            (fun z => χ n z * phiW z * (K * U z))
            (MeasureTheory.volume.restrict Iz) := by
          have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => χ n z)
              (MeasureTheory.volume.restrict Iz) :=
            ((hχdiff n).continuous).aestronglyMeasurable
          have h2 : MeasureTheory.AEStronglyMeasurable phiW
              (MeasureTheory.volume.restrict Iz) := aestronglyMeasurable_phiW
          have h3 : MeasureTheory.AEStronglyMeasurable U
              (MeasureTheory.volume.restrict Iz) := by
            have hUU : AEMeasurable (fun z => phiW z * U z)
                (MeasureTheory.volume.restrict Iz) := hUint'.aemeasurable
            have hφm : AEMeasurable phiW (MeasureTheory.volume.restrict Iz) :=
              aemeasurable_phiW
            have hquot : AEMeasurable (fun z => (phiW z * U z) / phiW z)
                (MeasureTheory.volume.restrict Iz) := hUU.div hφm
            refine hquot.aestronglyMeasurable.congr ?_
            filter_upwards [ae_pos_of_mem_Iz] with z hz
            have hφz : phiW z ≠ 0 := by
              rw [phiW]
              exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (by linarith))
                (pow_ne_zero 2 hz.ne'))
            rw [mul_div_cancel_left₀ _ hφz]
          exact ((h1.mul h2).mul (h3.const_mul K))
        have hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
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
      have hmono : (∫ z in Iz, -(χ n z * phiW z * σterm z))
          ≤ ∫ z in Iz, χ n z * phiW z * (K * U z) := by
        refine MeasureTheory.integral_mono_ae hneg hKint ?_
        filter_upwards [hslice] with z hz
        have hφ : 0 ≤ phiW z := phiW_nonneg z
        have hχ0 : 0 ≤ χ n z := (hχ01 n z).1
        have hprod : 0 ≤ χ n z * phiW z := mul_nonneg hχ0 hφ
        have hz' : -σterm z ≤ K * U z := by
          have hσz : σterm z = ∫ θ in Iθ, σw θ * (Lz u z θ * u z θ) := by simp only [hσterm]
          rw [hσz, hUdef]
          linarith [hz]
        calc -(χ n z * phiW z * σterm z) = χ n z * phiW z * (-σterm z) := by ring
          _ ≤ χ n z * phiW z * (K * U z) := mul_le_mul_of_nonneg_left hz' hprod
      have hval : (∫ z in Iz, χ n z * phiW z * (K * U z)) ≤ K * UU := by
        have h1 : (∫ z in Iz, χ n z * phiW z * (K * U z))
            ≤ ∫ z in Iz, K * (phiW z * U z) := by
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
        have h2 : (∫ z in Iz, K * (phiW z * U z)) = K * UU := by
          rw [zIntegral_const_mul K (fun z => phiW z * U z), hUUdef]
        linarith [h1, h2]
      have h3 : -(∫ z in Iz, χ n z * phiW z * σterm z)
          = ∫ z in Iz, -(χ n z * phiW z * σterm z) := by
        rw [MeasureTheory.integral_neg]
      have hgoal : (∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (Lz u z θ * u z θ)))
          = ∫ z in Iz, χ n z * phiW z * σterm z := rfl
      rw [hgoal, h3]
      linarith [hmono, hval]
    · have hzero : (∫ z in Iz, χ n z * phiW z * σterm z) = 0 :=
        MeasureTheory.integral_undef hint
      have hpos : 0 ≤ K * UU := mul_nonneg (le_of_lt hKpos) hUUnn
      have hgoal : (∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (Lz u z θ * u z θ)))
          = ∫ z in Iz, χ n z * phiW z * σterm z := rfl
      rw [hgoal, hzero]; linarith [hpos]
  -- ## (3) the `(z²w²)''` term
  have hB3 : ∀ n : ℕ, (∫ z in Iz,
      deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z) ≤ C0 * UU := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
        |deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z| ≤ C0 * phiW z := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      exact hχbd1 n z hz
    have h := weighted_le_of_bound
      (c := fun z => deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z)
      (m := U) (C := C0) (le_of_lt hC0pos) hUint' hUnn hb
    have h2 : |∫ z in Iz,
        deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z| ≤ C0 * UU := by
      simpa only [hUUdef] using h
    linarith [le_abs_self (∫ z in Iz,
      deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z), h2]
  -- ## (4) the `(zw²)'` term
  have hB4 : ∀ n : ℕ, -(∫ z in Iz,
      deriv (fun z => χ n z * phiW z * z) z * U z) ≤ C0 * UU := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
        |deriv (fun z => χ n z * phiW z * z) z| ≤ C0 * phiW z := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      exact hχbd2 n z hz
    have h := weighted_le_of_bound (c := fun z => deriv (fun z => χ n z * phiW z * z) z)
      (m := U) (C := C0) (le_of_lt hC0pos) hUint' hUnn hb
    have h2 : |∫ z in Iz,
        deriv (fun z => χ n z * phiW z * z) z * U z| ≤ C0 * UU := by
      simpa only [hUUdef] using h
    linarith [neg_le_abs (∫ z in Iz,
      deriv (fun z => χ n z * phiW z * z) z * U z), h2]
  -- ## the truncated identity, from `sigTruncIdentD`
  have hsl : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0) := fun θ hθ =>
    Work.FTS.EllipticEst.Dispatch.slice_z_smooth_D hA hθ 2
  have hident : ∀ n : ℕ,
      (∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ)))
        = α ^ 2 * (∫ z in Iz, χ n z * phiW z * z ^ 2 *
              (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2))
          + (∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (Lz u z θ * u z θ)))
          - (α ^ 2 / 2) * (∫ z in Iz,
              deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z)
          + ((α * (5 + α)) / 2) * (∫ z in Iz,
              deriv (fun z => χ n z * phiW z * z) z * U z) := by
    intro n
    have hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
      Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
    have hUeq : ∀ z : ℝ, (∫ θ in Iθ, σw θ * (u z θ) ^ 2) = U z := by
      intro z
      rw [hUdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    obtain ⟨hJ1, hJ2, hJ3, hJ4, hJ5⟩ :=
      Work.FTS.EllipticEst.Dispatch.sigJointD hA hgrad (χ n) (hχdiff n)
        (fun z => (hχ01 n z).1) (fun z => (hχ01 n z).2)
        ⟨C0, le_of_lt hC0pos, fun z hz => by
          have h := (hC0 n z hz).2
          have hfun : Work.FTS.EllipticEst.Dispatch.om2 (χ n)
              = (fun z' => Work.FTS.EllipticEst.cut n z'
                  * (Work.Spaces.w z') ^ 2 * z' ^ 2) := by
            funext y
            simp only [Work.FTS.EllipticEst.Dispatch.om2, Work.FTS.EllipticEst.Dispatch.om,
              hχdef]
          rw [hfun]; exact h⟩
        ⟨C0, le_of_lt hC0pos, fun z hz => by
          have h := (hC0 n z hz).1
          have hfun : Work.FTS.EllipticEst.Dispatch.om1 (χ n)
              = (fun z' => Work.FTS.EllipticEst.cut n z'
                  * (Work.Spaces.w z') ^ 2 * z') := by
            funext y
            simp only [Work.FTS.EllipticEst.Dispatch.om1, Work.FTS.EllipticEst.Dispatch.om,
              hχdef]
          rw [hfun]; exact h⟩
    have hmain := Work.FTS.EllipticEst.Dispatch.sigTruncIdentD α u G (χ n)
      (hχdiff n) (hχcpt n) (hχ0 n) (Work.FTS.EllipticEst.H2W.Ae.AeData.eq hA)
      hJ1 hJ2 hJ3 hJ4 hJ5 hsl
    have h1 : (∫ z in Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
        (∫ θ in Iθ, σw θ * (G z θ * u z θ)))
        = ∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (G z θ * u z θ)) := by
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      simp only [Work.FTS.EllipticEst.Dispatch.om, phiW]
    have h2 : (∫ z in Iz, Work.FTS.EllipticEst.Dispatch.om2 (χ n) z *
        (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2))
        = ∫ z in Iz, χ n z * phiW z * z ^ 2 *
            (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      simp only [Work.FTS.EllipticEst.Dispatch.om2, Work.FTS.EllipticEst.Dispatch.om, phiW]
    have h3 : (∫ z in Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
        (∫ θ in Iθ, σw θ * (Lz u z θ * u z θ)))
        = ∫ z in Iz, χ n z * phiW z * (∫ θ in Iθ, σw θ * (Lz u z θ * u z θ)) := by
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      simp only [Work.FTS.EllipticEst.Dispatch.om, phiW]
    have h4f : Work.FTS.EllipticEst.Dispatch.om2 (χ n)
        = fun z => χ n z * phiW z * z ^ 2 := by
      funext y
      simp only [Work.FTS.EllipticEst.Dispatch.om2, Work.FTS.EllipticEst.Dispatch.om, phiW]
    have h5f : Work.FTS.EllipticEst.Dispatch.om1 (χ n)
        = fun z => χ n z * phiW z * z := by
      funext y
      simp only [Work.FTS.EllipticEst.Dispatch.om1, Work.FTS.EllipticEst.Dispatch.om, phiW]
    have h4 : (∫ z in Iz, deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
        (∫ θ in Iθ, σw θ * (u z θ) ^ 2))
        = ∫ z in Iz, deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z *
            (∫ θ in Iθ, σw θ * (u z θ) ^ 2) := by
      rw [h4f]
    have h5 : (∫ z in Iz, deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
        (∫ θ in Iθ, σw θ * (u z θ) ^ 2))
        = ∫ z in Iz, deriv (fun z => χ n z * phiW z * z) z *
            (∫ θ in Iθ, σw θ * (u z θ) ^ 2) := by
      rw [h5f]
    rw [h1, h2, h3, h4, h5] at hmain
    simp only [hUeq] at hmain
    exact hmain
  -- ## combining into a uniform bound
  have hkey : ∀ n : ℕ, α ^ 2 * (∫ z in Iz, χ n z * phiW z * z ^ 2 *
        (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2))
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
    have h3' : (α ^ 2 / 2) * (∫ z in Iz,
        deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z) ≤ (α ^ 2 / 2) * (C0 * UU) :=
      mul_le_mul_of_nonneg_left h3 hc1
    have h4' : ((α * (5 + α)) / 2) * (-(∫ z in Iz,
        deriv (fun z => χ n z * phiW z * z) z * U z)) ≤ ((α * (5 + α)) / 2) * (C0 * UU) :=
      mul_le_mul_of_nonneg_left h4 hc2
    linarith [hid, h1, h2, h3', h4']
  -- ## the identity of the limit with `HkSq α 0 (grad u)`
  have hXeq : ∫ z in Iz, phiW z * (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
    rw [HkSq_eq_weighted α (Work.FTS.EllipticEst.H2W.Ae.grad u)]
    refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.FTS.EllipticEst.H2W.Ae.grad]
    ring
  -- ## the limit of the truncated radial energy
  have hlim : Filter.Tendsto (fun n => α ^ 2 * (∫ z in Iz, χ n z * phiW z * z ^ 2 *
        (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2)))
      Filter.atTop
      (nhds (α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))) := by
    have hbase : Filter.Tendsto (fun n => ∫ z in Iz, χ n z * phiW z * z ^ 2 *
        (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2)) Filter.atTop
        (nhds (∫ z in Iz, phiW z *
          (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2))) := by
      have heq : ∀ n : ℕ, (∫ z in Iz, χ n z * phiW z * z ^ 2 *
            (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2))
          = ∫ z in Iz, χ n z * phiW z *
              (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2) := by
        intro n
        refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        rw [mul_assoc, mul_sq_slice]
      have h0 := tendsto_radial_energy α u hA.smooth hXint χ hχdiff hχ01 hχlim
      rw [show (fun n => ∫ z in Iz, χ n z * phiW z * z ^ 2 *
            (∫ θ in Iθ, σw θ * (Work.Spaces.pz u z θ) ^ 2))
          = (fun n => ∫ z in Iz, χ n z * phiW z *
              (∫ θ in Iθ, σw θ * (z * Work.Spaces.pz u z θ) ^ 2)) from
        funext fun n => heq n]
      exact h0
    rw [← hXeq]
    exact hbase.const_mul (α ^ 2)
  have hupper : α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
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
  have hC1 : (α ^ 2 / 2) * (C0 * Work.Spaces.HkSq α 0 u)
      ≤ (1 / 2) * (C0 * Work.Spaces.HkSq α 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hC0pos) hUnn'')
    nlinarith [hα0, hα4]
  have hC2 : ((α * (5 + α)) / 2) * (C0 * Work.Spaces.HkSq α 0 u)
      ≤ 1 * (C0 * Work.Spaces.HkSq α 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hC0pos) hUnn'')
    nlinarith [hα4, hα0]
  nlinarith [hupper, hC1, hC2, hGnn, hUnn'', hKpos, hC0pos, hα0]

end Work.FTS.EllipticEst.Prop
