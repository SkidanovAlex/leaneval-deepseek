import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `w²` is `C²` on `(0,∞)`. -/
theorem wsq_contDiffOn_two : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp [Work.Spaces.w]
  rw [hfun]
  refine ContDiffOn.pow (ContDiffOn.div ?_ ?_ ?_) 2
  · fun_prop
  · fun_prop
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

/-- `w²` is continuous on `(0,∞)`. -/
theorem wsq_continuousOn : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
  (wsq_contDiffOn_two).continuousOn

/-- **The `σ`-θ-weighted truncated radial energy identity** (the `G`-form of
`truncRadialIbpTheta`).  For data in the almost-everywhere class, a `C²` cut-off `χ` supported in
`[a,b] ⊂ (0,∞)` with `0 ≤ χ ≤ 1`, and with `ω = χ·w²`,

`∫_z ω ∫_θ σ (G·u) = α²∫_z ω ∫_θ σ (z∂_zu)² + ∫_z ω ∫_θ σ ((Lzero u)·u)
   - (α²/2)∫_z (z²ω)'' ∫_θ σ u² + ((α(5+α))/2)∫_z (zω)' ∫_θ σ u²`,

`σ = sin(2θ)^{-η}`.  This is `truncRadialIbpTheta` combined with the equation
`bslOp α u = -(α²z²)∂_zzu - α(5+α)z∂_zu + Lzero u = G` on the open quadrant. -/
theorem aeTruncSigmaIdD (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (χ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hχ : ContDiff ℝ 2 χ)
    (hχsupp : ∀ z, z ∉ Set.Icc a b → χ z = 0)
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) :
    (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * Work.FTS.EllipticEst.sEta θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ))
        + (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ
                * Work.FTS.EllipticEst.sEta θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hUsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
  have hGsm : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hUsm)
      (fun z θ hz hθ1 hθ2 => hA.eq z hz θ hθ1 hθ2)
  -- the weight `ω = χ w²`
  have hωd : ContDiffOn ℝ 2 (fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (hχ.contDiffOn).mul wsq_contDiffOn_two
  have hωsupp : ∀ z, z ∉ Set.Icc a b → χ z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz
    rw [hχsupp z hz, zero_mul]
  have hωbdd : ∀ z, |χ z * (Work.Spaces.w z) ^ 2| ≤ (Work.Spaces.w z) ^ 2 := by
    intro z
    rw [abs_mul, abs_of_nonneg (hχ01 z).1, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
    calc χ z * (Work.Spaces.w z) ^ 2 ≤ 1 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hχ01 z).2 (sq_nonneg _)
      _ = (Work.Spaces.w z) ^ 2 := by ring
  -- the pointwise (a.e. on the quadrant) split `G u = (Lzero u) u - P u`
  have hsplit_pt : ∀ᵐ p ∂nuFts, G p.1 p.2 * u p.1 p.2
      = Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2
        - ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2) := by
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have heq := hA.eq p.1 hp1 p.2 hp2.1 hp2.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hG : G p.1 p.2 = Work.Elliptic.Lzero u p.1 p.2
        - (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) := by linarith [heq]
    rw [hG]; ring
  -- the three joint integrands (`nuFts`-integrable)
  have hIP : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
        + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts :=
    (tRibp_integrablePair (α := α) (u := u) (fun z => χ z * (Work.Spaces.w z) ^ 2) ha hab
      hA.smooth hgrad hA.memRad2 hu hωd hωsupp hωbdd).1
  have hIcont : ContinuousOn (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) (tRibp_continuousOn_sEta.mul
      (hGsm.continuousOn.mul hUsm.continuousOn))
    · exact (hχ.continuous).continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · exact wsq_continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hIG : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 G p.1 p.2) nuFts :=
    integrable_HkIntegrand_of_smoothOpen hGsm hA.memG
  have hIU : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 u p.1 p.2) nuFts :=
    integrable_HkIntegrand_of_smoothOpen hUsm hu
  have hIGU : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2))) nuFts := by
    refine ((hIG.add hIU).const_mul (1 / 2)).mono'
      (aesm_prod_of_continuousOn_Q0 hIcont) ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hσ : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    obtain ⟨z, θ⟩ := p
    have h1 : |χ z * (Work.Spaces.w z) ^ 2| ≤ (Work.Spaces.w z) ^ 2 := hωbdd z
    have h2 : |Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)|
        ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
      have h3 : |G z θ * u z θ| ≤ (1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) := by
        have h := abs_mul (G z θ) (u z θ)
        nlinarith [sq_nonneg (|G z θ| - |u z θ|), sq_abs (G z θ), sq_abs (u z θ), h]
      rw [abs_mul, abs_of_nonneg hσ]
      calc Work.FTS.EllipticEst.sEta θ * |G z θ * u z θ|
          ≤ Work.FTS.EllipticEst.sEta θ * ((1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 hσ
        _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |χ z * (Work.Spaces.w z) ^ 2| *
          |Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)|
        ≤ (Work.Spaces.w z) ^ 2 * ((1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (sq_nonneg _)
      _ = 1 / 2 * (Work.Spaces.HkIntegrand α 0 G z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) := by
          rw [HkIntegrand_zero_D α G hθ, HkIntegrand_zero_D α u hθ]; ring
  -- `fL = fG + fP` a.e.
  have hIL : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) nuFts := by
    refine (hIGU.add hIP).congr ?_
    filter_upwards [hsplit_pt] with p hp
    simp only [Pi.add_apply]
    rw [hp]
    ring
  -- the split at the level of the double integral
  have hsplit_double : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)) ∂nuFts)
      = (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
          (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)) ∂nuFts)
        - (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
          (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)) ∂nuFts) := by
    have h1 : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
          (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)) ∂nuFts)
        = ∫ p, (χ p.1 * (Work.Spaces.w p.1) ^ 2 *
              (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))
            - χ p.1 * (Work.Spaces.w p.1) ^ 2 *
              (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2
                * Work.Spaces.pzIter 2 u p.1 p.2
                + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) ∂nuFts := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hsplit_pt] with p hp
      rw [hp]; ring
    rw [h1, MeasureTheory.integral_sub hIL hIP]
  -- the iterated form of each double integral
  have hnuG : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)) ∂nuFts)
      = ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)) := by
    rw [show nuFts = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl]
    rw [MeasureTheory.integral_prod _ hIGU]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          χ z * (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)) from by
      funext z
      exact MeasureTheory.integral_const_mul _ _]
  have hnuL : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)) ∂nuFts)
      = ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)) := by
    rw [show nuFts = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl]
    rw [MeasureTheory.integral_prod _ hIL]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          χ z * (Work.Spaces.w z) ^ 2
            * (Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)) from by
      funext z
      exact MeasureTheory.integral_const_mul _ _]
  have hnuP : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)) ∂nuFts)
      = ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)) := by
    rw [show nuFts = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl]
    rw [MeasureTheory.integral_prod _ hIP]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          χ z * (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
            ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)) from by
      funext z
      exact MeasureTheory.integral_const_mul _ _]
  -- the `z`-level identity in `Ioi 0` form
  have hIbp := truncRadialIbpTheta (α := α) (u := u) (fun z => χ z * (Work.Spaces.w z) ^ 2)
    ha hab hA.smooth hgrad hA.memRad2 hu hωd hωsupp hωbdd
  have hmain : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
      = α ^ 2 * (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun y : ℝ => y ^ 2 * (χ y * (Work.Spaces.w y) ^ 2))) z *
              (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun y : ℝ => y * (χ y * (Work.Spaces.w y) ^ 2)) z *
              (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
    rw [← hnuG, hsplit_double, hnuL, hnuP, hIbp]
    ring
  -- transport `Ioi 0` to `Iz` and rewrite the weight
  have hIoi : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi2 : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi3 : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ
              * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi4 : (∫ z in Set.Ioi 0,
        deriv (deriv (fun y : ℝ => y ^ 2 * (χ y * (Work.Spaces.w y) ^ 2))) z *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    have hfun : (fun y : ℝ => y ^ 2 * (χ y * (Work.Spaces.w y) ^ 2))
        = fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2 := by
      funext y; ring
    rw [hfun]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi5 : (∫ z in Set.Ioi 0,
        deriv (fun y : ℝ => y * (χ y * (Work.Spaces.w y) ^ 2)) z *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz,
          deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z) z
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    have hfun : (fun y : ℝ => y * (χ y * (Work.Spaces.w y) ^ 2))
        = fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y := by
      funext y; ring
    rw [hfun]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  rw [hIoi, hIoi2, hIoi3, hIoi4, hIoi5] at hmain
  exact hmain

/-- **Joint integrability of the `σ`-weighted `Lzero`-pairing** against a compactly supported
radial weight `χ·w²`: needed to justify the linearity of the truncated `σ`-energy identity. -/
theorem integrable_lzeroL2_joint (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (χ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hχ : ContDiff ℝ 2 χ)
    (hχsupp : ∀ z, z ∉ Set.Icc a b → χ z = 0)
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) nuFts := by
  have hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hUsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
  have hGsm : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hUsm)
      (fun z θ hz hθ1 hθ2 => hA.eq z hz θ hθ1 hθ2)
  -- the weight `ω = χ w²`
  have hωd : ContDiffOn ℝ 2 (fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (hχ.contDiffOn).mul wsq_contDiffOn_two
  have hωsupp : ∀ z, z ∉ Set.Icc a b → χ z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz
    rw [hχsupp z hz, zero_mul]
  have hωbdd : ∀ z, |χ z * (Work.Spaces.w z) ^ 2| ≤ (Work.Spaces.w z) ^ 2 := by
    intro z
    rw [abs_mul, abs_of_nonneg (hχ01 z).1, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
    calc χ z * (Work.Spaces.w z) ^ 2 ≤ 1 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hχ01 z).2 (sq_nonneg _)
      _ = (Work.Spaces.w z) ^ 2 := by ring
  -- the pointwise (a.e. on the quadrant) split `G u = (Lzero u) u - P u`
  have hsplit_pt : ∀ᵐ p ∂nuFts, G p.1 p.2 * u p.1 p.2
      = Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2
        - ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2) := by
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have heq := hA.eq p.1 hp1 p.2 hp2.1 hp2.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hG : G p.1 p.2 = Work.Elliptic.Lzero u p.1 p.2
        - (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) := by linarith [heq]
    rw [hG]; ring
  -- the three joint integrands (`nuFts`-integrable)
  have hIP : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
        + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts :=
    (tRibp_integrablePair (α := α) (u := u) (fun z => χ z * (Work.Spaces.w z) ^ 2) ha hab
      hA.smooth hgrad hA.memRad2 hu hωd hωsupp hωbdd).1
  have hIcont : ContinuousOn (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) (tRibp_continuousOn_sEta.mul
      (hGsm.continuousOn.mul hUsm.continuousOn))
    · exact (hχ.continuous).continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · exact wsq_continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hIG : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 G p.1 p.2) nuFts :=
    integrable_HkIntegrand_of_smoothOpen hGsm hA.memG
  have hIU : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 u p.1 p.2) nuFts :=
    integrable_HkIntegrand_of_smoothOpen hUsm hu
  have hIGU : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2))) nuFts := by
    refine ((hIG.add hIU).const_mul (1 / 2)).mono'
      (aesm_prod_of_continuousOn_Q0 hIcont) ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hσ : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    obtain ⟨z, θ⟩ := p
    have h1 : |χ z * (Work.Spaces.w z) ^ 2| ≤ (Work.Spaces.w z) ^ 2 := hωbdd z
    have h2 : |Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)|
        ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
      have h3 : |G z θ * u z θ| ≤ (1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) := by
        have h := abs_mul (G z θ) (u z θ)
        nlinarith [sq_nonneg (|G z θ| - |u z θ|), sq_abs (G z θ), sq_abs (u z θ), h]
      rw [abs_mul, abs_of_nonneg hσ]
      calc Work.FTS.EllipticEst.sEta θ * |G z θ * u z θ|
          ≤ Work.FTS.EllipticEst.sEta θ * ((1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 hσ
        _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |χ z * (Work.Spaces.w z) ^ 2| *
          |Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)|
        ≤ (Work.Spaces.w z) ^ 2 * ((1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (sq_nonneg _)
      _ = 1 / 2 * (Work.Spaces.HkIntegrand α 0 G z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) := by
          rw [HkIntegrand_zero_D α G hθ, HkIntegrand_zero_D α u hθ]; ring
  -- `fL = fG + fP` a.e.
  have hIL : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) nuFts := by
    refine (hIGU.add hIP).congr ?_
    filter_upwards [hsplit_pt] with p hp
    simp only [Pi.add_apply]
    rw [hp]
    ring
  exact hIL

end Work.FTS.EllipticEst.Dispatch
