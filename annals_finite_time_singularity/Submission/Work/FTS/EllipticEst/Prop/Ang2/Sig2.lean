import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.sigJointD =====
section

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
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # Joint integrability of the `σ`-weighted truncated integrands (general weight `om`)

This module proves `Work.FTS.EllipticEst.Dispatch.sigJointD`: for a datum `AeData α u G` of the
almost-everywhere class, for `z ∂_z u ∈ ℋ⁰`, and for a `C²` weight `W` with `0 ≤ W ≤ 1` whose
associated weights `om W = W w²`, `om2 W = W w² z²`, `om1 W = W w² z` have bounded second
(resp. first) `z`-derivative against `w²`, the five integrands of the `σ`-weighted truncated
energy identity are jointly integrable against `dz dθ |_{[0,∞) × Iθ}`:

* `om W · σ · (bslOp α u · u)`;
* `σ · (om W · (z ∂_z u)²)`;
* `σ · ((om2 W)'' · u²)`;
* `σ · ((om1 W)' · u²)`;
* `om W · σ · (Lzero u · u)`.

The measure `msig` of the `σ`-weighted analysis differs from the measure `nuFts` of the sibling
`aeJointIntegrableF` only by the null set `{z = 0}`, so the joint-integrability machinery of that
module (`ℋ⁰`-integrand integrability, a.e. strong measurability from continuity on the open
quadrant) is reused verbatim. -/

/-! ## The two product measures coincide -/

/-- `msig` (the restriction of `dz dθ` to `[0,∞) × [0,π/2]`) and `nuFts` (the restriction to
`(0,∞) × [0,π/2]`) differ only by the null set `{z = 0}`. -/
theorem msig_eq_nuFts : msig = nuFts := by
  have h : (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)) : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  show (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [h]

/-! ## Continuity on the open quadrant of the weights -/

/-- `σ = sin(2θ)^{-η}` is continuous on the open quadrant, as a function of the second
variable. -/
theorem continuousOn_sEta_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) Q0 := by
  have hsm : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos hθ)))
  exact h1.comp continuous_snd.continuousOn (fun p hp => hp.2)

/-- `om W = W · w²` is continuous on `(0,∞)` when `W` is `C²`. -/
theorem continuousOn_om {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContinuousOn (om W) (Set.Ioi 0) :=
  (contDiffOn_two_Wcut hW).continuousOn

/-- `om2 W = W · w² · z² = W · (1+z)⁴/z²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_two_om2 {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContDiffOn ℝ 2 (om2 W) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) :=
    (contDiff_const.add contDiff_id).pow 4 |>.contDiffOn
  have hden : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi 0) :=
    (contDiff_id.pow 2).contDiffOn
  have hratio : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 4 / z ^ 2) (Set.Ioi 0) :=
    hnum.div hden (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => W z * ((1 + z) ^ 4 / z ^ 2)) (Set.Ioi 0) :=
    hW.contDiffOn.mul hratio
  refine h1.congr (fun z hz => ?_)
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp only [om2, om, Work.Spaces.w]
  field_simp

/-- `om1 W = W · w² · z = W · (1+z)⁴/z³` is `C²` on `(0,∞)`. -/
theorem contDiffOn_two_om1 {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContDiffOn ℝ 2 (om1 W) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) :=
    (contDiff_const.add contDiff_id).pow 4 |>.contDiffOn
  have hden : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 3) (Set.Ioi 0) :=
    (contDiff_id.pow 3).contDiffOn
  have hratio : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 4 / z ^ 3) (Set.Ioi 0) :=
    hnum.div hden (fun z hz => pow_ne_zero 3 (ne_of_gt hz))
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => W z * ((1 + z) ^ 4 / z ^ 3)) (Set.Ioi 0) :=
    hW.contDiffOn.mul hratio
  refine h1.congr (fun z hz => ?_)
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp only [om1, om, Work.Spaces.w]
  field_simp

/-- The second derivative of `om2 W` is continuous on `(0,∞)`. -/
theorem continuousOn_deriv_deriv_om2 {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContinuousOn (fun z : ℝ => deriv (deriv (om2 W)) z) (Set.Ioi 0) :=
  (((contDiffOn_two_om2 hW).deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).deriv_of_isOpen
    (m := 0) isOpen_Ioi (by norm_num)).continuousOn

/-- The first derivative of `om1 W` is continuous on `(0,∞)`. -/
theorem continuousOn_deriv_om1 {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContinuousOn (fun z : ℝ => deriv (om1 W) z) (Set.Ioi 0) :=
  ((contDiffOn_two_om1 hW).deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn

theorem continuousOn_om_fst {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContinuousOn (fun p : ℝ × ℝ => om W p.1) Q0 :=
  (continuousOn_om hW).comp continuous_fst.continuousOn (fun p hp => hp.1)

theorem continuousOn_deriv_deriv_om2_fst {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (om2 W)) p.1) Q0 :=
  (continuousOn_deriv_deriv_om2 hW).comp continuous_fst.continuousOn (fun p hp => hp.1)

theorem continuousOn_deriv_om1_fst {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (om1 W) p.1) Q0 :=
  (continuousOn_deriv_om1 hW).comp continuous_fst.continuousOn (fun p hp => hp.1)

/-! ## a.e. strong measurability of the two shapes of integrand -/

/-- a.e. strong measurability of `A(z) · σ(θ) · (F · H)`. -/
theorem aesm_sigma_pair {F H : ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1) Q0)
    (hF : ContinuousOn F Q0) (hH : ContinuousOn H Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => A p.1 * (Work.FTS.EllipticEst.sEta p.2 * (F p * H p))) nuFts :=
  aesm_prod_of_continuousOn_Q0 (hA.mul (continuousOn_sEta_snd.mul (hF.mul hH)))

/-- a.e. strong measurability of `σ(θ) · (A(z) · F²)`. -/
theorem aesm_sigma_sq {F : ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1) Q0)
    (hF : ContinuousOn F Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 * (A p.1 * (F p) ^ 2)) nuFts :=
  aesm_prod_of_continuousOn_Q0 (continuousOn_sEta_snd.mul (hA.mul (hF.pow 2)))

/-! ## The two domination lemmas -/

/-- **The `σ`-weighted pairing `A(z) · σ(θ) · f · g` is jointly integrable** as soon as
`|A z| ≤ C · w(z)²` on `(0,∞)` and the `ℋ⁰`-integrands of `f` and `g` are: the pointwise
estimate `|A| σ |f g| ≤ C w² σ (f²+g²)/2 = C (HkIntegrand f + HkIntegrand g)/2`. -/
theorem integrable_sigma_pair_of_HkIntegrable {α C : ℝ} {f g : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hC : 0 ≤ C) (hA : ∀ z, 0 < z → |A z| ≤ C * (Work.Spaces.w z) ^ 2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => A p.1 * (Work.FTS.EllipticEst.sEta p.2 * (f p.1 p.2 * g p.1 p.2)))
      nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts)
    (hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) nuFts) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A p.1 * (Work.FTS.EllipticEst.sEta p.2 * (f p.1 p.2 * g p.1 p.2)))
      nuFts := by
  refine ((hf.add hg).const_mul C).mono' haesm ?_
  filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hz hθ
  obtain ⟨z, θ⟩ := p
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσnn : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ_D hθI
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hHf : Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    HkIntegrand_zero_D α f hθI
  have hHg : Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    HkIntegrand_zero_D α g hθI
  have hfg : |f z θ| * |g z θ| ≤ ((f z θ) ^ 2 + (g z θ) ^ 2) / 2 := by
    have hh : 0 ≤ (|f z θ| - |g z θ|) ^ 2 := sq_nonneg _
    rw [sub_sq, sq_abs, sq_abs] at hh
    linarith
  have hnorm : ‖A z * (Work.FTS.EllipticEst.sEta θ * (f z θ * g z θ))‖
      = |A z| * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) := by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσnn]
  have h1 : 0 ≤ Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|) :=
    mul_nonneg hσnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hw1 : 0 ≤ (Work.Spaces.w z) ^ 2
      * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) := mul_nonneg hw2 h1
  have e1 : 0 ≤ (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    mul_nonneg hw2 (mul_nonneg (sq_nonneg _) hσnn)
  have e2 : 0 ≤ (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    mul_nonneg hw2 (mul_nonneg (sq_nonneg _) hσnn)
  calc ‖A z * (Work.FTS.EllipticEst.sEta θ * (f z θ * g z θ))‖
      = |A z| * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) := hnorm
    _ ≤ (C * (Work.Spaces.w z) ^ 2)
          * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) :=
        mul_le_mul_of_nonneg_right (hA z hz) h1
    _ = C * ((Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|))) := by ring
    _ ≤ C * ((Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.sEta θ * (((f z θ) ^ 2 + (g z θ) ^ 2) / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine mul_le_mul_of_nonneg_left ?_ hw2
        exact mul_le_mul_of_nonneg_left hfg hσnn
    _ ≤ C * (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [hHf, hHg]
        nlinarith [e1, e2]

/-- **The `σ`-weighted square `σ(θ) · A(z) · f²` is jointly integrable** as soon as
`|A z| ≤ C · w(z)²` on `(0,∞)` and the `ℋ⁰`-integrand of `f` is. -/
theorem integrable_sigma_sq_of_HkIntegrable {α C : ℝ} {f : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hC : 0 ≤ C) (hA : ∀ z, 0 < z → |A z| ≤ C * (Work.Spaces.w z) ^ 2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 * (A p.1 * (f p.1 p.2) ^ 2)) nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 * (A p.1 * (f p.1 p.2) ^ 2)) nuFts := by
  refine (hf.const_mul C).mono' haesm ?_
  filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hz hθ
  obtain ⟨z, θ⟩ := p
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσnn : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ_D hθI
  have hHf : Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    HkIntegrand_zero_D α f hθI
  have hnorm : ‖Work.FTS.EllipticEst.sEta θ * (A z * (f z θ) ^ 2)‖
      = Work.FTS.EllipticEst.sEta θ * (|A z| * (f z θ) ^ 2) := by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσnn, abs_of_nonneg (sq_nonneg (f z θ))]
  calc ‖Work.FTS.EllipticEst.sEta θ * (A z * (f z θ) ^ 2)‖
      = Work.FTS.EllipticEst.sEta θ * (|A z| * (f z θ) ^ 2) := hnorm
    _ ≤ Work.FTS.EllipticEst.sEta θ * ((C * (Work.Spaces.w z) ^ 2) * (f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hA z hz) (sq_nonneg _)) hσnn
    _ = C * Work.Spaces.HkIntegrand α 0 f z θ := by
        rw [hHf]; ring

/-! ## The main theorem -/

theorem sigJointD {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hWnn : ∀ z, 0 ≤ W z) (hWle : ∀ z, W z ≤ 1)
    (hD2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, 0 < z →
      |deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 W)) z|
        ≤ C * (Work.Spaces.w z) ^ 2)
    (hD1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, 0 < z →
      |deriv (Work.FTS.EllipticEst.Dispatch.om1 W) z|
        ≤ C * (Work.Spaces.w z) ^ 2) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Dispatch.om W p.1 *
        (Work.FTS.EllipticEst.sEta p.2 *
          (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2)))
        Work.FTS.EllipticEst.Dispatch.msig
      ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
          (Work.FTS.EllipticEst.Dispatch.om W p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2))
        Work.FTS.EllipticEst.Dispatch.msig
      ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
          (deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 W)) p.1 * (u p.1 p.2) ^ 2))
        Work.FTS.EllipticEst.Dispatch.msig
      ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
          (deriv (Work.FTS.EllipticEst.Dispatch.om1 W) p.1 * (u p.1 p.2) ^ 2))
        Work.FTS.EllipticEst.Dispatch.msig
      ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Dispatch.om W p.1 *
          (Work.FTS.EllipticEst.sEta p.2 *
            (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)))
        Work.FTS.EllipticEst.Dispatch.msig := by
  -- ## smoothness of the data on the open quadrant
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hU)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  have hD : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) := hU.Dz
  -- ## the `ℋ⁰`-memberships
  have hmu : Work.Spaces.HkMem α 0 u := hkMem_uM α u G h
  have hmg : Work.Spaces.HkMem α 0 G := h.memG
  have hma : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := h.memRad2
  have hmd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := hgrad
  -- ## joint integrability of the `ℋ⁰`-integrands
  have hIu := integrable_HkIntegrand_of_smoothOpen hU hmu
  have hIg := integrable_HkIntegrand_of_smoothOpen hG hmg
  have hIa := integrable_HkIntegrand_of_smoothOpen hA hma
  have hId := integrable_HkIntegrand_of_smoothOpen hD hmd
  -- ## the weight bound `|om W z| ≤ w(z)²`
  have hOmb : ∀ z, 0 < z → |om W z| ≤ 1 * (Work.Spaces.w z) ^ 2 := by
    intro z _
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hom0 : 0 ≤ om W z := mul_nonneg (hWnn z) hw2
    rw [abs_of_nonneg hom0, one_mul]
    show W z * (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.w z) ^ 2
    calc W z * (Work.Spaces.w z) ^ 2 ≤ 1 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hWle z) hw2
      _ = (Work.Spaces.w z) ^ 2 := one_mul _
  obtain ⟨C2, hC2nn, hC2⟩ := hD2
  obtain ⟨C1, hC1nn, hC1⟩ := hD1
  -- ## 1. the source pairing `om W · σ · (bslOp α u · u)`
  have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (Work.FTS.EllipticEst.sEta p.2 *
        (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))) msig := by
    rw [msig_eq_nuFts]
    have hb := integrable_sigma_pair_of_HkIntegrable (α := α) (C := 1) (A := om W) (f := G)
      (g := u) zero_le_one hOmb
      (aesm_sigma_pair (continuousOn_om_fst hW2) hG.continuousOn hU.continuousOn) hIg hIu
    refine hb.congr ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hz hθ
    obtain ⟨z, θ⟩ := p
    show om W z * (Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
        = om W z * (Work.FTS.EllipticEst.sEta θ
            * (Work.Elliptic.bslOp α u z θ * u z θ))
    rw [h.eq z hz θ hθ.1 hθ.2]
  -- ## 2. the radial first-derivative square `σ · (om W · (z ∂_z u)²)`
  have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
      (om W p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) msig := by
    rw [msig_eq_nuFts]
    refine integrable_sigma_sq_of_HkIntegrable (α := α) (C := 1) (A := om W)
      (f := Work.FTS.EllipticEst.H2W.Ae.grad u) zero_le_one hOmb
      (aesm_sigma_sq (continuousOn_om_fst hW2) hD.continuousOn) hId
  -- ## 3. the second `z`-derivative of the weight, paired with `u²`
  have h3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
      (deriv (deriv (om2 W)) p.1 * (u p.1 p.2) ^ 2)) msig := by
    rw [msig_eq_nuFts]
    refine integrable_sigma_sq_of_HkIntegrable (α := α) (C := C2)
      (A := fun z => deriv (deriv (om2 W)) z) (f := u) hC2nn hC2
      (aesm_sigma_sq (continuousOn_deriv_deriv_om2_fst hW2) hU.continuousOn) hIu
  -- ## 4. the first `z`-derivative of the weight, paired with `u²`
  have h4 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
      (deriv (om1 W) p.1 * (u p.1 p.2) ^ 2)) msig := by
    rw [msig_eq_nuFts]
    refine integrable_sigma_sq_of_HkIntegrable (α := α) (C := C1)
      (A := fun z => deriv (om1 W) z) (f := u) hC1nn hC1
      (aesm_sigma_sq (continuousOn_deriv_om1_fst hW2) hU.continuousOn) hIu
  -- ## 5. the `Lzero` pairing, expanded along the equation `bslOp α u = G`
  have h5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (Work.FTS.EllipticEst.sEta p.2 *
        (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig := by
    rw [msig_eq_nuFts]
    have hb1 := integrable_sigma_pair_of_HkIntegrable (α := α) (C := 1) (A := om W) (f := G)
      (g := u) zero_le_one hOmb
      (aesm_sigma_pair (continuousOn_om_fst hW2) hG.continuousOn hU.continuousOn) hIg hIu
    have hb2 := integrable_sigma_pair_of_HkIntegrable (α := α) (C := 1) (A := om W)
      (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (g := u) zero_le_one hOmb
      (aesm_sigma_pair (continuousOn_om_fst hW2) hA.continuousOn hU.continuousOn) hIa hIu
    have hb3 := integrable_sigma_pair_of_HkIntegrable (α := α) (C := 1) (A := om W)
      (f := Work.FTS.EllipticEst.H2W.Ae.grad u) (g := u) zero_le_one hOmb
      (aesm_sigma_pair (continuousOn_om_fst hW2) hD.continuousOn hU.continuousOn) hId hIu
    have hsum := (hb1.add (hb2.const_mul (α ^ 2))).add (hb3.const_mul (α * (5 + α)))
    refine hsum.congr ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hz hθ
    obtain ⟨z, θ⟩ := p
    have heq := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hLz : Work.Elliptic.Lzero u z θ
        = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ) := by linarith
    show om W z * (Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
        + α ^ 2 * (om W z * (Work.FTS.EllipticEst.sEta θ
            * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)))
        + α * (5 + α) * (om W z * (Work.FTS.EllipticEst.sEta θ
            * ((z * Work.Spaces.pz u z θ) * u z θ)))
      = om W z * (Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ))
    rw [hLz]
    ring
  exact ⟨h1, h2, h3, h4, h5⟩

end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Ang2.Sig2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeStepOneAux/aeDzNormSig` — the `σ`-weighted first-order radial bound from `SigmaCoercive`

For data in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData α u G` with
`HkMem α 0 (z∂_zu)` and the a.e. vanishing of the slices at `θ = 0⁺`, and with the
`σ`-coercivity `SigmaCoercive` of the angular operator `Lzero1` available as a hypothesis,

  `α · nrm α (grad u) ≤ C(M) · nrm α G`   whenever `nrm α u ≤ M · nrm α G`,

where `nrm α f = √(HkSq α 0 f)`, `grad u = z ∂_zu`, `σ θ = sin(2θ)^{-η}` and
`HkSq α 0 f = ∫_z (w z)² ∫_θ f² σ`, `w z = (1+z)²/z²`.

## Route

Write `ρ = w²σ`, `Du = z∂_zu`, and truncate radially by a smooth cut-off `χ n`
(`Work.FTS.EllipticEst.Mine.zcutFam`: `χ n = 0` near `0` and for `z ≥ 2(n+1)`, `= 1` on
`[2/(n+1), n+1]`, with `|z χ n'| ≤ C₁` and `|z(z χ n')'| ≤ C₂` *uniformly in* `n`), setting
`ω z = (w z)² χ n z`.

* `truncRadialIbpSigma` (the compactly supported per-`θ` radial IBP
  `Work.FTS.EllipticEst.Honest.zIBP_compact`, integrated in `θ` against `σ`) gives
  `∫_z ω ∫_θ σ (Pu)u = -α²∫_z ω∫_θ σ (Du)² + (α²/2)∫_z (z²ω)''∫_θ σ u²
     - (α(5+α)/2)∫_z (zω)'∫_θ σ u²`, where `Pu = α²z²∂_zzu + α(5+α)z∂_zu`.
* On the open quadrant `Lzero u = G + Pu`, so `∫_zω∫_θσ(Pu)u = ∫_zω∫_θσ(Lzero u)u - ∫_zω∫_θσGu`.
* The slicewise `σ`-coercivity (`sliceCoerciveAe`, from `SigmaCoercive`) bounds the first term
  from below by `-K∫_z ω∫_θ σ u²`; the source pairing is bounded by AM–GM; the transfer terms by
  `Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds`.  All of it is `≤ C(M) HkSq α 0 G`, using
  `nrm α u ≤ M nrm α G` and `HkMem α 0 u` (`Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU`).
* Letting `n → ∞` (`χ n ↑ 1` with `|χ n| ≤ 1`, dominated convergence) gives
  `α² HkSq α 0 (grad u) ≤ C(M)² HkSq α 0 G`, and taking square roots the claim.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeStepOneAux.Sig2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `σ`-weighted truncated radial integration by parts

This is the (previously missing) leaf of the argument below.  Its *equation* conjunct is the
proved `Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta` (`|ω| ≤ w²` in place of
`0 ≤ ω ≤ w²`), and the `IntegrableOn` conjunct is the `z`-integral of the joint integrability
proved there (`Dispatch.tRibp_integrablePair` + `Integrable.integral_prod_left`).  -/


/-! ## Elementary facts about the radial weight `φ z = w z ^ 2` -/

/-- The square of the radial weight is nonnegative. -/
theorem w_sq_nonneg (z : ℝ) : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _

/-- On the open half-line the square of the radial weight is positive: `w z = (1+z)²/z²`. -/
theorem w_sq_pos {z : ℝ} (hz : 0 < z) : 0 < (Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.w]
  exact pow_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)) 2

/-- The set integrals over `Ioi 0` and over `Iz = [0,∞)` agree (they differ by `{0}`). -/
theorem setIntegral_Ioi_eq_Iz (f : ℝ → ℝ) :
    (∫ z in Set.Ioi 0, f z) = ∫ z in Work.Spaces.Iz, f z := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.setIntegral_congr_set (f := f)
    (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))

/-- `HkSq α 0` in the `w²σ`-weighted form. -/
theorem HkSq_zero_eq_phi_mul (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z

/-- The outer `w²`-weighted slice integral of an `ℋ⁰`-element is integrable. -/
theorem integrableOn_phi_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz :=
  hf.2.congr_fun
    (fun z _ => Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z)
    measurableSet_Ici

/-! ## Measurability of the slice integrals -/

/-- The square of the radial weight is measurable. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

theorem measurable_w_sq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  unfold Work.Spaces.w
  fun_prop

/-- `AEStronglyMeasurable` of a function whose `w²`-weighted version is `AEStronglyMeasurable`
(the weight is nonvanishing on `(0,∞)`). -/
theorem aesm_div_phi {A : ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * A z)
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hdiv : AEMeasurable
      (fun z => ((Work.Spaces.w z) ^ 2 * A z) / ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    h.aemeasurable.div measurable_w_sq.aemeasurable
  refine (aestronglyMeasurable_iff_aemeasurable.mpr hdiv).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  have hne : (Work.Spaces.w z) ^ 2 ≠ 0 := ne_of_gt (w_sq_pos hz)
  exact mul_div_cancel_left₀ (A z) hne

/-- Restricting an `AEStronglyMeasurable` function from `Iz = [0,∞)` to `(0,∞)`. -/
theorem aesm_restrict_Ioi_of_Iz {g : ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).restrict (Set.Ioi 0)) := h.restrict
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iz).restrict (Set.Ioi 0)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.1, fun h => ⟨h, le_of_lt h⟩⟩
  rwa [h2] at h1

/-- The `w²`-weighted slice integral of an `ℋ⁰`-element is `AEStronglyMeasurable`. -/
theorem aesm_phi_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (aesm_restrict_Ioi_of_Iz hf.2.aestronglyMeasurable).congr
    (Filter.Eventually.of_forall fun z =>
      Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z)

/-- The slice integral `z ↦ ∫_θ f² σ` of an `ℋ⁰`-element is `AEStronglyMeasurable`. -/
theorem aesm_slice_sq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  aesm_div_phi (aesm_phi_mul_slice hf)

/-! ## Domination of truncated pairings -/

/-- **Domination of a truncated pairing by the `w²`-weighted one.**  If `0 ≤ ω ≤ w²`, `A ≥ 0`
and `z ↦ (w z)² A z` is integrable on `Iz`, then `z ↦ ω z A z` is integrable on `(0,∞)`. -/
theorem integrableOn_omega_mul {ω A : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hωm : Measurable ω) (hω0 : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => ω z * A z) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (hint.mono_set Set.Ioi_subset_Ici_self)
    (hωm.aestronglyMeasurable.mul hA) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hω0 z) (hA0 z))]
  exact mul_le_mul_of_nonneg_right (hωle z) (hA0 z)

/-- The integral of a truncated pairing is dominated by the `w²`-weighted integral. -/
theorem integral_omega_mul_le {ω A : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hωm : Measurable ω) (hω0 : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∫ z in Set.Ioi 0, ω z * A z)
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z := by
  have h1 := integrableOn_omega_mul hint hωm hω0 hωle hA0 hA
  have h2 : (∫ z in Set.Ioi 0, ω z * A z)
      ≤ ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * A z := by
    refine MeasureTheory.integral_mono_ae h1 (hint.mono_set Set.Ioi_subset_Ici_self) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
    exact mul_le_mul_of_nonneg_right (hωle z) (hA0 z)
  exact h2.trans_eq (setIntegral_Ioi_eq_Iz _)

/-- **Domination of a pairing with a bounded coefficient.**  If `|c z| ≤ C (w z)²` on `(0,∞)`,
`A ≥ 0` and `z ↦ (w z)² A z` is integrable on `Iz`, then `z ↦ c z A z` is integrable on `(0,∞)`
and `|∫_z c A| ≤ C ∫_z (w z)² A z`. -/
theorem integrableOn_coef_mul_le {c A : ℝ → ℝ} {C : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hC : 0 ≤ C) (hbound : ∀ z, 0 < z → |c z| ≤ C * (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => c z * A z) (Set.Ioi 0) ∧
      |∫ z in Set.Ioi 0, c z * A z|
        ≤ C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z) := by
  have hmain : MeasureTheory.IntegrableOn (fun z => c z * A z) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono'
      ((hint.mono_set Set.Ioi_subset_Ici_self).const_mul C) (hc.mul hA) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have h := hbound z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 z)]
    calc |c z| * A z ≤ (C * (Work.Spaces.w z) ^ 2) * A z :=
          mul_le_mul_of_nonneg_right h (hA0 z)
      _ = C * ((Work.Spaces.w z) ^ 2 * A z) := by ring
  refine ⟨hmain, ?_⟩
  have h1 : |∫ z in Set.Ioi 0, c z * A z| ≤ ∫ z in Set.Ioi 0, |c z * A z| :=
    abs_integral_le_integral_abs
  have h2 : (∫ z in Set.Ioi 0, |c z * A z|)
      ≤ ∫ z in Set.Ioi 0, C * ((Work.Spaces.w z) ^ 2 * A z) := by
    refine MeasureTheory.integral_mono_ae hmain.abs ?_ ?_
    · exact (hint.mono_set Set.Ioi_subset_Ici_self).const_mul C
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have h := hbound z hz
      rw [abs_mul, abs_of_nonneg (hA0 z)]
      calc |c z| * A z ≤ (C * (Work.Spaces.w z) ^ 2) * A z :=
            mul_le_mul_of_nonneg_right h (hA0 z)
        _ = C * ((Work.Spaces.w z) ^ 2 * A z) := by ring
  have h3 : (∫ z in Set.Ioi 0, C * ((Work.Spaces.w z) ^ 2 * A z))
      = C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z) := by
    rw [MeasureTheory.integral_const_mul, setIntegral_Ioi_eq_Iz]
  linarith [h1, h2, h3]


/-! ## The `θ`-slice functionals of the first-order estimate -/

/-- `R u z = ∫_θ σ θ · u(z,θ)²`. -/
def Rslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2

/-- `Z u z = ∫_θ σ θ · (z ∂_z u(z,θ))²`. -/
def Zslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2

/-- `Gslice G z = ∫_θ σ θ · G(z,θ)²`. -/
def Gslice (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2

/-- `Sslice G u z = ∫_θ σ θ · G(z,θ) · u(z,θ)`. -/
def Sslice (G u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)

/-- `Pslice α u z = ∫_θ σ θ · (α²z²∂_z²u + α(5+α)z∂_z u)(z,θ) · u(z,θ)`. -/
def Pslice (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
    ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)

/-- `Lslice u z = ∫_θ Lzero1(u z ·) θ · u z θ · σ θ`. -/
def Lslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * Work.FTS.EllipticEst.sEta θ

/-- The angular weight vanishes at `θ = 0`. -/
theorem sEta_zero : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-- The angular weight vanishes at `θ = π/2`. -/
theorem sEta_pi_div_two : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-- `HkSq α 0 u` in terms of `Rslice`. -/
theorem HkSq_zero_eq_Rslice (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 u = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z := by
  rw [HkSq_zero_eq_phi_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [Rslice]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- `HkSq α 0 (grad u)` in terms of `Zslice`. -/
theorem HkSq_grad_eq_Zslice (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Zslice u z := by
  rw [HkSq_zero_eq_phi_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [Zslice]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- The commutation `∫_θ f g = ∫_θ g f` on the angular interval. -/
theorem setIntegral_mul_comm (f g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ * g θ) = ∫ θ in Work.Spaces.Iθ, g θ * f θ :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- `Rslice` written with the square first. -/
theorem Rslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Rslice u z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [Rslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ) (fun θ => (u z θ) ^ 2)

/-- `Zslice` written with the square first. -/
theorem Zslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Zslice u z = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ := by
  rw [Zslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ)
    (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)

/-- `Gslice` written with the square first. -/
theorem Gslice_eq_integral (G : ℝ → ℝ → ℝ) (z : ℝ) :
    Gslice G z = ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [Gslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ) (fun θ => (G z θ) ^ 2)

/-- The `AeData`-slice of `Rslice` is `σ`-integrable. -/
theorem integrableOn_Rslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
      Work.Spaces.Iθ :=
  ((Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz).1).congr_fun
    (fun θ _ => by ring) measurableSet_Icc

/-- The `AeData`-slice of `Gslice` is `σ`-integrable. -/
theorem integrableOn_Gslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2)
      Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integrableOn_sq_mul_sEtaR_of_HkMem h.memG
    hz).congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The `AeData`-slice of `Pslice` is `σ`-integrable. -/
theorem integrableOn_Pslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ *
      ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)) Work.Spaces.Iθ := by
  obtain ⟨-, -, h3, h4, -⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz
  have ha : MeasureTheory.IntegrableOn (fun θ => (α ^ 2 * z ^ 2) *
      (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pzIter 2 u z θ * u z θ))) Work.Spaces.Iθ :=
    (h4.const_mul (α ^ 2 * z ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hb : MeasureTheory.IntegrableOn (fun θ => (α * (5 + α) * z) *
      (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iθ :=
    (h3.const_mul (α * (5 + α) * z)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  refine (ha.add hb).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply]
  ring

/-- The `AeData`-slice of `Sslice` is `σ`-integrable (AM–GM against `G² + u²`). -/
theorem integrableOn_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
      Work.Spaces.Iθ := by
  have hu2 := integrableOn_Rslice h hz
  have hg2 := integrableOn_Gslice h hz
  have hsum : MeasureTheory.IntegrableOn (fun θ =>
      (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
        + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) Work.Spaces.Iθ :=
    (hg2.add hu2).const_mul (1 / 2)
  have hsmG : MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aesm_slice_G h hz
  have hsmU : MeasureTheory.AEStronglyMeasurable (fun θ => u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aesm_of_contOn_Ioo
      (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.contOn_slice h hz)
  have hsmσ : MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.measurable_sEtaR.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hsum (hsmσ.mul (hsmG.mul hsmU)) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ, abs_mul]
  have h2 : 2 * (|G z θ| * |u z θ|) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
    nlinarith [sq_nonneg (|G z θ| - |u z θ|), sq_abs (G z θ), sq_abs (u z θ)]
  calc Work.FTS.EllipticEst.sEta θ * (|G z θ| * |u z θ|)
      = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (2 * (|G z θ| * |u z θ|))) := by ring
    _ ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
    _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
          + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring

/-- `Lslice` is the sum of `Pslice` and `Sslice` (the equation on the open quadrant). -/
theorem Lslice_eq_Pslice_add_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    Lslice u z = Pslice α u z + Sslice G u z := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * Work.FTS.EllipticEst.sEta θ
        = Work.FTS.EllipticEst.sEta θ *
            ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)
          + Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
      · have hbsl := h.eq z hz θ hθ0 hθ1
        have hL : Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
            = Work.Elliptic.Lzero u z θ := by
          have h1 : Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
              = Work.Elliptic.Lzero (fun _ θ' : ℝ => u z θ') z θ :=
            congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => u z θ') z) θ
          have h2 : Work.Elliptic.Lzero (fun _ θ' : ℝ => u z θ') z θ
              = Work.Elliptic.Lzero u z θ := by
            rw [Work.Elliptic.Lzero_eq_deriv, Work.Elliptic.Lzero_eq_deriv]
          rw [h1, h2]
        rw [hL]
        have hkey : Work.Elliptic.Lzero u z θ
            = G z θ + (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
                + (α * (5 + α) * z) * Work.Spaces.pz u z θ) := by
          rw [Work.Elliptic.bslOp_apply] at hbsl
          linarith [hbsl]
        rw [hkey]; ring
      · subst hθ1
        rw [sEta_pi_div_two]; ring
    · subst hθ0
      rw [sEta_zero]; ring
  rw [Lslice, Pslice, Sslice, Work.Spaces.Iθ]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt]
  exact MeasureTheory.integral_add (integrableOn_Pslice h hz) (integrableOn_Sslice h hz)

/-! ## Smoothness of the radial weight and the coefficient bounds of the cut-off -/

/-- `z ↦ (w z)²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_w_sq_two : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hden : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (ne_of_gt hz)
  have hdiv : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) :=
    hnum.div hden hne
  have hsq : ContDiffOn ℝ 2 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := hdiv.pow 2
  refine hsq.congr (fun z _ => ?_)
  rw [Work.Spaces.w]

/-- From the two logarithmic derivative bounds of `χ` one gets `|z²χ''| ≤ C₂ + C₁`. -/
theorem chi_second_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) {C₁ C₂ : ℝ}
    (h1 : ∀ z, |z * deriv χ z| ≤ C₁)
    (h2 : ∀ z, |z * deriv (fun w : ℝ => w * deriv χ w) z| ≤ C₂) :
    ∀ z, |z ^ 2 * deriv (deriv χ) z| ≤ C₂ + C₁ := by
  intro z
  have hd : DifferentiableAt ℝ χ z := (hχ.differentiable (by norm_num)) z
  have hd' : DifferentiableAt ℝ (deriv χ) z := (hχ.differentiable_deriv_two) z
  have hderiv : deriv (fun w : ℝ => w * deriv χ w) z = deriv χ z + z * deriv (deriv χ) z := by
    have h : HasDerivAt (fun w : ℝ => w * deriv χ w)
        (1 * deriv χ z + z * deriv (deriv χ) z) z :=
      (hasDerivAt_id z).mul hd'.hasDerivAt
    simpa using h.deriv
  have hkey : z ^ 2 * deriv (deriv χ) z
      = z * deriv (fun w : ℝ => w * deriv χ w) z - z * deriv χ z := by
    rw [hderiv]; ring
  rw [hkey]
  calc |z * deriv (fun w : ℝ => w * deriv χ w) z - z * deriv χ z|
      ≤ |z * deriv (fun w : ℝ => w * deriv χ w) z| + |z * deriv χ z| := abs_sub _ _
    _ ≤ C₂ + C₁ := add_le_add (h2 z) (h1 z)

/-! ## Measurability and domination helpers used by the main argument -/

/-- A property holding for every `z > 0` holds a.e. on `Iz = [0,∞)`. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), p z := by
  have h1 : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))).symm
  rw [h1]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-- The angular weight is continuous on `(0,π/2)`. -/
theorem continuousOn_sEta : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
    (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))

/-- **Measurability of the source pairing `z ↦ ∫_θ σ θ · G z θ · u z θ`** in the `AeData` class:
for `z > 0` the source `G` agrees with the smooth `bslOp α u`, so the integrand is continuous on
the open quadrant. -/
theorem aesm_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (Sslice G u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsm
  have hσc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_sEta.comp (continuous_snd.continuousOn) (fun p hp => hp.2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
      (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hσc.mul (((hbsl.forall 0).continuousOn).mul ((hsm.forall 0).continuousOn))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.bslOp α u z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.congr (ae_restrict_Iz_of_pos (fun z hz => by
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (Work.Elliptic.bslOp α u z θ * u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.sEta θ *
              (Work.Elliptic.bslOp α u z θ * u z θ) :=
        (MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
            (b := Real.pi / 2))).symm
      have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) :=
        (MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
            (b := Real.pi / 2))).symm
      show (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.bslOp α u z θ * u z θ))
          = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)
      rw [h1, h2]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun θ hθ => by rw [h.eq z hz θ hθ.1 hθ.2])))
  exact aesm_restrict_Ioi_of_Iz h1



end Work.FTS.EllipticEst.AeStepOneAux.Sig2
end
end
