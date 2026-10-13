import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyTools
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.AngAWeak.aeEnergyWAux
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF

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
