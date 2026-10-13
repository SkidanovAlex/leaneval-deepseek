/-
Copyright: work module for the Elgindi finite-time singularity project.

# Joint integrability of the integrands of the truncated energy identity (no moment hypothesis)

This module proves `Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF`: for a datum
`AeData α u G` of the almost-everywhere class and a cutoff `χ` with compact support contained
in `(0,∞)`, `0 ≤ χ ≤ 1`, all the integrands occurring in the truncated energy identity are
jointly integrable against the product measure `dz dθ` on `(0,∞) × Iθ`.

Unlike its sibling `aeJointIntegrableE`, no finiteness hypothesis on the angular mass
`∫⁻_z χw² · ∫⁻_θ u(z,θ)²` is assumed: it is *derived*, from the level-`0` honesty
`HkMem α 0 u` proved in `Dispatch.hkMemUD` (via the a.e. constrained slice Poincaré
inequality), together with `HkMem α 0 (z∂_zu)` (`Dispatch.hkMemGradUD`) and the three
`ℋ⁰`-memberships which are fields of `AeData`.

## Route

* `HkIntegrand α 0 f = w(z)² f(z,θ)² σ(θ)` on `Iθ` with `σ = sin(2θ)^{-η} ≥ 1` there, so for
  every `f` with `HkMem α 0 f` (and continuous on the open quadrant) the `ℋ⁰`-integrand is
  jointly integrable on `nuFts = (dz|_{(0,∞)}) × (dθ|_{Iθ})` (Tonelli on the iterated integral).
* Every one of the seven integrands is dominated, a.e. on `nuFts`, by
  `HkIntegrand α 0 f + HkIntegrand α 0 g` for suitable pairs `(f, g)` drawn from
  `{u, G, z²∂_z²u, z∂_zu}` — by `0 ≤ χ ≤ 1`, `|ab| ≤ (a²+b²)/2` and `w²f² ≤ HkIntegrand α 0 f`.
* The fourth integrand uses the boundedness of `(χw²z²)''` (a `C²` function supported in a
  compact subinterval of `(0,∞)`) together with `HkIntegrand α 0 u ≥ u²` (`w ≥ 1` on `(0,∞)`).
* The seventh integrand is reduced, a.e. on the open quadrant, to the first, second and sixth
  ones via the pointwise equation `Lzero u = G + α²z²∂_z²u + α(5+α)z∂_zu`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.Dispatch.sliceZibpD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

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

/-- The product measure `dz dθ` on the quadrant `(0,∞) × Iθ`. -/
abbrev nuFts : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## The measure `nuFts` and its concentration on the open quadrant -/

/-- `nuFts` is the restriction of the planar Lebesgue measure to the open quadrant. -/
theorem nu_eq_Q0 :
    nuFts = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  change (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _)
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm)

/-- Almost every `(z,θ) ∈ nuFts` has `z > 0`. -/
theorem ae_mem_Ioi_nu : ∀ᵐ p ∂nuFts, 0 < p.1 := by
  rw [nu_eq_Q0]
  exact MeasureTheory.ae_restrict_of_forall_mem
    ((isOpen_Ioi.prod isOpen_Ioo).measurableSet) (fun p hp => hp.1)

/-- Almost every `(z,θ) ∈ nuFts` has `θ ∈ (0, π/2)`. -/
theorem ae_mem_Ioo_nu : ∀ᵐ p ∂nuFts, p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [nu_eq_Q0]
  exact MeasureTheory.ae_restrict_of_forall_mem
    ((isOpen_Ioi.prod isOpen_Ioo).measurableSet) (fun p hp => hp.2)

/-! ## a.e. strong measurability from continuity on the open quadrant -/

/-- A function continuous on the open quadrant is a.e. strongly measurable for `nuFts`. -/
theorem aesm_prod_of_continuousOn_Q0 {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F Q0) :
    MeasureTheory.AEStronglyMeasurable F nuFts := by
  rw [nu_eq_Q0]
  exact hF.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet

/-- The radial weight `Wcut χ` is a.e. strongly measurable for `nuFts`. -/
theorem aesm_Wcut_fst {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Wcut χ p.1) nuFts := by
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; rw [Work.Spaces.w]
    rw [hfun]
    refine (ContinuousOn.div ?_ ?_ ?_).pow 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have hcont : ContinuousOn (Wcut χ) (Set.Ioi 0) :=
    hχsm.continuous.continuousOn.mul hw
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => Wcut χ p.1)
      (Set.Ioi 0 ×ˢ (Set.univ : Set ℝ)) :=
    hcont.comp continuous_fst.continuousOn (fun p hp => hp.1)
  rw [show nuFts = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) from MeasureTheory.Measure.prod_restrict _ _]
  exact (hcomp.mono (Set.prod_mono subset_rfl (Set.subset_univ _))).aestronglyMeasurable
    (measurableSet_Ioi.prod measurableSet_Icc)

/-- a.e. strong measurability of the product integrand `Wcut χ · f · g`. -/
theorem aesm_Wcut_mul_pair {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) {F H : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F Q0) (hH : ContinuousOn H Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Wcut χ p.1 * F p * H p) nuFts :=
  ((aesm_Wcut_fst hχsm).mul (aesm_prod_of_continuousOn_Q0 hF)).mul
    (aesm_prod_of_continuousOn_Q0 hH)

/-- a.e. strong measurability of the square integrand `Wcut χ · f²`. -/
theorem aesm_Wcut_sq {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Wcut χ p.1 * F p ^ 2) nuFts :=
  (aesm_Wcut_fst hχsm).mul ((aesm_prod_of_continuousOn_Q0 hF).pow 2)

/-! ## The level-`0` integrand dominates the unweighted square -/

/-- On the open angular interval, `σ = sin(2θ)^{-η} ≥ 1`, hence
`w(z)² f(z,θ)² ≤ HkIntegrand α 0 f z θ`. -/
theorem sq_weight_le_Hk (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_D hθ
  have h2 : (f z θ) ^ 2 ≤ (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (f z θ))
  rw [HkIntegrand_zero_D α f hθI]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg (Work.Spaces.w z))

/-! ## Joint integrability of the `ℋ⁰`-integrand -/

/-- **Joint integrability of an `ℋ⁰`-integrand.**  Tonelli: the slicewise and outer
integrability of `HkMem α 0 g` give the integrability of `HkIntegrand α 0 g` against the
product measure, the a.e. strong measurability of the slices converting the `lintegral` in
`θ` into an honest integral. -/
theorem integrable_HkIntegrand_of_hkMem {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 g)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) nuFts) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) nuFts := by
  have hnn : ∀ p : ℝ × ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 g p.1 p.2 := fun p =>
    Work.Spaces.HkIntegrand_nonneg α 0 g p.1 p.2
  -- the inner lintegral is the `ofReal` of the slice integral, for every `z > 0`
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
    intro z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hm.1 z (Set.mem_Ici.mpr (le_of_lt hz)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))).symm
  -- the lintegral over the product measure
  have hkey : (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂nuFts)
      = ENNReal.ofReal (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 g z θ) := by
    rw [MeasureTheory.lintegral_prod
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2))
      haesm.aemeasurable.ennreal_ofReal]
    have hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact hslice z hz
    rw [MeasureTheory.lintegral_congr_ae hinner]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hm.2.mono_set Set.Ioi_subset_Ici_self)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z _ =>
        MeasureTheory.integral_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)))).symm
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  rw [show (∫⁻ p : ℝ × ℝ, ‖Work.Spaces.HkIntegrand α 0 g p.1 p.2‖ₑ ∂nuFts)
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂nuFts from
    MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun p => Real.enorm_of_nonneg (hnn p)))]
  rw [hkey]
  exact ENNReal.ofReal_lt_top

/-- The `ℋ⁰`-integrand of a function which is `SmoothOpen` and honestly in `ℋ⁰` is jointly
integrable on `nuFts`. -/
theorem integrable_HkIntegrand_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts :=
  integrable_HkIntegrand_of_hkMem hm
    (aesm_prod_of_continuousOn_Q0
      (F := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (hf.continuousOn_HkIntegrand α 0))

/-! ## The domination lemmas -/

/-- A function dominated a.e. by a nonnegative multiple of `HkIntegrand α 0 f` is integrable. -/
theorem integrable_of_le_const_mul_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    {K : ℝ} (hK0 : 0 ≤ K) (haesm : MeasureTheory.AEStronglyMeasurable F nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts)
    (hbd : ∀ᵐ p ∂nuFts, ‖F p‖ ≤ K * Work.Spaces.HkIntegrand α 0 f p.1 p.2) :
    MeasureTheory.Integrable F nuFts :=
  (hf.const_mul K).mono' haesm hbd

/-- **The pairing `χw² f g` is jointly integrable** whenever the `ℋ⁰`-integrands of `f` and
`g` are: `0 ≤ χ ≤ 1`, `|fg| ≤ (f²+g²)/2` and `w²f² ≤ HkIntegrand α 0 f`. -/
theorem integrable_Wcut_mul_of_HkIntegrable {α : ℝ} {f g : ℝ → ℝ → ℝ} {χ : ℝ → ℝ}
    (hχnn : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Wcut χ z * f z θ * g z θ)) nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts)
    (hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) nuFts) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => Wcut χ z * f z θ * g z θ)) nuFts := by
  refine (hf.add hg).mono' haesm ?_
  filter_upwards [ae_mem_Ioo_nu] with p hp
  obtain ⟨z, θ⟩ := p
  have hχabs : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [hχnn z], hχ1 z⟩
  have hf2 : (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 f z θ :=
    sq_weight_le_Hk α f hp
  have hg2 : (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 g z θ :=
    sq_weight_le_Hk α g hp
  have hnn_f : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α 0 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 0 f z θ
  have hnn_g : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α 0 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 0 g z θ
  have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have habs : ‖Wcut χ z * f z θ * g z θ‖
      = |χ z| * ((Work.Spaces.w z) ^ 2 * (|f z θ| * |g z θ|)) := by
    simp only [Real.norm_eq_abs, Wcut, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
    ring
  have hamgm : |f z θ| * |g z θ| ≤ ((f z θ) ^ 2 + (g z θ) ^ 2) / 2 := by
    have h : 0 ≤ (|f z θ| - |g z θ|) ^ 2 := sq_nonneg _
    rw [sub_sq, sq_abs, sq_abs] at h
    linarith
  calc ‖Wcut χ z * f z θ * g z θ‖
      = |χ z| * ((Work.Spaces.w z) ^ 2 * (|f z θ| * |g z θ|)) := habs
    _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (|f z θ| * |g z θ|)) :=
        mul_le_mul_of_nonneg_right hχabs
          (mul_nonneg hw (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = (Work.Spaces.w z) ^ 2 * (|f z θ| * |g z θ|) := one_mul _
    _ ≤ (Work.Spaces.w z) ^ 2 * (((f z θ) ^ 2 + (g z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hamgm hw
    _ = ((Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 + (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2) / 2 := by
        ring
    _ ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ) / 2 := by
        linarith
    _ ≤ Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ := by
        linarith

/-- **The square `χw² f²` is jointly integrable** whenever the `ℋ⁰`-integrand of `f` is. -/
theorem integrable_Wcut_sq_of_HkIntegrable {α : ℝ} {f : ℝ → ℝ → ℝ} {χ : ℝ → ℝ}
    (hχnn : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Wcut χ z * (f z θ) ^ 2)) nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => Wcut χ z * (f z θ) ^ 2)) nuFts := by
  refine hf.mono' haesm ?_
  filter_upwards [ae_mem_Ioo_nu] with p hp
  obtain ⟨z, θ⟩ := p
  have hχabs : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [hχnn z], hχ1 z⟩
  have hf2 : (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 f z θ :=
    sq_weight_le_Hk α f hp
  have habs : ‖Wcut χ z * (f z θ) ^ 2‖
      = |χ z| * ((Work.Spaces.w z) ^ 2 * (f z θ) ^ 2) := by
    rw [Real.norm_eq_abs, Wcut, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z)),
      abs_of_nonneg (sq_nonneg (f z θ))]
    ring
  calc ‖Wcut χ z * (f z θ) ^ 2‖
      = |χ z| * ((Work.Spaces.w z) ^ 2 * (f z θ) ^ 2) := habs
    _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hχabs (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 := one_mul _
    _ ≤ Work.Spaces.HkIntegrand α 0 f z θ := hf2

/-! ## The second derivative of the truncated radial weight `χw²z²` -/

/-- `Wcut χ = χ·w²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_two_Wcut {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) :
    ContDiffOn ℝ 2 (Wcut χ) (Set.Ioi 0) := by
  have hw : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; rw [Work.Spaces.w]
  have hw2 : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    rw [hw]
    refine (ContDiffOn.div ?_ ?_ ?_).pow 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  exact ContDiffOn.mul hχsm.contDiffOn hw2

/-- `WcutZ2 χ = χ·w²·z²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_two_WcutZ2 {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) :
    ContDiffOn ℝ 2 (WcutZ2 χ) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * Wcut χ z) (Set.Ioi 0) :=
    (contDiffOn_id.pow 2).mul (contDiffOn_two_Wcut hχsm)
  refine h1.congr ?_
  intro z hz
  simp only [WcutZ2]
  ring

/-- Continuity on `(0,∞)` of the second derivative of `WcutZ2 χ`. -/
theorem continuousOn_deriv_deriv_WcutZ2 {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) :
    ContinuousOn (fun z : ℝ => deriv (deriv (WcutZ2 χ)) z) (Set.Ioi 0) :=
  (((contDiffOn_two_WcutZ2 hχsm).deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).deriv_of_isOpen
      (m := 0) isOpen_Ioi (by norm_num)).continuousOn

/-- The second derivative of `χw²z²` is a.e. strongly measurable for `nuFts`. -/
theorem aesm_deriv_deriv_WcutZ2 {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (Function.uncurry u) Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv (deriv (WcutZ2 χ)) p.1 * (u p.1 p.2) ^ 2) nuFts := by
  refine aesm_prod_of_continuousOn_Q0 (F := fun p : ℝ × ℝ =>
    deriv (deriv (WcutZ2 χ)) p.1 * (u p.1 p.2) ^ 2) ?_
  exact ((continuousOn_deriv_deriv_WcutZ2 hχsm).comp continuous_fst.continuousOn
    (fun p hp => hp.1)).mul (hu.pow 2)

/-- **The second derivative of `χw²z²` is bounded.**  The function is `C²` and supported in a
compact subinterval of `(0,∞)`, so its second derivative vanishes off that interval and is
bounded on it. -/
theorem exists_abs_deriv_deriv_WcutZ2_le {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ)
    (hχcpt : HasCompactSupport χ)
    (hχ0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → χ z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, |deriv (deriv (WcutZ2 χ)) z| ≤ K := by
  obtain ⟨δ, hδpos, hχδ⟩ := hχ0
  obtain ⟨b, hb⟩ := hasCompactSupport_eventually_zero hχcpt
  have hsupp : ∀ z, z ∉ Set.Icc δ b → χ z = 0 := by
    intro z hz
    rcases not_and_or.mp hz with h | h
    · exact hχδ z (le_of_lt (not_le.mp h))
    · exact hb z (le_of_lt (not_le.mp h))
  have hsuppW : ∀ z, z ∉ Set.Icc δ b → WcutZ2 χ z = 0 := by
    intro z hz
    simp only [WcutZ2, Wcut]
    rw [hsupp z hz]
    ring
  have hcont : ContinuousOn (fun z : ℝ => deriv (deriv (WcutZ2 χ)) z) (Set.Icc δ b) :=
    (continuousOn_deriv_deriv_WcutZ2 hχsm).mono
      (fun z hz => lt_of_lt_of_le hδpos hz.1)
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max K 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc δ b
  · refine le_trans ?_ (le_max_left K 0)
    simpa only [Real.norm_eq_abs] using hK z hz
  · rw [deriv_deriv_eq_zero_off hsuppW z hz, abs_zero]
    exact le_max_right K 0

/-! ## The main theorem -/

theorem aeJointIntegrableF (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (χ : ℝ → ℝ) (hχsm : ContDiff ℝ 2 χ) (hχcpt : HasCompactSupport χ)
    (hχ0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → χ z = 0)
    (hχnn : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) :
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.FTS.EllipticEst.Dispatch.Wcut χ z * G z θ * u z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.FTS.EllipticEst.Dispatch.WcutZ2 χ z * Work.Spaces.pzIter 2 u z θ * u z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.FTS.EllipticEst.Dispatch.Wcut χ z * (z * Work.Spaces.pz u z θ) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => deriv (deriv (Work.FTS.EllipticEst.Dispatch.WcutZ2 χ)) z * (u z θ) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.FTS.EllipticEst.Dispatch.Wcut χ z * (u z θ) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.FTS.EllipticEst.Dispatch.WcutZ χ z * Work.Spaces.pz u z θ * u z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.FTS.EllipticEst.Dispatch.Wcut χ z
          * (Work.Elliptic.Lzero u z θ) * u z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
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
  have hmd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := hkMem_gradUD α u G h
  -- ## joint integrability of the `ℋ⁰`-integrands
  have hIu := integrable_HkIntegrand_of_smoothOpen hU hmu
  have hIg := integrable_HkIntegrand_of_smoothOpen hG hmg
  have hIa := integrable_HkIntegrand_of_smoothOpen hA hma
  have hId := integrable_HkIntegrand_of_smoothOpen hD hmd
  -- ## the seven integrands
  -- 1. the source pairing `χw² G u`
  have h1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Wcut χ z * G z θ * u z θ)) nuFts :=
    integrable_Wcut_mul_of_HkIntegrable hχnn hχ1
      (aesm_Wcut_mul_pair hχsm hG.continuousOn hU.continuousOn) hIg hIu
  -- 2. the radial second-derivative pairing `χw² z² ∂_z²u · u`
  have h2' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Wcut χ z * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)) nuFts :=
    integrable_Wcut_mul_of_HkIntegrable hχnn hχ1
      (aesm_Wcut_mul_pair hχsm hA.continuousOn hU.continuousOn) hIa hIu
  have h2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => WcutZ2 χ z * Work.Spaces.pzIter 2 u z θ * u z θ)) nuFts :=
    h2'.congr (Filter.Eventually.of_forall fun p => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry, WcutZ2, Wcut]
      ring)
  -- 3. the radial first-derivative square `χw² (z ∂_zu)²`
  have h3 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Wcut χ z * (z * Work.Spaces.pz u z θ) ^ 2)) nuFts :=
    integrable_Wcut_sq_of_HkIntegrable hχnn hχ1
      (aesm_Wcut_sq hχsm hD.continuousOn) hId
  -- 4. the weight-derivative term `(χw²z²)'' u²`
  obtain ⟨K, hK0, hK⟩ := exists_abs_deriv_deriv_WcutZ2_le hχsm hχcpt hχ0
  have h4 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => deriv (deriv (WcutZ2 χ)) z * (u z θ) ^ 2)) nuFts :=
    integrable_of_le_const_mul_HkIntegrand hK0 (aesm_deriv_deriv_WcutZ2 hχsm hU.continuousOn) hIu
      (by
        filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
        obtain ⟨z, θ⟩ := p
        have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := one_le_w_D hp1
        have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw1
        have hsq : (u z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 u z θ := by
          have h := sq_weight_le_Hk (z := z) α u hp2
          have h' : (u z θ) ^ 2 ≤ (Work.Spaces.w z) ^ 2 * (u z θ) ^ 2 := by
            calc (u z θ) ^ 2 = 1 * (u z θ) ^ 2 := (one_mul _).symm
              _ ≤ (Work.Spaces.w z) ^ 2 * (u z θ) ^ 2 :=
                  mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
          linarith
        have habs : ‖deriv (deriv (WcutZ2 χ)) z * (u z θ) ^ 2‖
            = |deriv (deriv (WcutZ2 χ)) z| * (u z θ) ^ 2 := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (u z θ))]
        calc ‖deriv (deriv (WcutZ2 χ)) z * (u z θ) ^ 2‖
            = |deriv (deriv (WcutZ2 χ)) z| * (u z θ) ^ 2 := habs
          _ ≤ K * (u z θ) ^ 2 := mul_le_mul_of_nonneg_right (hK z) (sq_nonneg _)
          _ ≤ K * Work.Spaces.HkIntegrand α 0 u z θ := mul_le_mul_of_nonneg_left hsq hK0)
  -- 5. the weight term `χw² u²`
  have h5 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Wcut χ z * (u z θ) ^ 2)) nuFts :=
    integrable_Wcut_sq_of_HkIntegrable hχnn hχ1 (aesm_Wcut_sq hχsm hU.continuousOn) hIu
  -- 6. the radial first-derivative pairing `χw² z ∂_zu · u`
  have h6' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Wcut χ z * (z * Work.Spaces.pz u z θ) * u z θ)) nuFts :=
    integrable_Wcut_mul_of_HkIntegrable hχnn hχ1
      (aesm_Wcut_mul_pair hχsm hD.continuousOn hU.continuousOn) hId hIu
  have h6 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => WcutZ χ z * Work.Spaces.pz u z θ * u z θ)) nuFts :=
    h6'.congr (Filter.Eventually.of_forall fun p => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry, WcutZ, Wcut]
      ring)
  -- 7. the `Lzero` pairing `χw² (Lzero u) u`
  have h7 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Wcut χ z * (Work.Elliptic.Lzero u z θ) * u z θ)) nuFts := by
    have hsub : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Wcut χ z * G z θ * u z θ
          + α ^ 2 * (WcutZ2 χ z * Work.Spaces.pzIter 2 u z θ * u z θ)
          + (α * (5 + α)) * (WcutZ χ z * Work.Spaces.pz u z θ * u z θ))) nuFts :=
      (h1.add (h2.const_mul (α ^ 2))).add (h6.const_mul (α * (5 + α)))
    refine hsub.congr ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    obtain ⟨z, θ⟩ := p
    have heq := h.eq z hp1 θ hp2.1 hp2.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hLz : Work.Elliptic.Lzero u z θ
        = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ) := by linarith
    simp only [Function.uncurry, WcutZ2, WcutZ, hLz]
    ring
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Work.FTS.EllipticEst.Dispatch
