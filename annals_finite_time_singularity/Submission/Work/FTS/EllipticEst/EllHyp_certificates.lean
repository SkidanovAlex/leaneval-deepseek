import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {k : ℕ} {f g F Ψ : ℝ → ℝ → ℝ}

/-! ## 1. Structural lemmas about `SmoothOpen`, `HkMem` and `HkIntegrand`

These are the *bookkeeping* lemmas of the certificate: they transfer the weighted `ℋ^k`
membership along equalities on the open quadrant, and they close it under addition.  They are
stated for `SmoothOpen` (i.e. `C^∞` *on the open quadrant*), which is what the data of
`EllHyp` provides; the corresponding closed-quadrant version
(`Work.FTS.Galerkin.Hilbert.HkMem_add`) needs the much stronger `SmoothNbhd`
(`C^ω` on a neighbourhood of the closed quadrant). -/


/-- The product of a radial function which is `C^∞` on `(0,∞)` with a function of `θ` which is
`C^∞` everywhere is `C^∞` on the open quadrant. -/
theorem SmoothOpen.sep_mul {g χ : ℝ → ℝ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) (hχ : ContDiff ℝ ⊤ χ) :
    SmoothOpen (fun z θ => g z * χ θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => g z * χ θ)) Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => g p.1 * χ p.2) Q0
  rw [show (fun p : ℝ × ℝ => g p.1 * χ p.2)
      = (fun p : ℝ × ℝ => g p.1) * (fun p : ℝ × ℝ => χ p.2) from rfl]
  have hginfty : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Set.Ioi 0) :=
    contDiffOn_infty.mpr hg
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g p.1) Q0 :=
    hginfty.comp contDiffOn_fst fun p hp => (mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p.2) Q0 := by
    change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ ∘ Prod.snd) Q0
    exact (hχ.of_le le_top).comp_contDiffOn (s := Q0)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) contDiffOn_snd
  exact h1.mul h2

/-- Multiplication of a `SmoothOpen` function by `z ^ 2` keeps it `SmoothOpen`. -/
theorem SmoothOpen.zsq_mul (hu : SmoothOpen Ψ) : SmoothOpen (fun z θ => z ^ 2 * Ψ z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)) Q0
  rw [show Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Ψ p.1 p.2 from rfl]
  have hu' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Ψ p.1 p.2) Q0 := hu
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Q0)).pow 2).mul hu'

/-- **Membership in `ℋ^k` by an almost-everywhere majorant.**  The closed-quadrant version
`Work.FTS.LocData.HkMem_of_majorant` requires the domination at every point of
`[0,∞) × [0,π/2]`; here it is only required for almost every interior angle, which is what
the additivity of the `D`-operators on the open quadrant delivers. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) Q0)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k f θ).symm
    · refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      exact hθ
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) := by
        show Set.Icc (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
        exact hIoo.symm
      rw [MeasureTheory.setIntegral_congr_set hIθ,
        MeasureTheory.setIntegral_congr_set hIθ]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        ((hMslice z hz).congr_set_ae hIoo) ?_
      filter_upwards [hle z hz] with θ hθ
      exact hθ
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        exact Filter.Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
          exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

/-- **`ℋ^k`-membership only depends on the open quadrant.**  If `f = g` on `(0,∞) × (0,π/2)`
and both are `C^∞` there, then `f ∈ ℋ^k ↔ g ∈ ℋ^k`; this is the transfer used to replace a
function by the right-hand side of an identity which holds on the open quadrant. -/
theorem HkMem_agreeOnQ {f g : ℝ → ℝ → ℝ} (hg : SmoothOpen g)
    (h : AgreeOnQ f g) (hmf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k g := by
  refine HkMem_of_majorant_ae α k (hg.continuousOn_HkIntegrand α k) hmf.1 hmf.2 ?_
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ =>
      le_of_eq (HkIntegrand_congr h z θ hz0 hθ.1 hθ.2).symm

/-- **Pointwise subadditivity of the `ℋ^k`-integrand on the open quadrant** (the
open-quadrant analogue of `Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le`). -/
theorem HkIntegrand_add_le_open_Ioo (hf : SmoothOpen f) (hg : SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := fun i =>
    SmoothOpen.DzIter_add hf hg i z θ hz hθ.1 hθ.2
  have hMixed : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := fun j i =>
    SmoothOpen.mixed_add hf hg j i z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.HkIntegrand]
  have hZ : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hDz i, add_mul]
          nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i, add_mul]
            nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
          · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
            norm_num
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hZ, hM]

/-- **`ℋ^k` is closed under addition** for data which are `C^∞` on the open quadrant. -/
theorem HkMem_add_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  refine HkMem_of_majorant_ae (α := α) (k := k) (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * (Work.Spaces.HkIntegrand α k f z θ
      + Work.Spaces.HkIntegrand α k g z θ))
    ((smoothOpen_add hf hg).continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    have h1 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ
        + Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iθ :=
      (hmf.1 z hz).add (hmg.1 z hz)
    exact h1.const_mul 2
  · refine IntegrableOn.congr_fun ((hmf.2.add hmg.2).const_mul 2) ?_ measurableSet_Ici
    intro z hz
    show 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      = ∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.HkIntegrand α k f z θ
          + Work.Spaces.HkIntegrand α k g z θ)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst,
          Work.FTS.LocData.HkIntegrand_zero_fst]
        norm_num
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ => HkIntegrand_add_le_open_Ioo hf hg hz0 hθ

/-! ## 2. The analytic inputs of the certificate

These are the (open-quadrant) facts the certificate rests on: the smoothness of the angular
moment `F_*` and of the singular term `Gsing`, the two relations they satisfy, the membership
`D_zΨ ∈ ℋ^k` (the weighted Hardy/AM-GM estimate), and the `ℋ^k`-membership of `F_*·sin 2θ`
and of `Ḡ·sin 2θ`. -/








/-! ## 2b. More `SmoothOpen` closure properties -/

/-- Scalar multiples of a `SmoothOpen` function are `SmoothOpen`. -/
theorem SmoothOpen.const_mul' (c : ℝ) (hu : SmoothOpen Ψ) :
    SmoothOpen (fun z θ => c * Ψ z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => c * Ψ z θ)) Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c * Ψ p.1 p.2) Q0
  have hu' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Ψ p.1 p.2) Q0 := hu
  exact (contDiffOn_const (c := c) (s := Q0)).mul hu'

/-- Differences of `SmoothOpen` functions are `SmoothOpen`. -/
theorem smoothOpen_sub (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - g z θ)) Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2) Q0
  have hf' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2) Q0 := hf
  have hg' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => g p.1 p.2) Q0 := hg
  exact hf'.sub hg'

/-- Congruence for `SmoothOpen` along an equality on the open quadrant. -/
theorem SmoothOpen.congr {f g : ℝ → ℝ → ℝ} (h : SmoothOpen f)
    (h' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) : SmoothOpen g := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Q0
  refine ContDiffOn.congr h ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
  exact (h' p.1 p.2 hz hθ0 hθ1).symm

/-! ## 3. The pointwise identities for the radial multiples of `sin 2θ` -/

/-- `∂_z (g(z)·c) = (∂_z g)·c` (no differentiability needed: `deriv` is linear over
constants). -/
theorem deriv_mul_const' (c : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    deriv (fun z' : ℝ => g z' * c) z = deriv g z * c := by
  have hfun : (fun z' : ℝ => g z' * c) = fun z' => c * g z' := by
    funext z'; ring
  rw [hfun, deriv_const_mul_field]
  ring




/-! ## 4. The identities expressing the elliptic combination -/






/-- The product of a radial function which is `C^∞` on `(0,∞)` with a function of `θ` which is
`C^∞` everywhere, in the opposite order. -/
theorem SmoothOpen.sep_mul_swap {g χ : ℝ → ℝ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) (hχ : ContDiff ℝ ⊤ χ) :
    SmoothOpen (fun z θ => χ θ * g z) := by
  have h := SmoothOpen.sep_mul (g := g) (χ := χ) hg hχ
  exact SmoothOpen.congr h fun z θ _ _ _ => by ring

/-! ## 2c. The smoothness of `Ḡ·sin 2θ`, derived from the first-order relation -/



end Work.FTS.EllipticEst
