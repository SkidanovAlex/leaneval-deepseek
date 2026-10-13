import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Gsing_ode_of_sol
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin

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

/-- A function which is `C^ω` on a neighbourhood of the closed quadrant is `C^∞` on the open
quadrant. -/
theorem SmoothNbhd_smoothOpen (h : Work.Spaces.SmoothNbhd Ψ) : SmoothOpen Ψ := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ) Q0
  have hsub : Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
    refine ⟨?_, ?_, ?_⟩
    · show (-1 : ℝ) < p.1; linarith
    · show (-1 : ℝ) < p.2; linarith
    · show p.2 < π / 2 + 1; linarith [Real.pi_pos]
  exact (h.mono hsub).of_le le_top

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

/-- The angular moment `F_*(F)` is `C^∞` on `(0,∞)` for the data of `EllHyp`. -/
theorem Fstar_contDiffOn_Ioi_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
  (Work.FTS.EllipticEst.Gsing_ode_of_sol α k F Ψ hα (by linarith) hHyp.smoothNbhd hHyp.sol
    hHyp.memF).1

/-- The singular term `Gsing α F` is `C^∞` on `(0,∞)` for the data of `EllHyp`. -/
theorem Gsing_contDiffOn_Ioi_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0) :=
  (Work.FTS.EllipticEst.Gsing_ode_of_sol α k F Ψ hα (by linarith) hHyp.smoothNbhd hHyp.sol
    hHyp.memF).2.1

/-- The first-order relation of the singular term: `α z ∂_z Gsing = -5 Ḡ`. -/
theorem Gsing_first_order_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z := by
  have hFsm := Fstar_contDiffOn_Ioi_of_EllHyp α k F Ψ hα hα4 hHyp
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol hHyp.memF
  have hL12 := Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
      (by norm_num)).hasDerivAt
  have hJ := Cert.Jfun_hasDerivAt_of_Fstar α F hFsm hFint hα (by linarith)
  exact Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ

/-- The second-order ODE of the singular term:
`α²z²G'' + α(5+α)zG' = (15/4)F_*`. -/
theorem Gsing_second_order_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z :=
  (Work.FTS.EllipticEst.Gsing_ode_of_sol α k F Ψ hα (by linarith) hHyp.smoothNbhd hHyp.sol
    hHyp.memF).2.2

/-- `D_z Ψ ∈ ℋ^k` for the data of `EllHyp` (the weighted radial Hardy/AM-GM estimate). -/
theorem HkMem_Dz_psi_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) := by
  obtain ⟨C, hC, h⟩ := Work.FTS.EllipticEst.HkNorm_Dz_le_open k
  exact (h α Ψ hα (by linarith)
    (fun n => (SmoothNbhd_smoothOpen hHyp.smoothNbhd).forall n) hHyp.memPsi hHyp.memZ2).1

/-- `F_*·sin 2θ ∈ ℋ^k` for the data of `EllHyp`. -/
theorem HkMem_Fstar_sin_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
  Cert.HkMem_Fstar_sin α k F Ψ hα hα4 hHyp

/-- `Ḡ·sin 2θ ∈ ℋ^k` for the data of `EllHyp` (Lemma `HardyInequality4` of the paper). -/
theorem HkMem_Gbar_sin_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
  Cert.HkMem_Gbar_sin α k F Ψ hα hα4 hHyp

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

/-- `∂_z` of a radial multiple of `sin 2θ`: `∂_z (g(z)·sin 2θ) = ∂_z g·sin 2θ`. -/
theorem pz_radialSin (g : ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => g z * Real.sin (2 * θ))
      = fun z θ => deriv g z * Real.sin (2 * θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv_mul_const' (Real.sin (2 * θ)) g z

/-- `D_z (g(z)·sin 2θ) = (z ∂_zg)·sin 2θ`, as a function of `(z,θ)`. -/
theorem Dz_radialSin (g : ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => g z * Real.sin (2 * θ))
      = fun z θ => z * deriv g z * Real.sin (2 * θ) := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_radialSin]
  ring

/-- `D_z²(g(z)·sin 2θ) = (z ∂_zg + z²∂_zzg)·sin 2θ`. -/
theorem DzIter2_radialSin (g : ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => deriv g z') z) :
    Work.Spaces.DzIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = (z * deriv g z + z ^ 2 * deriv (fun z' => deriv g z') z) * Real.sin (2 * θ) := by
  have hfun : Work.Spaces.Dz (fun z θ => g z * Real.sin (2 * θ))
      = fun z θ => z * deriv g z * Real.sin (2 * θ) := Dz_radialSin g
  rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, hfun]
  have hderiv : deriv (fun z' : ℝ => z' * deriv g z' * Real.sin (2 * θ)) z
      = (deriv g z + z * deriv (fun z' => deriv g z') z) * Real.sin (2 * θ) := by
    have hA : HasDerivAt (fun z' : ℝ => deriv g z') (deriv (fun z' => deriv g z') z) z :=
      hd.hasDerivAt
    have hB : HasDerivAt (fun z' : ℝ => z' * deriv g z')
        (1 * deriv g z + z * deriv (fun z' => deriv g z') z) z :=
      (hasDerivAt_id z).mul hA
    have hC := hB.mul_const (Real.sin (2 * θ))
    rw [hC.deriv]
    ring
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hderiv]
  ring

/-! ## 4. The identities expressing the elliptic combination -/

/-- **The identity for `α²D_z²` of the radial multiple.**  Writing `G = Gsing α F`, the ODE
`α²z²G'' + α(5+α)zG' = (15/4)F_*` and the first-order relation `α z G' = -5Ḡ` give

  `α²D_z²(G(z)·sin 2θ) = (15/4)·(sin 2θ · F_*) + 25·(Ḡ · sin 2θ)`. -/
theorem alphaDzIter2_GsingSin_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
    (hode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z)
    (hrel : α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) :
    α ^ 2 * Work.Spaces.DzIter 2
        (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
        + 25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  rw [DzIter2_radialSin (Work.Elliptic.Gsing α F) hd]
  have hX : α ^ 2 * (z * deriv (Work.Elliptic.Gsing α F) z
        + z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
      = (15 / 4) * Work.Elliptic.Fstar F z + 25 * Work.Elliptic.Gbar α F z := by
    nlinarith [hode, hrel]
  linear_combination (Real.sin (2 * θ)) * hX

/-- **The identity for `5αD_z` of the radial multiple.**  The first-order relation
`α z G' = -5Ḡ` gives `5αD_z(G(z)·sin 2θ) = -25·(Ḡ·sin 2θ)`. -/
theorem alphaDz_GsingSin_eq (α : ℝ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hrel : α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) :
    5 * α * Work.Spaces.Dz
        (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = -25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  rw [Dz_radialSin]
  linear_combination (5 * Real.sin (2 * θ)) * hrel

/-- **The identity for `α²D_z²` of the straightened solution `Ψ̂ = Ψ + Gsing α F·sin 2θ`.** -/
theorem alphaDzIter2_straight_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hΨ : SmoothOpen Ψ)
    (hG : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (hd : DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
    (hode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z)
    (hrel : α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) :
    α ^ 2 * Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ
        + ((15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
          + 25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
  rw [SmoothOpen.DzIter_add hΨ hG 2 z θ hz hθ.1 hθ.2, mul_add,
    alphaDzIter2_GsingSin_eq α F hα hd hode hrel]

/-- **The identity for `5αD_z` of the straightened solution.** -/
theorem alphaDz_straight_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hΨ : SmoothOpen Ψ)
    (hG : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (hrel : α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) :
    5 * α * Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = 5 * α * Work.Spaces.Dz Ψ z θ
        - 25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  rw [show Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
      = Work.Spaces.DzIter 1 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
      from rfl,
    SmoothOpen.DzIter_add hΨ hG 1 z θ hz hθ.1 hθ.2, mul_add]
  rw [show Work.Spaces.DzIter 1 (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
      = Work.Spaces.Dz (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
      from rfl]
  rw [show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl]
  rw [alphaDz_GsingSin_eq α F hrel]
  ring

/-- `D_z²Ψ = z²∂_zzΨ + D_zΨ` on the open quadrant. -/
theorem DzIter2_eq_zsq_pzIter2_add_Dz (Ψ : ℝ → ℝ → ℝ) (hΨ : SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + Work.Spaces.Dz Ψ z θ := by
  have hd1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice hθ hz).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z :=
    (hΨ.pz.hasDerivAt_slice hθ hz).differentiableAt
  have h := zsq_pzIter2_eq Ψ hd1 hd2
  linarith [h]

/-- The product of a radial function which is `C^∞` on `(0,∞)` with a function of `θ` which is
`C^∞` everywhere, in the opposite order. -/
theorem SmoothOpen.sep_mul_swap {g χ : ℝ → ℝ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) (hχ : ContDiff ℝ ⊤ χ) :
    SmoothOpen (fun z θ => χ θ * g z) := by
  have h := SmoothOpen.sep_mul (g := g) (χ := χ) hg hχ
  exact SmoothOpen.congr h fun z θ _ _ _ => by ring

/-! ## 2c. The smoothness of `Ḡ·sin 2θ`, derived from the first-order relation -/

/-- **`Ḡ·sin 2θ` is `C^∞` on the open quadrant** for the data of `EllHyp`.  This is *derived*
from the first-order relation `α z ∂_zG = -5Ḡ` (the child `Gsing` need not be smooth): on the
open quadrant `25·(Ḡ·sin 2θ) = 5α D_zΨ - 5α D_z Ψ̂` with `Ψ̂ = Ψ + G·sin 2θ` is a difference of
two `SmoothOpen` functions. -/
theorem SmoothOpen_GbarSin (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hgs : ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z)
    (hGsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0))
    (hΨso : SmoothOpen Ψ)
    (hSso : SmoothOpen (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) :
    SmoothOpen (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  have hsin2 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hGso : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    SmoothOpen.sep_mul hGsm hsin2
  have h25 : SmoothOpen (fun z θ => 25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
    refine (smoothOpen_sub (hΨso.Dz.const_mul' (5 * α))
      (hSso.Dz.const_mul' (5 * α))).congr ?_
    intro z θ hz hθ hlt
    have h := alphaDz_straight_eq α F Ψ hz ⟨hθ, hlt⟩ hΨso hGso (hgs z hz)
    linarith [h]
  have h1 : SmoothOpen (fun z θ => (1 / 25) * (25 * (Work.Elliptic.Gbar α F z
      * Real.sin (2 * θ)))) := h25.const_mul' (1 / 25)
  exact h1.congr fun z θ _ _ _ => by ring

theorem EllHyp_certificates (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      Work.Spaces.HkMem α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) ∧
      Work.Spaces.HkMem α k (fun z θ => 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) ∧
      Work.Spaces.HkMem α k (fun z θ => -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ∧
      Work.Spaces.HkMem α k
        (fun z θ => (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) ∧
      Work.Spaces.HkMem α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) ∧
      Work.Spaces.HkMem α k (fun z θ => -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
  -- the analytic inputs
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Fstar_contDiffOn_Ioi_of_EllHyp α k F Ψ hα hα4 hHyp
  have hGsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0) :=
    Gsing_contDiffOn_Ioi_of_EllHyp α k F Ψ hα hα4 hHyp
  have hrel := Gsing_first_order_of_EllHyp α k F Ψ hα hα4 hHyp
  have hode := Gsing_second_order_of_EllHyp α k F Ψ hα hα4 hHyp
  have hsin2 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  -- smoothness of the pieces
  have hΨso : SmoothOpen Ψ := SmoothNbhd_smoothOpen hHyp.smoothNbhd
  have hAso : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    SmoothOpen.sep_mul hGsm hsin2
  have hSso : SmoothOpen (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    smoothOpen_add hΨso hAso
  have hFsso : SmoothOpen (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    SmoothOpen.sep_mul hFsm hsin2
  have hGsinso : SmoothOpen (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z) :=
    SmoothOpen.sep_mul_swap hFsm hsin2
  have hGbso : SmoothOpen (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    SmoothOpen_GbarSin α F Ψ hα hrel hGsm hΨso hSso
  have hGderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z := by
    intro z hz
    have hd : ContDiffOn ℝ (1 : WithTop ℕ∞) (deriv (Work.Elliptic.Gsing α F)) (Set.Ioi 0) :=
      (hGsm 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- the atomic memberships
  have hmemDz : Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) :=
    HkMem_Dz_psi_of_EllHyp α k F Ψ hα hα4 hHyp
  have hmemFs : Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    HkMem_Fstar_sin_of_EllHyp α k F Ψ hα hα4 hHyp
  have hmemGb : Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    HkMem_Gbar_sin_of_EllHyp α k F Ψ hα hα4 hHyp
  have hmemDzIter2 : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 Ψ) := by
    have hcomb : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + Work.Spaces.Dz Ψ z θ) :=
      HkMem_add_open ((hΨso.pzIter 2).zsq_mul) hΨso.Dz hHyp.memZ2 hmemDz
    refine HkMem_agreeOnQ (hΨso.DzIter 2) ?_ hcomb
    intro z θ hz hθ hlt
    exact (DzIter2_eq_zsq_pzIter2_add_Dz Ψ hΨso hz ⟨hθ, hlt⟩).symm
  -- the scaled pieces
  have hs1 : SmoothOpen (fun z θ => α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ) :=
    (hΨso.DzIter 2).const_mul' (α ^ 2)
  have hm1 : Work.Spaces.HkMem α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α k (α ^ 2) hmemDzIter2
  have hs2 : SmoothOpen (fun z θ => 5 * α * Work.Spaces.Dz Ψ z θ) :=
    hΨso.Dz.const_mul' (5 * α)
  have hm2 : Work.Spaces.HkMem α k (fun z θ => 5 * α * Work.Spaces.Dz Ψ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α k (5 * α) hmemDz
  have hs3 : SmoothOpen (fun z θ => (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) :=
    hGsinso.const_mul' (15 / 4)
  have hm3 : Work.Spaces.HkMem α k
      (fun z θ => (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
    have h := Work.FTS.LocData.HkMem_const_mul α k (15 / 4) hmemFs
    rwa [show (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
        = fun z θ => (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z) from by
      funext z θ; ring] at h
  have hs4 : SmoothOpen (fun z θ => 25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    hGbso.const_mul' 25
  have hm4 : Work.Spaces.HkMem α k
      (fun z θ => 25 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k 25 hmemGb
  have hs7 : SmoothOpen (fun z θ => -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    ((hΨso.pzIter 2).zsq_mul).const_mul' (-(α ^ 2))
  have hm7 : Work.Spaces.HkMem α k
      (fun z θ => -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α k (-(α ^ 2)) hHyp.memZ2
  have hs8 : SmoothOpen
      (fun z θ => (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) :=
    hGsinso.const_mul' (3 * α / 4)
  have hm8 : Work.Spaces.HkMem α k
      (fun z θ => (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
    have h := Work.FTS.LocData.HkMem_const_mul α k (3 * α / 4) hmemFs
    rwa [show (fun z θ => (3 * α / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
        = fun z θ => (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z) from by
      funext z θ; ring] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hSso.DzIter 2).forall n
  · intro n
    exact (hSso.Dz).forall n
  · intro n
    exact ((hΨso.pzIter 2).zsq_mul).forall n
  · intro n
    exact hGsinso.forall n
  · refine HkMem_agreeOnQ ((hSso.DzIter 2).const_mul' (α ^ 2)) ?_
      (HkMem_add_open hs1 (smoothOpen_add hs3 hs4) hm1 (HkMem_add_open hs3 hs4 hm3 hm4))
    intro z θ hz hθ hlt
    exact (alphaDzIter2_straight_eq α F Ψ hα hz ⟨hθ, hlt⟩ hΨso hAso (hGderiv z hz)
      (hode z hz) (hrel z hz)).symm
  · have hmain : Work.Spaces.HkMem α k (fun z θ => 5 * α * Work.Spaces.Dz Ψ z θ
        + (-25) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
      HkMem_add_open hs2 (hGbso.const_mul' (-25)) hm2
        (Work.FTS.LocData.HkMem_const_mul α k (-25) hmemGb)
    refine HkMem_agreeOnQ ((hSso.Dz).const_mul' (5 * α)) ?_ hmain
    intro z θ hz hθ hlt
    have h := alphaDz_straight_eq α F Ψ hz ⟨hθ, hlt⟩ hΨso hAso (hrel z hz)
    show 5 * α * Work.Spaces.Dz Ψ z θ + (-25) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      = 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
    rw [h]
    ring
  · exact hm7
  · exact hm8
  · refine HkMem_agreeOnQ
      (smoothOpen_add ((hSso.DzIter 2).const_mul' (α ^ 2)) ((hSso.Dz).const_mul' (5 * α))) ?_
      (HkMem_add_open hs1 (smoothOpen_add hs2 hs3) hm1 (HkMem_add_open hs2 hs3 hm2 hm3))
    intro z θ hz hθ hlt
    have h1 := alphaDzIter2_straight_eq α F Ψ hα hz ⟨hθ, hlt⟩ hΨso hAso (hGderiv z hz)
      (hode z hz) (hrel z hz)
    have h2 := alphaDz_straight_eq α F Ψ hz ⟨hθ, hlt⟩ hΨso hAso (hrel z hz)
    show α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ + (5 * α * Work.Spaces.Dz Ψ z θ
        + (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z))
      = α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
    rw [h1, h2]
    ring
  · exact HkMem_add_open hs7 hs8 hm7 hm8

end Work.FTS.EllipticEst
