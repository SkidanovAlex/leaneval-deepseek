import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Open-quadrant closure lemmas for the `RemovingL12` assembly

Self-contained `SmoothOpen`/`HkMem` closure lemmas (proved from `OpenQDefs`, `LocData` and
`SmoothOpenAdd`) used by the assembly of
`Work.FTS.EllipticEst.theta_theta_removing_fts`.  They are collected in their own module so
that the assembly file stays within the project's per-file limits and shares no module with the
`Fstar_Hk_le` development (whose `integrableOn_zSummand` clashes with `OpenQDefs`).
-/
noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
variable {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}

set_option maxHeartbeats 4000000

abbrev StraightHat (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

/-- The angular coefficient `z ↦ (15/4)·F_*(z) + 5(5+α)·Ḡ(z)` of the removal identity for
`z²∂_zzΨ`. -/
abbrev Gcoef (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z

/-! ## Self-contained open-quadrant closure lemmas

The assembly uses only a handful of `SmoothOpen`/`HkMem` closure facts.  They are proved here
from `OpenQDefs`, `LocData` and `SmoothOpenAdd` so that this file shares no module with the
`Fstar_Hk_le` development, whose declaration `integrabletesOn_zSummand` clashes with the one of
`OpenQDefs`. -/

/-- `SmoothNbhd` implies `SmoothOpen`. -/
theorem SmoothNbhd_smoothOpen' {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
    Work.FTS.EllipticEst.Q0
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ :=
      Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 from hp)
    refine ⟨?_, ?_, ?_⟩
    · show (-1 : ℝ) < p.1; linarith
    · show (-1 : ℝ) < p.2; linarith
    · show p.2 < π / 2 + 1; linarith [Real.pi_pos]
  exact (h.mono hsub).of_le le_top

/-- A radial factor which is `C^∞` on `(0,∞)` times an angular factor which is `C^∞`
everywhere is `C^∞` on the open quadrant. -/
theorem SmoothOpen_sep_mul' {g χ : ℝ → ℝ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) (hχ : ContDiff ℝ ⊤ χ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z * χ θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => g z * χ θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => g p.1 * χ p.2) Work.FTS.EllipticEst.Q0
  rw [show (fun p : ℝ × ℝ => g p.1 * χ p.2)
      = (fun p : ℝ × ℝ => g p.1) * (fun p : ℝ × ℝ => χ p.2) from rfl]
  have hginfty : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Set.Ioi 0) :=
    contDiffOn_infty.mpr hg
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g p.1)
      Work.FTS.EllipticEst.Q0 :=
    hginfty.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p.2)
      Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ ∘ Prod.snd) Work.FTS.EllipticEst.Q0
    exact (hχ.of_le le_top).comp_contDiffOn (s := Work.FTS.EllipticEst.Q0)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) contDiffOn_snd
  exact h1.mul h2

/-- `SmoothOpen` is closed under multiplication by `z ^ 2`. -/
theorem SmoothOpen_zsq_mul' {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => z ^ 2 * f z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * f p.1 p.2 from rfl]
  have h' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := h
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul h'

/-- `SmoothOpen` is closed under multiplication by `z`. -/
theorem SmoothOpen_z_mul' {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => z * f z θ)
      = fun p : ℝ × ℝ => p.1 * f p.1 p.2 from rfl]
  have h' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := h
  exact (contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).mul h'

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem SmoothOpen_const_mul' (c : ℝ) {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => c * f z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c * f p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul h

/-- `SmoothOpen` is closed under pointwise subtraction. -/
theorem SmoothOpen_sub' {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.sub hg

/-- **Pointwise subadditivity of the `ℋ^k`-integrand on the open quadrant** (a self-contained
copy of the workspace lemma of the same shape, so that this module needs neither
`EllHyp_certificates` nor the `Fstar_Hk_le` development). -/
theorem HkIntegrand_add_le_open_Ioo' (hf : SmoothOpen f) (hg : SmoothOpen g) {z θ : ℝ}
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

/-- **Membership in `ℋ^k` by an almost-everywhere majorant** (the open-quadrant version of
`Work.FTS.LocData.HkMem_of_majorant`). -/
theorem HkMem_of_majorant_ae' (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      Work.FTS.EllipticEst.Q0)
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

/-- **`ℋ^k` is closed under addition** for data which are `C^∞` on the open quadrant. -/
theorem HkMem_add_open' {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  refine HkMem_of_majorant_ae' (α := α) (k := k) (f := fun z θ => f z θ + g z θ)
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
      exact Filter.Eventually.of_forall fun θ hθ => HkIntegrand_add_le_open_Ioo' hf hg hz0 hθ


/-! ## Glue lemmas -/

/-- Congruence of `SmoothOpen` on the open quadrant. -/
theorem SmoothOpen_congr {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g :=
  Work.FTS.EllipticEst.smoothOpen_of_forall fun n =>
    (hf.forall n).congr fun p hp => by
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact (h p.1 p.2 hz hθ0 hθ1).symm

/-- Congruence of `HkNorm` on the open quadrant. -/
theorem HkNorm_congr_open {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-- `∂_θ`-iterates of a function `C^∞` on the open quadrant are `C^∞` there. -/
theorem SmoothOpen_pthIter' {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `orthSource F` is orthogonal to `sin θ cos²θ` — unconditionally: the junk case of the
totalised integral and the honest case of Fubini both give `0`. -/
theorem Fstar_orthSource' (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z = 0 := by
  set g : ℝ → ℝ := fun θ => (F z θ - (15 / 4) * Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
    * Work.Elliptic.sinCos2 θ with hg
  have hval : Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z
      = ∫ θ in Work.Spaces.Iθ, g θ := by
    rw [Work.Elliptic.Fstar]
    refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [hg, Work.Elliptic.orthSource]
  rw [hval]
  by_cases hint : Integrable g (volume.restrict Work.Spaces.Iθ)
  · have hpt : ∀ θ, g θ = F z θ * Work.Elliptic.sinCos2 θ
        - ((15 / 4) * Work.Elliptic.Fstar F z) * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; simp only [hg]; ring
    have h2int : Integrable (fun θ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have hc : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
        simp only [Work.Elliptic.sinCos2]; fun_prop
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
    have h1int : Integrable (fun θ => F z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have hsub : Integrable (fun θ => g θ + ((15 / 4) * Work.Elliptic.Fstar F z)
          * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) (volume.restrict Work.Spaces.Iθ) :=
        hint.add (h2int.const_mul _)
      refine hsub.congr ?_
      filter_upwards with θ
      rw [hpt θ]; ring
    have hcongr : (∫ θ in Work.Spaces.Iθ, g θ)
        = ∫ θ in Work.Spaces.Iθ, (F z θ * Work.Elliptic.sinCos2 θ
            - ((15 / 4) * Work.Elliptic.Fstar F z)
              * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) :=
      setIntegral_congr_fun measurableSet_Icc fun θ _ => hpt θ
    rw [hcongr, MeasureTheory.integral_sub h1int (h2int.const_mul _),
      MeasureTheory.integral_const_mul, Work.Elliptic.integral_sin_two_mul_sinCos2]
    simp only [Work.Elliptic.Fstar]
    ring
  · exact MeasureTheory.integral_undef hint


end Work.FTS.EllipticEst
