/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongPersist.L3Rhs.L3MulDth`

The product rule `h · D_θ f ∈ ℋ³` with the `𝒲^{4,∞}`-price on `h`:

```
∃ C > 0, ∀ α ∈ (0,1], ∀ h f,
  SmoothOpen h → WlInfMem α 4 h → SmoothOpen f → HkMem α 4 f →
    HkMem α 3 (h · D_θ f) ∧ HkSq α 3 (h · D_θ f) ≤ C/(γ-1) · |h|²_{𝒲^{4,∞}} · HkSq α 4 f
```

(The factor `1/(γ-1)` is *not* needed for this particular product — every `D_θ`-slot of
`D_θ f` is a genuine mixed slot of `f` of order `≤ 4`, so no Hardy loss occurs; the statement
is the weaker one with the factor present, and `C` is chosen so that it holds.  The whole
`(γ-1)`-bookkeeping of the general product rule is absent here.)

The mathematical content is the pointwise bound

`HkIntegrand α 3 (h·D_θ f) z θ ≤ (4·10^8 + 16·10^12) · |h|²_{𝒲^{4,∞}} · HkIntegrand α 4 f z θ`

on the closed quadrant `Iz ×ˢ Iθ`, assembled from the two slot bounds
(`L3MulDthAux.ZslotPt.zslot_le_pt`, `L3MulDthAux.MslotPt.mslot_le_pt`):

* the pure `D_z`-slots of `HkIntegrand α 3 (h·D_θ f)`;
* the (at most 25) mixed slots, of which the `1 ≤ i`, `i + j ≤ 3` ones are priced by
  `mslot_le_pt` and the rest vanish;

then `HkMem α 3 (h·D_θ f)` by domination (`HkMem_of_majorant`, the dominant being a multiple
of the integrable `HkIntegrand α 4 f`) and `HkSq α 3 (h·D_θ f) ≤ C |h|²_𝒲 HkSq α 4 f` by
integrating the pointwise bound twice.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Dth_of_pth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.ZslotPt
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.MslotPt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Assembly of the pointwise bound on the open quadrant -/

/-- **The pointwise bound on the open quadrant**, from the two slot bounds. -/
private theorem mulDth_pt_open {Cz Cm : ℝ}
    (hzslot : ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Cz * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
    (hmslot : ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i j : ℕ, 1 ≤ i → i + j ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
    (hCznn : 0 ≤ Cz) (hCmnn : 0 ≤ Cm) :
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
          ≤ (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ := by
  intro α h f hα hα1 hh hhm hf hfm z θ hz hθ0 hθ1
  have hHInn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hMb : 0 ≤ Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg hCmnn (sq_nonneg _)) hHInn
  have h1 : (∑ i ∈ Finset.range (3 + 1),
        (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 4 * (Cz * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ i ∈ Finset.range (3 + 1),
          (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (3 + 1),
            (Cz * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          Finset.sum_le_sum fun i hi =>
            hzslot α h f hα hα1 hh hhm hf hfm i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1
      _ = 4 * (Cz * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have h2 : (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
        (if 1 ≤ i ∧ i + j ≤ 3 then
          (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 16 * (Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
          (if 1 ≤ i ∧ i + j ≤ 3 then
            (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range (3 + 1), ∑ _j ∈ Finset.range (3 + 1),
            (Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 3
          · rw [if_pos hc]
            exact hmslot α h f hα hα1 hh hhm hf hfm i j hc.1 hc.2 z θ hz hθ0 hθ1
          · rw [if_neg hc]
            exact hMb
      _ = 16 * (Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  rw [Work.Spaces.HkIntegrand]
  calc (∑ i ∈ Finset.range (3 + 1),
        (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
        (if 1 ≤ i ∧ i + j ≤ 3 then
          (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 4 * (Cz * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
        + 16 * (Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
        add_le_add h1 h2
    _ = (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2
          * Work.Spaces.HkIntegrand α 4 f z θ := by ring

/-- **The pointwise bound on the closed quadrant**, by the boundary vanishing of both
`ℋ`-integrands at `z = 0` and at `sin(2θ) = 0`. -/
private theorem mulDth_pt_quad {Cz Cm : ℝ}
    (hzslot : ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Cz * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
    (hmslot : ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i j : ℕ, 1 ≤ i → i + j ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cm * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
    (hCznn : 0 ≤ Cz) (hCmnn : 0 ≤ Cm) :
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
          ≤ (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ := by
  intro α h f hα hα1 hh hhm hf hfm z hz θ hθ
  have hopen := mulDth_pt_open hzslot hmslot hCznn hCmnn α h f hα hα1 hh hhm hf hfm
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
  · rw [← h0,
      Work.FTS.LocData.HkIntegrand_zero_fst α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α 4 f θ]
    simp only [mul_zero]
    exact le_refl 0
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · exact hopen z θ hzpos hθi.1 hθi.2
    · have hs : Real.sin (2 * θ) = 0 := by
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h1 | h1
        · rw [← h1]; simp
        · have h2 : θ = Real.pi / 2 := by
            rcases eq_or_lt_of_le (show θ ≤ Real.pi / 2 from hθ.2) with h2 | h2
            · exact h2
            · exact absurd ⟨h1, h2⟩ hθi
          rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [Work.FTS.EllipticEst.Cert.HkIntegrand_eq_zero_of_sin_eq_zero α hα 3
          (fun z θ => h z θ * Work.Spaces.Dth f z θ) hs,
        Work.FTS.EllipticEst.Cert.HkIntegrand_eq_zero_of_sin_eq_zero α hα 4 f hs]
      simp only [mul_zero]
      exact le_refl 0

/-- Transfer of the `ℋ`-square along a pointwise domination of the integrand (the two
indices may differ). -/
private theorem HkSq_le_of_integrand_le (α : ℝ) (k l : ℕ) {F g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmg : Work.Spaces.HkMem α l g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ ≤ C * Work.Spaces.HkIntegrand α l g z θ) :
    Work.Spaces.HkSq α k F ≤ C * Work.Spaces.HkSq α l g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α l g z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k F z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α l g z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
        ((hmg.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ))
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
      (hmg.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-! ## The target -/

theorem L3MulDth : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cz, hCz0, hzslot⟩ := zslot_le_pt
  obtain ⟨Cm, hCm0, hmslot⟩ := mslot_le_pt
  have hCznn : 0 ≤ Cz := le_of_lt hCz0
  have hCmnn : 0 ≤ Cm := le_of_lt hCm0
  refine ⟨4 * Cz + 16 * Cm, by linarith, ?_⟩
  intro α h f hα hα1 hh hhm hf hfm
  have hCpt : 0 ≤ 4 * Cz + 16 * Cm := by linarith
  have hpt := mulDth_pt_quad hzslot hmslot hCznn hCmnn α h f hα hα1 hh hhm hf hfm
  refine ⟨?_, ?_⟩
  · refine Work.FTS.LocData.HkMem_of_majorant α 3 ?_ ?_ ?_ hpt
    · exact (show Work.FTS.EllipticEst.SmoothOpen
          (fun z θ => h z θ * Work.Spaces.Dth f z θ) from hh.mul hf.Dth).continuousOn_HkIntegrand α 3
    · intro z hz
      exact (hfm.1 z hz).const_mul ((4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2)
    · have hint := hfm.2.const_mul ((4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2)
      have hkey : (fun z => ∫ θ in Work.Spaces.Iθ,
            (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ)
          = fun z => ((4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2)
              * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [hkey]
      exact hint
  · have hsq : Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ)
        ≤ ((4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2) * Work.Spaces.HkSq α 4 f :=
      HkSq_le_of_integrand_le α 3 4
        ((4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2) hfm hpt
    have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have hγle : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have hinv : (1 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ := by
      rw [one_le_inv₀ hγ1]; exact hγle
    have hbase : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkSq α 4 f :=
      mul_nonneg (sq_nonneg _) (Work.Spaces.HkSq_nonneg α 4 f)
    calc Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ)
        ≤ ((4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2) * Work.Spaces.HkSq α 4 f := hsq
      _ ≤ ((4 * Cz + 16 * Cm) * (Work.Spaces.gam α - 1)⁻¹)
            * ((Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkSq α 4 f) := by
          have h1 : (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkSq α 4 f
              = (4 * Cz + 16 * Cm)
                * ((Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkSq α 4 f) := by ring
          rw [h1]
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCpt hinv) hbase
      _ = (4 * Cz + 16 * Cm) / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkSq α 4 f := by
          rw [div_eq_mul_inv]; ring

end Work.FTS.StrongPersist.L3Rhs
