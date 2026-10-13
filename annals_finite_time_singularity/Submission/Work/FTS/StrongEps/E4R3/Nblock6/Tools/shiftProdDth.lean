import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBdDefs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Tools.shiftProdDth` — the `D_θ` shift-product bound of the level-`6` `N`-block

`HkSq α 6 (A · D_θ f) ≤ C (MA² (1 + HkSq α 7 f) + (1 + (γ-1)⁻¹ (HkSq α 6 A + HkSq α 6 f))
  (HkSq α 6 A + HkSq α 6 f))`,

from the pointwise master bound `PtBdDth` (proved in `Tools/ptBoundDth.lean`) and the
exceptional-pair bound `N6Trans.T1SixAux.excDz5_mixed_pair_bound`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- **The `D_θ` shift-product bound** from the pointwise master bound. -/
theorem shiftProdDth_of (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hB : PtBdDth α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨K, hK, hBd⟩ := hB
  obtain ⟨Csp, hCsppos, hsp⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound 0 2 (by norm_num)
      (by norm_num)
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hgnn10 : (10 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ := ten_le_inv_gam_sub_one hα hα1
  refine ⟨2 * (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹) + 1, by positivity, ?_⟩
  intro A f MA hsmA hsmf hmA hmf hmf7 hMA
  have hA6 : 0 ≤ Work.Spaces.HkSq α 6 A := Work.Spaces.HkSq_nonneg α 6 A
  have hF6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hF7 : 0 ≤ Work.Spaces.HkSq α 7 f := Work.Spaces.HkSq_nonneg α 7 f
  have hMA2 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have hgnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  obtain ⟨hspmem, hspbd⟩ := hsp α A f hα hα1 hsmA hmA hsmf hmf
  -- abbreviations
  set S : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
      * Work.Spaces.Wt α z θ with hSdef
  -- the pointwise bound
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * (S z θ) ^ 2 := by
    intro z θ hz hθ hθ'
    have h := hBd A f MA hsmA hsmf hmA hmf hmf7 hMA z θ hz hθ hθ'
    have hS : S z θ = Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ := by rw [hSdef]
    rw [hS] at *
    rw [← hS]
    exact h
  -- the θ-slice integrability of the majorant at each positive `z`
  have hGint : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ => K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
      + K * (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
      + K * (S z θ) ^ 2) Iθ := by
    intro z hz
    have hzI : z ∈ Iz := hz.le
    exact (((hmf7.1 z hzI).const_mul _).add
      (((hmA.1 z hzI).add (hmf.1 z hzI)).const_mul _)).add ((hspmem.1 z hzI).const_mul _)
  -- the θ-integral evaluated
  have hGeq : ∀ z : ℝ, 0 < z → (∫ θ in Iθ,
        (K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * (S z θ) ^ 2))
      = K * MA ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
            + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        + K * (∫ θ in Iθ, (S z θ) ^ 2) := by
    intro z hz
    have hzI : z ∈ Iz := hz.le
    have h1 : Integrable (fun θ => K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ)
        (volume.restrict Iθ) := (hmf7.1 z hzI).const_mul _
    have h2 : Integrable (fun θ => K * (1 + (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
        (volume.restrict Iθ) := ((hmA.1 z hzI).add (hmf.1 z hzI)).const_mul _
    have h3 : Integrable (fun θ => K * (S z θ) ^ 2) (volume.restrict Iθ) :=
      (hspmem.1 z hzI).const_mul _
    rw [integral_add_three h1 h2 h3]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add (hmA.1 z hzI) (hmf.1 z hzI)]
  -- the θ-bound at each positive `z`
  have hinner : ∀ z : ℝ, 0 < z → (∫ θ in Iθ,
        Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ)
      ≤ K * MA ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
            + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        + K * (∫ θ in Iθ, (S z θ) ^ 2) := by
    intro z hz
    rw [← hGeq z hz]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (hGint z hz) ?_
    filter_upwards [ae_mem_Ioo_Iθ_fts] with θ hθ
    exact hpt z θ hz hθ.1 hθ.2
  -- the exceptional-term bound
  have hsp' : Work.Spaces.L2Sq S ≤ Csp * (Work.Spaces.gam α - 1)⁻¹
      * Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f := by
    have hSe : S = fun z θ => Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ := by
      funext z θ; rw [hSdef]
    rw [hSe]
    calc Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 A z θ
            * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ)
        ≤ Csp / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A
            * Work.Spaces.HkSq α 6 f := hspbd
      _ = Csp * (Work.Spaces.gam α - 1)⁻¹ * Work.Spaces.HkSq α 6 A
            * Work.Spaces.HkSq α 6 f := by rw [div_eq_mul_inv]
  -- main inequality
  have hmain : Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ)
      ≤ K * MA ^ 2 * Work.Spaces.HkSq α 7 f
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
        + K * Work.Spaces.L2Sq S := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq,
      Work.Spaces.L2Sq]
    have h1 : IntegrableOn (fun z => K * MA ^ 2
        * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)) Iz := hmf7.2.const_mul _
    have h2 : IntegrableOn (fun z => K * (1 + (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
          + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))) Iz :=
      (hmA.2.add hmf.2).const_mul _
    have h3 : IntegrableOn (fun z => K * (∫ θ in Iθ, (S z θ) ^ 2)) Iz :=
      hspmem.2.const_mul _
    have hθ_int : IntegrableOn (fun z => K * MA ^ 2
        * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
            + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        + K * (∫ θ in Iθ, (S z θ) ^ 2)) Iz := (h1.add h2).add h3
    have hstep : (∫ z in Iz, ∫ θ in Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ)
        ≤ ∫ z in Iz, (K * MA ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
            + K * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
                + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
            + K * (∫ θ in Iθ, (S z θ) ^ 2)) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hθ_int ?_
      filter_upwards [ae_mem_Ioi_Iz_fts] with z hz
      exact hinner z hz
    calc (∫ z in Iz, ∫ θ in Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ)
        ≤ _ := hstep
      _ = K * MA ^ 2 * (∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * ((∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
              + (∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
          + K * (∫ z in Iz, ∫ θ in Iθ, (S z θ) ^ 2) := by
        rw [integral_add_three_z h1 h2 h3]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_add hmA.2 hmf.2]
  -- arithmetic
  have hspnn : 0 ≤ Work.Spaces.L2Sq S := by
    rw [Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hAF : Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f
      ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := by
    have h1 : 4 * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f)
        ≤ (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.HkSq α 6 A - Work.Spaces.HkSq α 6 f)]
    have h3 : 0 ≤ (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := sq_nonneg _
    have h4 : 40 * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f)
        ≤ (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := by
      nlinarith [h1, hgnn10, h3, mul_nonneg (sub_nonneg.mpr hgnn10) h3]
    have h5 : (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
        = (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
          + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := by ring
    have h6 : 0 ≤ Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f := by linarith
    nlinarith [h4, h5, h6]
  have hspnn' : 0 ≤ Csp * (Work.Spaces.gam α - 1)⁻¹ * Work.Spaces.HkSq α 6 A
      * Work.Spaces.HkSq α 6 f := by positivity
  have hmid : Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f
      ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := hAF
  -- the two "cA"-terms bound
  set LB : ℝ := K * MA ^ 2 * Work.Spaces.HkSq α 7 f
      + K * (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
      + K * Work.Spaces.L2Sq S with hLBdef
  have hkey : LB ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
      * (MA ^ 2 * Work.Spaces.HkSq α 7 f
        + (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
    have hL2 : K * Work.Spaces.L2Sq S ≤ K * (Csp * (Work.Spaces.gam α - 1)⁻¹
        * Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left hsp' hK.le
    have hKC : 0 ≤ K * Csp * (Work.Spaces.gam α - 1)⁻¹ := by positivity
    have hcA_nn : 0 ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := by positivity
    have hAF' : Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f
        ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := hAF
    have hmn : 0 ≤ MA ^ 2 * Work.Spaces.HkSq α 7 f := mul_nonneg hMA2 hF7
    rw [hLBdef]
    have hsum1 : K * MA ^ 2 * Work.Spaces.HkSq α 7 f
        ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
          * (MA ^ 2 * Work.Spaces.HkSq α 7 f) := by
      nlinarith [hmn, hK.le, hKC]
    have hsum2 : K * (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
        + K * (Csp * (Work.Spaces.gam α - 1)⁻¹ * Work.Spaces.HkSq α 6 A
            * Work.Spaces.HkSq α 6 f)
        ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
          * ((1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
      have hCspnn : 0 ≤ Csp * (Work.Spaces.gam α - 1)⁻¹ := by positivity
      have hstep : K * (Csp * (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f))
          ≤ K * (Csp * (Work.Spaces.gam α - 1)⁻¹
            * ((1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK.le
        exact mul_le_mul_of_nonneg_left hAF' hCspnn
      nlinarith [hstep, hcA_nn, hK.le, hKC]
    linarith [hsum1, hsum2]
  calc Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) ≤ LB := hmain
    _ ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
        * (MA ^ 2 * Work.Spaces.HkSq α 7 f
          + (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := hkey
    _ ≤ (2 * (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹) + 1)
        * (MA ^ 2 * Work.Spaces.HkSq α 7 f
          + (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
        have hb : 0 ≤ MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := by positivity
        have hKC : 0 ≤ K + K * Csp * (Work.Spaces.gam α - 1)⁻¹ := by positivity
        nlinarith [hb, hKC]


/-- **The `D_θ` shift-product bound**, instantiated at `ptBoundDth`. -/
theorem shiftProdDth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) :=
  shiftProdDth_of α hα hα1 (ptBoundDth α hα hα1)

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
