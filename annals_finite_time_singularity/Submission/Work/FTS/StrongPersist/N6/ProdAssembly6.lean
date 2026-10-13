/-
# `Work.FTS.StrongPersist.N6.ProdAssembly6`

The **measure-theoretic assembly** of the level-six product rule: the level-six shift of
`Submission/Work/FTS/OpenPkg/prod_field.lean`.

* `aesm_sliceIntegral6` — a.e. strong measurability of a partially integrated slice;
* `HkSq_prod_bound_of6` — given the pointwise majorant of `HkIntegrand α 6 (f·g)` and the two
  bounds on the exceptional `(5,1)`-terms, the product is in `ℋ⁶` and
  `|f g|²_{ℋ⁶} ≤ C (γ-1)⁻¹ |f|²_{ℋ⁶}|g|²_{ℋ⁶}`;
* `prod_field_of6` — the same, converted to the stated `Xn`-form with the `α^{-1/2}`-loss.

`Submission/Work/FTS/StrongPersist/N6/Prod6.lean` instantiates the two analytic inputs with
`prod_majorant6` and `exc_bound6` and concludes `prod_field6`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The a.e. strong measurability of a partially integrated slice -/

/-- The partially integrated function of a datum continuous on the open quadrant is a.e.
strongly measurable on `Iz`. -/
theorem aesm_sliceIntegral6 {F : ℝ → ℝ → ℝ} (hcont : ContinuousOn (Function.uncurry F) Q0) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Iθ, F z θ) (volume.restrict Iz) := by
  have h : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry F) hcont
  have h2 := h.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only [Function.uncurry] using h2

/-! ## The measure-theoretic assembly -/

theorem HkSq_prod_bound_of6 {α K Ce : ℝ} {f g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : SmoothOpen f) (hmemF : HkMem α 6 f) (hG : SmoothOpen g) (hmemG : HkMem α 6 g)
    (hK : 0 < K) (hCe : 0 < Ce)
    (hmaj : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K / (gam α - 1) * (HkSq α 6 f * HkIntegrand α 6 g z θ
            + HkSq α 6 g * HkIntegrand α 6 f z θ)
          + K * ((DzIter 5 f z θ * Dth g z θ) ^ 2
              + (Dth f z θ * DzIter 5 g z θ) ^ 2) * (Wt α z θ) ^ 2)
    (hexcA : L2Mem (fun z θ => DzIter 5 f z θ * Dth g z θ * Wt α z θ))
    (hexcAs : L2Sq (fun z θ => DzIter 5 f z θ * Dth g z θ * Wt α z θ)
        ≤ Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g)
    (hexcB : L2Mem (fun z θ => Dth f z θ * DzIter 5 g z θ * Wt α z θ))
    (hexcBs : L2Sq (fun z θ => Dth f z θ * DzIter 5 g z θ * Wt α z θ)
        ≤ Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g) :
    HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      HkSq α 6 (fun z θ => f z θ * g z θ)
        ≤ (2 * K + 2 * (K * Ce)) / (gam α - 1) * HkSq α 6 f * HkSq α 6 g := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hHkF : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  have hHkG : 0 ≤ HkSq α 6 g := HkSq_nonneg α 6 g
  have hFGso : SmoothOpen (fun z θ => f z θ * g z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF hG
  set A : ℝ → ℝ → ℝ := fun z θ => DzIter 5 f z θ * Dth g z θ * Wt α z θ with hAdef
  set B : ℝ → ℝ → ℝ := fun z θ => Dth f z θ * DzIter 5 g z θ * Wt α z θ with hBdef
  have hAval : ∀ z θ, A z θ = DzIter 5 f z θ * Dth g z θ * Wt α z θ := fun z θ => rfl
  have hBval : ∀ z θ, B z θ = Dth f z θ * DzIter 5 g z θ * Wt α z θ := fun z θ => rfl
  have hA1 : ∀ z ∈ Iz, IntegrableOn (fun θ => (A z θ) ^ 2) Iθ := hexcA.1
  have hA2 : IntegrableOn (fun z => ∫ θ in Iθ, (A z θ) ^ 2) Iz := hexcA.2
  have hB1 : ∀ z ∈ Iz, IntegrableOn (fun θ => (B z θ) ^ 2) Iθ := hexcB.1
  have hB2 : IntegrableOn (fun z => ∫ θ in Iθ, (B z θ) ^ 2) Iz := hexcB.2
  set M : ℝ → ℝ → ℝ := fun z θ =>
      (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
      + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ
      + K * ((A z θ) ^ 2 + (B z θ) ^ 2) with hMdef
  have hMval : ∀ z θ, M z θ =
      (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
      + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ
      + K * ((A z θ) ^ 2 + (B z θ) ^ 2) := fun z θ => rfl
  -- the zero slice at `z = 0`
  have hzero_Hk : ∀ (h : ℝ → ℝ → ℝ) (θ : ℝ), HkIntegrand α 6 h 0 θ = 0 := by
    intro h θ
    simp [HkIntegrand, Wt, w]
  -- (1) the pointwise majorisation
  have hpt : ∀ z θ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ ≤ M z θ := by
    intro z θ hz hθ
    have hMeq : M z θ = K / (gam α - 1) * (HkSq α 6 f * HkIntegrand α 6 g z θ
          + HkSq α 6 g * HkIntegrand α 6 f z θ)
        + K * ((DzIter 5 f z θ * Dth g z θ) ^ 2
            + (Dth f z θ * DzIter 5 g z θ) ^ 2) * (Wt α z θ) ^ 2 := by
      rw [hMval z θ, hAval z θ, hBval z θ]; ring
    rw [hMeq]
    exact hmaj z θ hz hθ.1 hθ.2
  -- (2) integrability of the angular slices of the majorant
  have hMslice : ∀ z ∈ Iz, IntegrableOn (fun θ => M z θ) Iθ := by
    intro z hz
    have h1 := hmemG.1 z hz
    have h2 := hmemF.1 z hz
    have h3 := hA1 z hz
    have h4 := hB1 z hz
    have hfun : (fun θ => M z θ) = fun θ =>
        (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
        + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ
        + K * ((A z θ) ^ 2 + (B z θ) ^ 2) := funext fun θ => hMval z θ
    rw [hfun]
    exact ((h1.const_mul _).add (h2.const_mul _)).add ((h3.add h4).const_mul K)
  -- (3) the angular integral of the majorant
  have hinner : ∀ z ∈ Iz, (∫ θ in Iθ, M z θ)
      = (K / (gam α - 1) * HkSq α 6 f) * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
        + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ)
        + K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2)) := by
    intro z hz
    have hfun : (fun θ => M z θ) = fun θ =>
        (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
        + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ
        + K * ((A z θ) ^ 2 + (B z θ) ^ 2) := funext fun θ => hMval z θ
    have hI1 : Integrable (fun θ : ℝ =>
        (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ) (volume.restrict Iθ) :=
      (hmemG.1 z hz).const_mul (K / (gam α - 1) * HkSq α 6 f)
    have hI2 : Integrable (fun θ : ℝ =>
        (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ) (volume.restrict Iθ) :=
      (hmemF.1 z hz).const_mul (K / (gam α - 1) * HkSq α 6 g)
    have hI3 : Integrable (fun θ : ℝ => (A z θ) ^ 2) (volume.restrict Iθ) := hA1 z hz
    have hI4 : Integrable (fun θ : ℝ => (B z θ) ^ 2) (volume.restrict Iθ) := hB1 z hz
    have hI12 : Integrable (fun θ : ℝ =>
        (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
        + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ) (volume.restrict Iθ) :=
      hI1.add hI2
    have hI34 : Integrable (fun θ : ℝ => (A z θ) ^ 2 + (B z θ) ^ 2) (volume.restrict Iθ) :=
      hI3.add hI4
    have hI012 : Integrable (fun θ : ℝ => K * ((A z θ) ^ 2 + (B z θ) ^ 2))
        (volume.restrict Iθ) := hI34.const_mul K
    have hB1' : (∫ θ in Iθ, ((K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
          + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ
          + K * ((A z θ) ^ 2 + (B z θ) ^ 2)))
        = (∫ θ in Iθ, ((K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
              + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ))
          + (∫ θ in Iθ, K * ((A z θ) ^ 2 + (B z θ) ^ 2)) :=
      MeasureTheory.integral_add hI12 hI012
    have hB2' : (∫ θ in Iθ, ((K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ
              + (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ))
        = (∫ θ in Iθ, (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ)
          + (∫ θ in Iθ, (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ) :=
      MeasureTheory.integral_add hI1 hI2
    have hB3' : (∫ θ in Iθ, K * ((A z θ) ^ 2 + (B z θ) ^ 2))
        = K * (∫ θ in Iθ, ((A z θ) ^ 2 + (B z θ) ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    have hB4' : (∫ θ in Iθ, ((A z θ) ^ 2 + (B z θ) ^ 2))
        = (∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2) :=
      MeasureTheory.integral_add hI3 hI4
    have hB5' : (∫ θ in Iθ, (K / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ)
        = (K / (gam α - 1) * HkSq α 6 f) * (∫ θ in Iθ, HkIntegrand α 6 g z θ) := by
      rw [MeasureTheory.integral_const_mul]
    have hB6' : (∫ θ in Iθ, (K / (gam α - 1) * HkSq α 6 g) * HkIntegrand α 6 f z θ)
        = (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ) := by
      rw [MeasureTheory.integral_const_mul]
    rw [hfun, hB1', hB2', hB3', hB4', hB5', hB6']
  -- (4) integrability of the `z`-integral of the majorant
  have hM2 : IntegrableOn (fun z => ∫ θ in Iθ, M z θ) Iz := by
    have hbase : Integrable (fun z =>
        (K / (gam α - 1) * HkSq α 6 f) * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
        + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ)
        + K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2)))
        (volume.restrict Iz) :=
      ((hmemG.2.const_mul _).add (hmemF.2.const_mul _)).add ((hA2.add hB2).const_mul K)
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => hinner z hz)] with z hz
    exact hz.symm
  -- (5) the iterated integral of the majorant
  have hMint : (∫ z in Iz, ∫ θ in Iθ, M z θ)
      = (K / (gam α - 1) * HkSq α 6 f) * HkSq α 6 g
        + (K / (gam α - 1) * HkSq α 6 g) * HkSq α 6 f
        + K * (L2Sq A + L2Sq B) := by
    have h1 : (∫ z in Iz, ∫ θ in Iθ, M z θ)
        = ∫ z in Iz, ((K / (gam α - 1) * HkSq α 6 f) * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
            + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ)
            + K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici ?_
      intro z hz
      exact hinner z hz
    rw [h1]
    have hJ1 : Integrable (fun z : ℝ => (K / (gam α - 1) * HkSq α 6 f)
        * (∫ θ in Iθ, HkIntegrand α 6 g z θ)) (volume.restrict Iz) :=
      hmemG.2.const_mul (K / (gam α - 1) * HkSq α 6 f)
    have hJ2 : Integrable (fun z : ℝ => (K / (gam α - 1) * HkSq α 6 g)
        * (∫ θ in Iθ, HkIntegrand α 6 f z θ)) (volume.restrict Iz) :=
      hmemF.2.const_mul (K / (gam α - 1) * HkSq α 6 g)
    have hJ3 : Integrable (fun z : ℝ =>
        (∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2)) (volume.restrict Iz) :=
      hA2.add hB2
    have hJ3' : Integrable (fun z : ℝ =>
        K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2))) (volume.restrict Iz) :=
      hJ3.const_mul K
    have hJ12 : Integrable (fun z : ℝ =>
        (K / (gam α - 1) * HkSq α 6 f) * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
        + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ))
        (volume.restrict Iz) := hJ1.add hJ2
    have hK1 : (∫ z in Iz, ((K / (gam α - 1) * HkSq α 6 f)
            * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
            + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ)
            + K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2))))
        = (∫ z in Iz, ((K / (gam α - 1) * HkSq α 6 f)
              * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
              + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ)))
          + (∫ z in Iz, K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2))) :=
      MeasureTheory.integral_add hJ12 hJ3'
    have hK2 : (∫ z in Iz, ((K / (gam α - 1) * HkSq α 6 f)
              * (∫ θ in Iθ, HkIntegrand α 6 g z θ)
              + (K / (gam α - 1) * HkSq α 6 g) * (∫ θ in Iθ, HkIntegrand α 6 f z θ)))
        = (∫ z in Iz, (K / (gam α - 1) * HkSq α 6 f)
              * (∫ θ in Iθ, HkIntegrand α 6 g z θ))
          + (∫ z in Iz, (K / (gam α - 1) * HkSq α 6 g)
              * (∫ θ in Iθ, HkIntegrand α 6 f z θ)) :=
      MeasureTheory.integral_add hJ1 hJ2
    have hK3 : (∫ z in Iz, K * ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2)))
        = K * (∫ z in Iz, ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2))) := by
      rw [MeasureTheory.integral_const_mul]
    have hK4 : (∫ z in Iz, ((∫ θ in Iθ, (A z θ) ^ 2) + (∫ θ in Iθ, (B z θ) ^ 2)))
        = (∫ z in Iz, ∫ θ in Iθ, (A z θ) ^ 2)
          + (∫ z in Iz, ∫ θ in Iθ, (B z θ) ^ 2) :=
      MeasureTheory.integral_add hA2 hB2
    have hK5 : (∫ z in Iz, (K / (gam α - 1) * HkSq α 6 f)
            * (∫ θ in Iθ, HkIntegrand α 6 g z θ))
        = (K / (gam α - 1) * HkSq α 6 f) * (∫ z in Iz, ∫ θ in Iθ, HkIntegrand α 6 g z θ) := by
      rw [MeasureTheory.integral_const_mul]
    have hK6 : (∫ z in Iz, (K / (gam α - 1) * HkSq α 6 g)
            * (∫ θ in Iθ, HkIntegrand α 6 f z θ))
        = (K / (gam α - 1) * HkSq α 6 g) * (∫ z in Iz, ∫ θ in Iθ, HkIntegrand α 6 f z θ) := by
      rw [MeasureTheory.integral_const_mul]
    rw [hK1, hK2, hK3, hK4, hK5, hK6]
    rfl
  -- (6) the a.e. bound of the slices of the product
  have hslice_le : (fun z : ℝ => ∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
      ≤ᵐ[volume.restrict Iz] (fun z : ℝ => ∫ θ in Iθ, M z θ) := by
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => HkIntegrand_nonneg α 6 _ z θ) (hMslice z hz.le) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
    exact hpt z θ hz hθ
  -- (7) the bound
  have hbound : HkSq α 6 (fun z θ => f z θ * g z θ)
      ≤ (2 * K + 2 * (K * Ce)) / (gam α - 1) * HkSq α 6 f * HkSq α 6 g := by
    have hstep : HkSq α 6 (fun z θ => f z θ * g z θ) ≤ ∫ z in Iz, ∫ θ in Iθ, M z θ := by
      show (∫ z in Iz, ∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) ≤ _
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
          HkIntegrand_nonneg α 6 _ z θ) hM2 hslice_le
    refine le_trans hstep ?_
    rw [hMint]
    have hAs : L2Sq A ≤ Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g := hexcAs
    have hBs : L2Sq B ≤ Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g := hexcBs
    have hsum : L2Sq A + L2Sq B ≤ 2 * (Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g) := by
      linarith
    have halg : (2 * K + 2 * (K * Ce)) / (gam α - 1) * HkSq α 6 f * HkSq α 6 g
        = (K / (gam α - 1) * HkSq α 6 f) * HkSq α 6 g
          + (K / (gam α - 1) * HkSq α 6 g) * HkSq α 6 f
          + K * (2 * (Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g)) := by
      field_simp
      ring
    rw [halg]
    have h1 : K * (L2Sq A + L2Sq B)
        ≤ K * (2 * (Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g)) :=
      mul_le_mul_of_nonneg_left hsum hK.le
    linarith
  refine ⟨⟨?_, ?_⟩, hbound⟩
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have h1 : (fun θ : ℝ => HkIntegrand α 6 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) := funext fun θ =>
        hzero_Hk (fun z θ => f z θ * g z θ) θ
      rw [h1]
      exact integrableOn_zero
    · refine Integrable.mono' (hMslice z hz) ?_ ?_
      · refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
        have hmap : Continuous fun θ : ℝ => (z, θ) := continuous_const.prodMk continuous_id
        exact (hFGso.continuousOn_HkIntegrand α 6).comp hmap.continuousOn
          (fun θ hθ => mem_Q0.mpr ⟨hpos, hθ.1, hθ.2⟩)
      · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
        rw [Real.norm_of_nonneg (HkIntegrand_nonneg α 6 _ z θ)]
        exact hpt z θ hpos hθ
  · refine Integrable.mono' hM2 ?_ ?_
    · exact aesm_sliceIntegral6 (F := fun z θ => HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        (hFGso.continuousOn_HkIntegrand α 6)
    · filter_upwards [hslice_le] with z hz
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => HkIntegrand_nonneg α 6 _ z θ)]
      exact hz

/-! ## The conversion `HkSq` ↠ the stated `Xn`-form -/

/-- `(α^{-1/2})² = α^{-1}`. -/
theorem rpow_neg_half_sq6 {α : ℝ} (hα : 0 < α) :
    (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
  rw [sq, ← Real.rpow_add hα, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by ring,
    Real.rpow_neg_one]

/-- **The target from the two analytic inputs.** -/
theorem prod_field_of6
    (hMaj : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      SmoothOpen f → HkMem α 6 f → SmoothOpen g → HkMem α 6 g →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
          ≤ K / (gam α - 1) * (HkSq α 6 f * HkIntegrand α 6 g z θ
              + HkSq α 6 g * HkIntegrand α 6 f z θ)
            + K * ((DzIter 5 f z θ * Dth g z θ) ^ 2
                + (Dth f z θ * DzIter 5 g z θ) ^ 2) * (Wt α z θ) ^ 2)
    (hExc : ∃ Ce : ℝ, 0 < Ce ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      SmoothOpen f → HkMem α 6 f → SmoothOpen g → HkMem α 6 g →
      (L2Mem (fun z θ => DzIter 5 f z θ * Dth g z θ * Wt α z θ) ∧
        L2Sq (fun z θ => DzIter 5 f z θ * Dth g z θ * Wt α z θ)
          ≤ Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g)
      ∧ (L2Mem (fun z θ => Dth f z θ * DzIter 5 g z θ * Wt α z θ) ∧
        L2Sq (fun z θ => Dth f z θ * DzIter 5 g z θ * Wt α z θ)
          ≤ Ce / (gam α - 1) * HkSq α 6 f * HkSq α 6 g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f * HkNorm α 6 g := by
  obtain ⟨K, hK, hmaj⟩ := hMaj
  obtain ⟨Ce, hCe, hexc⟩ := hExc
  have hDpos : 0 < 2 * K + 2 * (K * Ce) := by positivity
  refine ⟨Real.sqrt (10 * (2 * K + 2 * (K * Ce))) + 1, by positivity, ?_⟩
  intro α hα hα1 f g hf hg
  obtain ⟨hsoF, hmemF⟩ := hf
  obtain ⟨hsoG, hmemG⟩ := hg
  obtain ⟨⟨hexcA, hexcAs⟩, hexcB, hexcBs⟩ := hexc α f g hα hα1 hsoF hmemF hsoG hmemG
  obtain ⟨hmem, hsq⟩ := HkSq_prod_bound_of6 hα hα1 hsoF hmemF hsoG hmemG hK hCe
    (hmaj α f g hα hα1 hsoF hmemF hsoG hmemG) hexcA hexcAs hexcB hexcBs
  refine ⟨hmem, ?_⟩
  have hFnn : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  have hGnn : 0 ≤ HkSq α 6 g := HkSq_nonneg α 6 g
  have hRnn : 0 ≤ Real.sqrt (10 * (2 * K + 2 * (K * Ce))) * α ^ (-(1 / 2 : ℝ))
      * HkNorm α 6 f * HkNorm α 6 g := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (10 * (2 * K + 2 * (K * Ce))) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h3 : (0 : ℝ) ≤ HkNorm α 6 f := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ HkNorm α 6 g := Real.sqrt_nonneg _
    positivity
  have hsq' : HkSq α 6 (fun z θ => f z θ * g z θ)
      ≤ (Real.sqrt (10 * (2 * K + 2 * (K * Ce))) * α ^ (-(1 / 2 : ℝ))
          * HkNorm α 6 f * HkNorm α 6 g) ^ 2 := by
    have hfac : (2 * K + 2 * (K * Ce)) / (gam α - 1)
        = 10 * (2 * K + 2 * (K * Ce)) * α⁻¹ := by
      rw [gam_sub_one]; field_simp
    have hR2 : (Real.sqrt (10 * (2 * K + 2 * (K * Ce))) * α ^ (-(1 / 2 : ℝ))
          * HkNorm α 6 f * HkNorm α 6 g) ^ 2
        = 10 * (2 * K + 2 * (K * Ce)) * α⁻¹ * HkSq α 6 f * HkSq α 6 g := by
      have h3 : (HkNorm α 6 f) ^ 2 = HkSq α 6 f := by
        rw [show HkNorm α 6 f = Real.sqrt (HkSq α 6 f) from rfl, Real.sq_sqrt hFnn]
      have h4 : (HkNorm α 6 g) ^ 2 = HkSq α 6 g := by
        rw [show HkNorm α 6 g = Real.sqrt (HkSq α 6 g) from rfl, Real.sq_sqrt hGnn]
      calc (Real.sqrt (10 * (2 * K + 2 * (K * Ce))) * α ^ (-(1 / 2 : ℝ))
            * HkNorm α 6 f * HkNorm α 6 g) ^ 2
          = (Real.sqrt (10 * (2 * K + 2 * (K * Ce)))) ^ 2
              * (α ^ (-(1 / 2 : ℝ))) ^ 2
              * (HkNorm α 6 f) ^ 2 * (HkNorm α 6 g) ^ 2 := by ring
        _ = 10 * (2 * K + 2 * (K * Ce)) * α⁻¹ * HkSq α 6 f * HkSq α 6 g := by
            rw [h3, h4, rpow_neg_half_sq6 hα,
              Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 10 * (2 * K + 2 * (K * Ce)))]
    rw [hR2]
    rwa [hfac] at hsq
  rw [show HkNorm α 6 (fun z θ => f z θ * g z θ)
      = Real.sqrt (HkSq α 6 (fun z θ => f z θ * g z θ)) from rfl]
  calc Real.sqrt (HkSq α 6 (fun z θ => f z θ * g z θ))
      ≤ Real.sqrt ((Real.sqrt (10 * (2 * K + 2 * (K * Ce))) * α ^ (-(1 / 2 : ℝ))
          * HkNorm α 6 f * HkNorm α 6 g) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt (10 * (2 * K + 2 * (K * Ce))) * α ^ (-(1 / 2 : ℝ))
          * HkNorm α 6 f * HkNorm α 6 g := Real.sqrt_sq hRnn
    _ ≤ (Real.sqrt (10 * (2 * K + 2 * (K * Ce))) + 1) * α ^ (-(1 / 2 : ℝ))
          * HkNorm α 6 f * HkNorm α 6 g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (10 * (2 * K + 2 * (K * Ce))) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
        have h3 : (0 : ℝ) ≤ HkNorm α 6 f := Real.sqrt_nonneg _
        have h4 : (0 : ℝ) ≤ HkNorm α 6 g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

end Work.FTS.StrongPersist.N6
