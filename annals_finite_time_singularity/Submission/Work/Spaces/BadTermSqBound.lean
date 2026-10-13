import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_g_bound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HProductRule_bad_term

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- The two dominating functions used by the bad term of the `H^4` product rule:

* `badU α f z` is the (constant in `θ`) bound for the `f`-factor, coming from the angular
  Hardy inequality (`bt_f_bound`);
* `badV α g θ` is the (constant in `z`) bound for the `g`-factor, coming from the radial
  Hardy inequality (`bt_g_bound`).

Both are honest integrable functions: `badU` because the squared weighted mixed derivative
`mixed 3 1 f · W` is square-integrable on the product (`bt_prod_integrable`), `badV` for the
same reason with `g` and `mixed 1 1 g`. -/
def badU (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  100 / (gam α - 1) * ∫ s in Iθ, (mixed 3 1 f z s * Wt α z s) ^ 2

def badV (α : ℝ) (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z' in Iz, (mixed 1 1 g z' θ * Wt α z' θ) ^ 2

theorem badU_int (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (hsmf : SmoothNbhd f)
    (hmemf : HkMem α 4 f) :
    Integrable (badU α f) (volume.restrict Iz) := by
  have hF1 : Integrable
      (fun p : ℝ × ℝ => (mixed 3 1 f p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    (bt_prod_integrable α f hsmf hmemf 3 1 (by norm_num) (by norm_num)).1
  exact hF1.integral_prod_left.const_mul (100 / (gam α - 1))

theorem badV_int (α : ℝ) (g : ℝ → ℝ → ℝ) (hsmg : SmoothNbhd g) (hmemg : HkMem α 4 g) :
    Integrable (badV α g) (volume.restrict Iθ) := by
  have hF2 : Integrable
      (fun p : ℝ × ℝ => (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    (bt_prod_integrable α g hsmg hmemg 1 1 (le_refl 1) (by norm_num)).1
  exact hF2.integral_prod_right

theorem BadTermSqBound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hvtf : Work.Spaces.VanishTheta f)
    (hmemf : Work.Spaces.HkMem α 4 f) (hsmg : Work.Spaces.SmoothNbhd g)
    (hdecg : Work.Spaces.DecayInZ 4 g) (hmemg : Work.Spaces.HkMem α 4 g)
    (hslice_meas : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
            * Work.Spaces.Wt α z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter 3 f p.1 p.2 * Work.Spaces.Dth g p.1 p.2
            * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
            * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 3 f z θ
              * Work.Spaces.Dth g z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz
      ∧ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 3 f z θ
              * Work.Spaces.Dth g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
  have hmIz : MeasurableSet Iz := measurableSet_Ici
  have hmIθ : MeasurableSet Iθ := measurableSet_Icc
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  -- the product-measure integrability data of the two mixed derivatives
  obtain ⟨hF1, hF1val⟩ := bt_prod_integrable α f hsmf hmemf 3 1 (by norm_num) (by norm_num)
  obtain ⟨hF2, hF2val⟩ := bt_prod_integrable α g hsmg hmemg 1 1 (le_refl 1) (by norm_num)
  -- the two Hardy bounds
  have hfbound := bt_f_bound α hα hα1 f hsmf hvtf hmemf
  have hgbound := bt_g_bound α hα hα1 g hsmg hdecg hF2
  -- the two dominating functions
  have hUint : Integrable (badU α f) (volume.restrict Iz) := badU_int α hα f hsmf hmemf
  have hVint : Integrable (badV α g) (volume.restrict Iθ) := badV_int α g hsmg hmemg
  have hUnn : ∀ z, 0 ≤ badU α f z := by
    intro z
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) hγ)) (integral_nonneg fun s => sq_nonneg _)
  have hVnn : ∀ θ, 0 ≤ badV α g θ := fun θ => integral_nonneg fun z => sq_nonneg _
  -- pointwise (in `θ`) domination of the `f`-factor on the domain
  have hfdom : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (DzIter 3 f z θ) ^ 2 * (w z) ^ 2 ≤ badU α f z := fun z hz θ hθ => hfbound z hz θ hθ
  -- pointwise (a.e. in `θ`) domination of the `g`-factor
  have hgdom : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
      (Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) ≤ badV α g θ := hgbound
  -- the pointwise domination of the whole bad-term integrand
  have hdom : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
      ‖(DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2‖ ≤ badU α f z * badV α g θ := by
    filter_upwards [hgdom, ae_restrict_mem hmIθ] with θ hb hθ z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), bt_factor α z θ hα hθ f g]
    refine mul_le_mul (hfdom z hz θ hθ) (hb z hz)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _)) (hUnn z)
  -- the `θ`-integral of the bad-term integrand, bounded by `badU z * ∫ badV`
  have hinner : ∀ z ∈ Iz,
      (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2)
        ≤ badU α f z * ∫ θ in Iθ, badV α g θ := by
    intro z hz
    calc ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, ((DzIter 3 f z θ) ^ 2 * (w z) ^ 2)
            * ((Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hmIθ] with θ hθ
          exact bt_factor α z θ hα hθ f g
      _ ≤ ∫ θ in Iθ, badU α f z * badV α g θ := by
          apply integral_mono_of_nonneg
          · filter_upwards [ae_restrict_mem hmIθ] with θ hθ
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _))
          · exact hVint.const_mul _
          · filter_upwards [hgdom, ae_restrict_mem hmIθ] with θ hb hθ
            refine mul_le_mul (hfdom z hz θ hθ) (hb z hz)
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _)) (hUnn z)
      _ = badU α f z * ∫ θ in Iθ, badV α g θ := integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · -- each angular slice is integrable, by domination
    intro z hz
    exact Integrable.mono' (hVint.const_mul _) (hslice_meas z hz) (hdom.mono fun θ h => h z hz)
  · -- the iterated integral is integrable, by domination
    refine Integrable.mono' (hUint.mul_const (∫ θ in Iθ, badV α g θ)) ?_ ?_
    · exact hjoint.integral_prod_right'
    · filter_upwards [ae_restrict_mem hmIz] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
      exact hinner z hz
  · -- the value of the iterated integral, by the assembly lemma
    exact bt_assembly α hα hα1 f g hsmf hvtf hmemf hsmg hdecg hmemg hF1 hF1val hF2 hF2val
      hfbound hgbound

end Work.Spaces
