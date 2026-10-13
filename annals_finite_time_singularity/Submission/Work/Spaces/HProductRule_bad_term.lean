import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.integral_sin_rpow
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_g_bound

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

/-- Assembly step for the bad term: combining the pointwise `θ`-bound on `D_z^3 f`, the a.e.
`z`-bound on `D_θ g`, and the product integrability / Fubini data. -/
theorem bt_assembly (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : SmoothNbhd f) (hvtf : VanishTheta f) (hmf : HkMem α 4 f)
    (hsmg : SmoothNbhd g) (hdecg : DecayInZ 4 g) (hmg : HkMem α 4 g)
    (hF1 : Integrable (fun p : ℝ × ℝ => (mixed 3 1 f p.1 p.2 * Wt α p.1 p.2) ^ 2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)))
    (hF1val : integral ((volume.restrict Iz).prod (volume.restrict Iθ))
        (fun p : ℝ × ℝ => (mixed 3 1 f p.1 p.2 * Wt α p.1 p.2) ^ 2)
        = L2Sq (fun z θ => mixed 3 1 f z θ * Wt α z θ))
    (hF2 : Integrable (fun p : ℝ × ℝ => (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)))
    (hF2val : integral ((volume.restrict Iz).prod (volume.restrict Iθ))
        (fun p : ℝ × ℝ => (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2)
        = L2Sq (fun z θ => mixed 1 1 g z θ * Wt α z θ))
    (hfbound : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
        (DzIter 3 f z θ) ^ 2 * (w z) ^ 2
          ≤ 100 / (gam α - 1) * ∫ s in Iθ, (mixed 3 1 f z s * Wt α z s) ^ 2)
    (hgbound : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
        (Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          ≤ ∫ z' in Iz, (mixed 1 1 g z' θ * Wt α z' θ) ^ 2) :
    L2Sq (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
      ≤ 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
  have hmIz : MeasurableSet Iz := measurableSet_Ici
  have hmIθ : MeasurableSet Iθ := by rw [Iθ]; exact measurableSet_Icc
  have hγ : 0 < 100 / (gam α - 1) := by
    apply div_pos (by norm_num)
    rw [gam_sub_one]; linarith
  -- integrability of the slices/objects
  have hUint : Integrable (fun z => ∫ s, (mixed 3 1 f z s * Wt α z s) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := hF1.integral_prod_left
  have hVint : Integrable (fun θ => ∫ z', (mixed 1 1 g z' θ * Wt α z' θ) ^ 2 ∂(volume.restrict Iz))
      (volume.restrict Iθ) := hF2.integral_prod_right
  set Uhat : ℝ → ℝ := fun z => 100 / (gam α - 1) * ∫ s in Iθ, (mixed 3 1 f z s * Wt α z s) ^ 2 with hUhat
  set Vhat : ℝ → ℝ := fun θ => ∫ z' in Iz, (mixed 1 1 g z' θ * Wt α z' θ) ^ 2 with hVhat
  have hUhat_int : Integrable Uhat (volume.restrict Iz) := by
    rw [hUhat]; exact hUint.const_mul _
  have hVhat_int : Integrable Vhat (volume.restrict Iθ) := by
    rw [hVhat]; exact hVint
  have hUhat_nn : ∀ z, 0 ≤ Uhat z := by
    intro z; rw [hUhat]
    exact mul_nonneg (le_of_lt hγ) (integral_nonneg fun s => sq_nonneg _)
  have hVhat_nn : ∀ θ, 0 ≤ Vhat θ := by
    intro θ; rw [hVhat]
    exact integral_nonneg fun z => sq_nonneg _
  -- value and bound for `∫ Vhat`
  have hVval : ∫ θ, Vhat θ ∂(volume.restrict Iθ)
      = L2Sq (fun z θ => mixed 1 1 g z θ * Wt α z θ) := by
    have key : ∫ θ, Vhat θ ∂(volume.restrict Iθ)
        = ∫ z, (∫ θ, (mixed 1 1 g z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
            ∂(volume.restrict Iz) := by
      rw [hVhat]
      exact (MeasureTheory.integral_integral_swap
        (f := fun z θ => (mixed 1 1 g z θ * Wt α z θ) ^ 2) hF2).symm
    rw [key]
    rw [← MeasureTheory.integral_prod
      (fun p : ℝ × ℝ => (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2) hF2, hF2val]
  have hVle : ∫ θ, Vhat θ ∂(volume.restrict Iθ) ≤ HkSq α 4 g := by
    rw [hVval]
    exact L2Sq_mixed_le_HkSq α 4 g hmg 1 1 (le_refl 1) (by norm_num)
  -- value and bound for `∫ Uhat`
  have hUval : ∫ z, Uhat z ∂(volume.restrict Iz)
      = 100 / (gam α - 1) * L2Sq (fun z θ => mixed 3 1 f z θ * Wt α z θ) := by
    rw [hUhat, MeasureTheory.integral_const_mul]
    congr 1
  have hUle : ∫ z, Uhat z ∂(volume.restrict Iz) ≤ 100 / (gam α - 1) * HkSq α 4 f := by
    rw [hUval]
    exact mul_le_mul_of_nonneg_left
      (L2Sq_mixed_le_HkSq α 4 f hmf 1 3 (by norm_num) (by norm_num)) (le_of_lt hγ)
  -- inner (θ-)bound
  have hinner : ∀ z ∈ Iz, ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
      ≤ Uhat z * ∫ θ in Iθ, Vhat θ := by
    intro z hz
    have hU := hfbound z hz
    calc ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, ((DzIter 3 f z θ) ^ 2 * (w z) ^ 2)
            * ((Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem hmIθ] with θ hθ
          exact bt_factor α z θ hα hθ f g
      _ ≤ ∫ θ in Iθ, Uhat z * Vhat θ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · filter_upwards [MeasureTheory.ae_restrict_mem hmIθ] with θ hθ
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _))
          · exact hVhat_int.const_mul _
          · filter_upwards [MeasureTheory.ae_restrict_mem hmIθ, hgbound] with θ hθ hb
            have hUb : (DzIter 3 f z θ) ^ 2 * (w z) ^ 2 ≤ Uhat z := by
              rw [hUhat]; exact hU θ hθ
            have hVb : (Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) ≤ Vhat θ := by
              rw [hVhat]; exact hb z hz
            exact mul_le_mul hUb hVb
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _))
              (hUhat_nn z)
      _ = Uhat z * ∫ θ in Iθ, Vhat θ := by
          rw [MeasureTheory.integral_const_mul]
  -- outer (z-)bound
  have houter : ∫ z in Iz, (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2)
      ≤ (∫ θ in Iθ, Vhat θ) * ∫ z in Iz, Uhat z := by
    calc ∫ z in Iz, (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2)
        ≤ ∫ z in Iz, Uhat z * (∫ θ in Iθ, Vhat θ) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · filter_upwards with z
            exact integral_nonneg fun θ => sq_nonneg _
          · exact hUhat_int.mul_const _
          · filter_upwards [MeasureTheory.ae_restrict_mem hmIz] with z hz
            exact hinner z hz
      _ = (∫ z in Iz, Uhat z) * (∫ θ in Iθ, Vhat θ) := by
          rw [MeasureTheory.integral_mul_const]
      _ = (∫ θ in Iθ, Vhat θ) * ∫ z in Iz, Uhat z := by ring
  calc L2Sq (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
      = ∫ z in Iz, (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2) := rfl
    _ ≤ (∫ θ in Iθ, Vhat θ) * ∫ z in Iz, Uhat z := houter
    _ ≤ HkSq α 4 g * (100 / (gam α - 1) * HkSq α 4 f) :=
        mul_le_mul hVle hUle (integral_nonneg hUhat_nn) (HkSq_nonneg α 4 g)
    _ = 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring


/-! ## The bad term of the `H^4` product rule -/

theorem HProductRule_bad_term : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f g : ℝ → ℝ → ℝ),
    Work.Spaces.SmoothNbhd f → Work.Spaces.SmoothNbhd g →
    Work.Spaces.VanishTheta f → Work.Spaces.VanishTheta g →
    Work.Spaces.DecayInZ 4 f → Work.Spaces.DecayInZ 4 g →
    Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
          * Work.Spaces.Wt α z θ)
        ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hα hα1 f g hsmf hsmg hvtf hvtg hdecf hdecg hmf hmg
  obtain ⟨hF1, hF1val⟩ := bt_prod_integrable α f hsmf hmf 3 1 (by norm_num) (by norm_num)
  obtain ⟨hF2, hF2val⟩ := bt_prod_integrable α g hsmg hmg 1 1 (le_refl 1) (by norm_num)
  exact bt_assembly α hα hα1 f g hsmf hvtf hmf hsmg hdecg hmg hF1 hF1val hF2 hF2val
    (bt_f_bound α hα hα1 f hsmf hvtf hmf) (bt_g_bound α hα hα1 g hsmg hdecg hF2)

end Work.Spaces
