import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePt6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound
import Submission.Work.FTS.H2.HeasyBlocksId
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# pureGamFamSix — critical-weight slot (B): the slice bound
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The slice bound -/

theorem critD_eq (α : ℝ) :
    critD α = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * θ)) ^ (-(1 - α / 10)) :=
  rfl

theorem int_sig_beta_eq_critD (α : ℝ) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * θ)) ^ (α / 10 - 1)) = critD α := by
  rw [critD]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  congr 1
  ring

theorem sliceCritPt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (m : ℕ) (hm : m + 1 ≤ 6)
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1)) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2
        ≤ (2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
            + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
                (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
                  * (Real.sin (2 * θ')) ^ (1 - α / 10)) * critD α)
          * (Real.sin (2 * θ)) ^ (α / 10 - 1) := by
  have hβ0 : (0 : ℝ) < α / 10 := by linarith
  have hβ1 : α / 10 ≤ 1 := by linarith
  set f : ℝ → ℝ := fun θ => Work.Spaces.DzIter m g z θ with hf
  have hsm : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((hgs.DzIter m).curry_θ hz).of_le (by norm_num)
  have hintS : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simpa only [hf] using hasDeriv_int_slice hα hgs hgm m hm hz
  have hpt := slicePtBound (β := α / 10) hβ0 hβ1 hsm hintS hintB
  intro θ hθ
  have h1 := hpt θ hθ
  have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  rw [show -(1 - α / 10) = α / 10 - 1 from by ring]
  calc (Real.sin (2 * θ)) ^ (α / 10 - 1) * (Work.Spaces.DzIter m g z θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (α / 10 - 1)
          * (2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
            + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
                (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
                  * (Real.sin (2 * θ')) ^ (1 - α / 10))
              * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (Real.sin (2 * θ)) ^ (α / 10 - 1))) :=
        mul_le_mul_of_nonneg_left (by simpa only [hf] using h1) (Real.rpow_pos_of_pos hσ _).le
    _ = (2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
            + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
                (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
                  * (Real.sin (2 * θ')) ^ (1 - α / 10)) * critD α)
          * (Real.sin (2 * θ)) ^ (α / 10 - 1) := by
        rw [int_sig_beta_eq_critD]; ring

theorem sliceCritBound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (m : ℕ) (hm : m + 1 ≤ 6)
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1)) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g z θ) ^ 2)
      ≤ 2 * critD α * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
        + 2 * critD α * critD α
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed m 1 g z θ) ^ 2) := by
  have hβ0 : (0 : ℝ) < α / 10 := by linarith
  have hβ1 : α / 10 ≤ 1 := by linarith
  obtain ⟨hm1, hm6⟩ : 1 ≤ m + 1 ∧ m + 1 ≤ 6 := ⟨by omega, hm⟩
  set f : ℝ → ℝ := fun θ => Work.Spaces.DzIter m g z θ with hf
  set Az : ℝ := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10) with hAz
  set Qz : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    * (Work.Spaces.mixed m 1 g z θ) ^ 2 with hQz
  have hAzQ : Az ≤ Qz := by
    rw [hAz, hQz]
    have hcongr : Set.EqOn
        (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed m 1 g z θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      intro θ hθ
      simp only []
      have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
      have hd : deriv f θ = Work.Spaces.mixed m 1 g z θ / Real.sin (2 * θ) := by
        rw [hf, eq_div_iff (ne_of_gt hσ), mul_comm]
        exact sigma_pth_dzIter hgs m hz hθ
      have h2 : (Real.sin (2 * θ)) ^ (1 - α / 10)
          * ((Real.sin (2 * θ)) ^ (2 : ℕ))⁻¹
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [← Real.rpow_two, ← Real.rpow_neg hσ.le, ← Real.rpow_add hσ, Work.Spaces.gam]
        congr 1
        ring
      rw [hd, div_pow, div_eq_mul_inv]
      calc ((Work.Spaces.mixed m 1 g z θ) ^ 2 * ((Real.sin (2 * θ)) ^ (2 : ℕ))⁻¹)
            * (Real.sin (2 * θ)) ^ (1 - α / 10)
          = ((Real.sin (2 * θ)) ^ (1 - α / 10) * ((Real.sin (2 * θ)) ^ (2 : ℕ))⁻¹)
              * (Work.Spaces.mixed m 1 g z θ) ^ 2 := by ring
        _ = _ := by rw [h2]
    have hI := mixedSlot_slice_integrable_Iθ hα hgs hgm (a := 1) (b := m) le_rfl
      (by omega) hz
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hcongr]
    refine MeasureTheory.setIntegral_mono_set hI ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        mul_nonneg (sin_two_rpow_nonneg_Iθ hθ) (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have hkey := sliceCritPt hα hα1 hgs hgm m hm hintB hz
  have hmaj : MeasureTheory.Integrable
      (fun θ => (2 * (f (Real.pi / 4)) ^ 2 + 2 * Az * critD α)
        * (Real.sin (2 * θ)) ^ (α / 10 - 1))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hintB.const_mul _
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (f θ) ^ 2)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (2 * (f (Real.pi / 4)) ^ 2 + 2 * Az * critD α)
            * (Real.sin (2 * θ)) ^ (α / 10 - 1) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_) hmaj
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_)
    · exact mul_nonneg (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) _) (sq_nonneg _)
    · rw [hAz]
      exact hkey θ hθ
  have hval : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (2 * (f (Real.pi / 4)) ^ 2 + 2 * Az * critD α)
          * (Real.sin (2 * θ)) ^ (α / 10 - 1))
      = (2 * (f (Real.pi / 4)) ^ 2 + 2 * Az * critD α) * critD α := by
    rw [← int_sig_beta_eq_critD, MeasureTheory.integral_const_mul]
  have hLHS : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (f θ) ^ 2 := by
    rw [← restrict_Ioo_eq_Iθ]
  rw [hLHS]
  refine (hmono.trans_eq hval).trans ?_
  have h2 : Az * critD α ^ 2 ≤ Qz * critD α ^ 2 :=
    mul_le_mul_of_nonneg_right hAzQ (sq_nonneg _)
  nlinarith [h2]


end Work.FTS.StrongPersist.N6Trans.SixRoute
