import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePt6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound
import Submission.Work.FTS.H2.HeasyBlocksId
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# pureGamFamSix — critical-weight slot (A): slice tools
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The critical angular weight integral `∫_{(0,π/2)} sin(2θ)^{α/10-1} dθ`. -/
def critD (α : ℝ) : ℝ :=
  ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * θ)) ^ (-(1 - α / 10))

theorem critD_nonneg (α : ℝ) : 0 ≤ critD α :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun _ hθ =>
    Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) _

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have h3 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, h3⟩

theorem sin_two_rpow_nonneg_Iθ {c : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ c :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem restrict_Ioo_eq_Iθ :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))

/-! ## Slice strong measurability -/

theorem aesm_slice_Iθ {f : ℝ → ℝ} (h : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [← restrict_Ioo_eq_Iθ]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-! ## The `γ`-weighted mixed slot, slicewise -/

theorem mixedSlot_slice_integrable_Iθ {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed b a g z θ) ^ 2) Work.Spaces.Iθ := by
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 :=
    one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  refine MeasureTheory.Integrable.mono' (hgm.1 z hz.le) ?_ ?_
  · refine aesm_slice_Iθ ?_
    have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b a g z θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))).mul
        (((hgs.mixed b a).curry_θ hz).continuousOn.pow 2)
    exact hcont
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Real.norm_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
        by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _))]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, show Real.sin (2 * (0:ℝ)) = 0 by simp,
        Real.zero_rpow (by simpa using gam_ne_zero hα), zero_mul]
      exact Work.Spaces.HkIntegrand_nonneg α 6 g z 0
    rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · rw [h2, show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi],
        Real.zero_rpow (by simpa using gam_ne_zero hα), zero_mul]
      exact Work.Spaces.HkIntegrand_nonneg α 6 g z (Real.pi / 2)
    · have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo ⟨h0, h2⟩
      have hY0 : 0 ≤ (Work.Spaces.mixed b a g z θ) ^ 2 := sq_nonneg _
      have hσγ0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg hσ.le _
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed b a g z θ) ^ 2
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b a g z θ) ^ 2 := by
            have h := mul_le_mul_of_nonneg_right hw (mul_nonneg hσγ0 hY0)
            linarith [h]
        _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            rw [mul_pow, Wt_sq_eq (gam_ne_zero hα) hσ.le]
            ring
        _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ a b ha hab

/-! ## The Hardy-compatible integrability of the slice derivative -/

theorem hasDeriv_int_slice {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (m : ℕ) (hm : m + 1 ≤ 6) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (1 - α / 10)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h0 : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed m 1 g z θ) ^ 2) Work.Spaces.Iθ :=
    mixedSlot_slice_integrable_Iθ hα hgs hgm (a := 1) (b := m) le_rfl (by omega) hz
  have h1 : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed m 1 g z θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h0.mono_set Set.Ioo_subset_Icc_self
  refine h1.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hd : deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ
      = Work.Spaces.mixed m 1 g z θ / Real.sin (2 * θ) := by
    rw [eq_div_iff (ne_of_gt hσ), mul_comm]
    exact sigma_pth_dzIter hgs m hz hθ
  have h2 : (Real.sin (2 * θ)) ^ (1 - α / 10) * ((Real.sin (2 * θ)) ^ (2 : ℕ))⁻¹
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_neg hσ.le, ← Real.rpow_add hσ, Work.Spaces.gam]
    congr 1
    ring
  have h1' : (Real.sin (2 * θ)) ^ (1 - α / 10)
        * (Work.Spaces.mixed m 1 g z θ / Real.sin (2 * θ)) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed m 1 g z θ) ^ 2 := by
    rw [div_pow, div_eq_mul_inv]
    calc (Real.sin (2 * θ)) ^ (1 - α / 10)
          * ((Work.Spaces.mixed m 1 g z θ) ^ 2 * ((Real.sin (2 * θ)) ^ (2 : ℕ))⁻¹)
        = ((Real.sin (2 * θ)) ^ (1 - α / 10) * ((Real.sin (2 * θ)) ^ (2 : ℕ))⁻¹)
            * (Work.Spaces.mixed m 1 g z θ) ^ 2 := by ring
      _ = _ := by rw [h2]
  calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed m 1 g z θ) ^ 2
      = (Real.sin (2 * θ)) ^ (1 - α / 10)
          * (Work.Spaces.mixed m 1 g z θ / Real.sin (2 * θ)) ^ 2 := h1'.symm
    _ = (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (1 - α / 10) := by
        rw [hd]
        ring


end Work.FTS.StrongPersist.N6Trans.SixRoute
