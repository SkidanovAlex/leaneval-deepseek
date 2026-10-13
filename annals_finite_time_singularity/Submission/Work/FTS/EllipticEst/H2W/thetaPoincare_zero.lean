import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.H2W.sliceEtaPoincare

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Rewriting the `k = 0` integrand -/

theorem HkIntegrand_zero_eq_Wf (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ = (f z θ * Wf z θ) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Wf]
  norm_num

theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : 0 ≤ Real.sin (2 * θ)) :
    Work.Spaces.HkIntegrand α 0 f z θ = (f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * rho θ) := by
  rw [HkIntegrand_zero_eq_Wf, mul_pow, Wf_sq_eq h]

/-- The `z`-slice of the squared `k = 0` integrand. -/
def Slice (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (f z θ * Wf z θ) ^ 2

theorem Slice_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Slice f z = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * rho θ := by
  rw [Slice, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [mul_pow, Wf_sq_eq (sin_two_nonneg ‹_›)]
  ring

theorem Slice_nonneg (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Slice f z :=
  integral_nonneg fun _ => sq_nonneg _

theorem Slice_zero (f : ℝ → ℝ → ℝ) : Slice f 0 = 0 := by
  rw [Slice]
  have h : ∀ θ : ℝ, Wf 0 θ = 0 := fun _ => by simp [Wf, Work.Spaces.w]
  simp only [h, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  simp

theorem NSq_eq_integral_Slice (f : ℝ → ℝ → ℝ) :
    NSq f = ∫ z in Work.Spaces.Iz, Slice f z := rfl

theorem Slice_eq_integral_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Slice f z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ := by
  rw [Slice]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  exact (HkIntegrand_zero_eq_Wf α f z θ).symm

theorem HkIntegrand_zero_fst (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f 0 θ = 0 := by
  rw [HkIntegrand_zero_eq_Wf]
  have h : Wf 0 θ = 0 := by simp [Wf, Work.Spaces.w]
  rw [h, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

theorem HkIntegrand_zero_integrableOn_of {α : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * rho θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f z θ) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * rho θ)) Work.Spaces.Iθ :=
    h.const_mul _
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  rw [HkIntegrand_zero_eq α f z θ (sin_two_nonneg ‹_›)]
  ring

theorem integrableOn_sq_rho_of_HkIntegrand_zero {α : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (hw : (Work.Spaces.w z) ^ 2 ≠ 0)
    (h : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * rho θ) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.HkIntegrand α 0 f z θ))
      Work.Spaces.Iθ := h.const_mul _
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only []
  rw [HkIntegrand_zero_eq α f z θ (sin_two_nonneg ‹_›)]
  rw [show (f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * rho θ)
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * rho θ) from by ring]
  exact inv_mul_cancel_left₀ hw ((f z θ) ^ 2 * rho θ)

theorem thetaPoincare_zero : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, V z 0 = 0) → (∀ z, V z (Real.pi / 2) = 0) →
    (∀ z, 0 < z → Filter.Tendsto (fun θ => V z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (∀ z, 0 < z → Filter.Tendsto (fun θ => V z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 V) →
    Work.Spaces.HkMem α 0 V ∧ Work.Spaces.HkMem α 0 (Work.Spaces.pth V) ∧
      Work.Spaces.HkNorm α 0 V ≤ C * Work.Spaces.HkNorm α 0 (Work.Spaces.pthIter 2 V) ∧
      Work.Spaces.HkNorm α 0 (Work.Spaces.pth V) ≤ C * Work.Spaces.HkNorm α 0 (Work.Spaces.pthIter 2 V) := by
  obtain ⟨C1, hC1pos, hC1⟩ := sliceEtaPoincare
  refine ⟨max 1 (Real.sqrt C1),
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.sqrt C1)), ?_⟩
  intro α V _hα _hα4 hsm _hV0 _hVL hlim0 hlimL hmem
  have hSO : Work.FTS.EllipticEst.SmoothOpen V := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hsm_slice : ∀ z : ℝ, 0 < z → ∀ n : ℕ,
      ContDiffOn ℝ n (fun θ : ℝ => V z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz n
    have hcurve : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_const (c := z)).prodMk contDiffOn_id
    have hcomp := (hsm n).comp hcurve (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hmain : ∀ z ∈ Work.Spaces.Iz,
      Slice V z ≤ C1 * Slice (Work.Spaces.pthIter 2 V) z ∧
      Slice (Work.Spaces.pth V) z ≤ C1 * Slice (Work.Spaces.pthIter 2 V) z ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 V z θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth V) z θ)
        Work.Spaces.Iθ := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with hz0 | hzpos
    · subst hz0
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Slice_zero V, Slice_zero (Work.Spaces.pthIter 2 V)]; simp
      · rw [Slice_zero (Work.Spaces.pth V), Slice_zero (Work.Spaces.pthIter 2 V)]; simp
      · refine MeasureTheory.IntegrableOn.congr_fun (integrableOn_zero) (fun θ _ => ?_)
          measurableSet_Icc
        exact (HkIntegrand_zero_fst α V θ).symm
      · refine MeasureTheory.IntegrableOn.congr_fun (integrableOn_zero) (fun θ _ => ?_)
          measurableSet_Icc
        exact (HkIntegrand_zero_fst α (Work.Spaces.pth V) θ).symm
    · have hwpos : 0 < Work.Spaces.w z := by
        rw [Work.Spaces.w]
        exact div_pos (pow_pos (by linarith) 2) (pow_pos hzpos 2)
      have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
      have hint : MeasureTheory.IntegrableOn
          (fun θ => (deriv (deriv (fun θ : ℝ => V z θ)) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        integrableOn_sq_rho_of_HkIntegrand_zero hwne (hmem.1 z hz)
      obtain ⟨hiu, hi1, hineq_u, hineq_1⟩ :=
        hC1 (fun θ : ℝ => V z θ) (hsm_slice z hzpos) (hlim0 z hzpos) (hlimL z hzpos) hint
      refine ⟨?_, ?_, HkIntegrand_zero_integrableOn_of (f := V) hiu,
        HkIntegrand_zero_integrableOn_of (f := Work.Spaces.pth V) hi1⟩
      · rw [Slice_eq, Slice_eq]
        calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (V z θ) ^ 2 * rho θ)
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 V z θ) ^ 2 * rho θ)) :=
              mul_le_mul_of_nonneg_left hineq_u (sq_nonneg _)
          _ = C1 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 V z θ) ^ 2 * rho θ)) := by ring
      · rw [Slice_eq, Slice_eq]
        calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth V z θ) ^ 2 * rho θ)
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 V z θ) ^ 2 * rho θ)) :=
              mul_le_mul_of_nonneg_left hineq_1 (sq_nonneg _)
          _ = C1 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 V z θ) ^ 2 * rho θ)) := by ring
  have hT_slice_int : MeasureTheory.IntegrableOn (Slice (Work.Spaces.pthIter 2 V))
      Work.Spaces.Iz := by
    refine hmem.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    exact (Slice_eq_integral_HkIntegrand α (Work.Spaces.pthIter 2 V) z).symm
  have aesm_of : ∀ (f : ℝ → ℝ → ℝ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
        Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro f hf
    have hX : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hf
    have h2 := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h2
  have houtV : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 V z θ) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hT_slice_int.const_mul C1)
      (aesm_of V (hSO.continuousOn_HkIntegrand α 0)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 V z θ),
      ← Slice_eq_integral_HkIntegrand α V z]
    exact (hmain z hz).1
  have hout1 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth V) z θ)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hT_slice_int.const_mul C1)
      (aesm_of (Work.Spaces.pth V) ((hSO.pth).continuousOn_HkIntegrand α 0)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pth V) z θ),
      ← Slice_eq_integral_HkIntegrand α (Work.Spaces.pth V) z]
    exact (hmain z hz).2.1
  have hSqV : Work.Spaces.HkSq α 0 V
      ≤ C1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V) := by
    rw [NSq_eq_HkSq α V, NSq_eq_HkSq α (Work.Spaces.pthIter 2 V),
      NSq_eq_integral_Slice V, NSq_eq_integral_Slice (Work.Spaces.pthIter 2 V)]
    have hmono : (∫ z in Work.Spaces.Iz, Slice V z)
        ≤ ∫ z in Work.Spaces.Iz, C1 * Slice (Work.Spaces.pthIter 2 V) z := by
      refine integral_mono_of_nonneg ?_ (hT_slice_int.const_mul C1) ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
        exact Slice_nonneg V z
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        exact (hmain z hz).1
    calc (∫ z in Work.Spaces.Iz, Slice V z)
        ≤ ∫ z in Work.Spaces.Iz, C1 * Slice (Work.Spaces.pthIter 2 V) z := hmono
      _ = C1 * ∫ z in Work.Spaces.Iz, Slice (Work.Spaces.pthIter 2 V) z :=
          MeasureTheory.integral_const_mul C1 _
  have hSq1 : Work.Spaces.HkSq α 0 (Work.Spaces.pth V)
      ≤ C1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V) := by
    rw [NSq_eq_HkSq α (Work.Spaces.pth V), NSq_eq_HkSq α (Work.Spaces.pthIter 2 V),
      NSq_eq_integral_Slice (Work.Spaces.pth V),
      NSq_eq_integral_Slice (Work.Spaces.pthIter 2 V)]
    have hmono : (∫ z in Work.Spaces.Iz, Slice (Work.Spaces.pth V) z)
        ≤ ∫ z in Work.Spaces.Iz, C1 * Slice (Work.Spaces.pthIter 2 V) z := by
      refine integral_mono_of_nonneg ?_ (hT_slice_int.const_mul C1) ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
        exact Slice_nonneg (Work.Spaces.pth V) z
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        exact (hmain z hz).2.1
    calc (∫ z in Work.Spaces.Iz, Slice (Work.Spaces.pth V) z)
        ≤ ∫ z in Work.Spaces.Iz, C1 * Slice (Work.Spaces.pthIter 2 V) z := hmono
      _ = C1 * ∫ z in Work.Spaces.Iz, Slice (Work.Spaces.pthIter 2 V) z :=
          MeasureTheory.integral_const_mul C1 _
  have norm_le : ∀ f : ℝ → ℝ → ℝ, Work.Spaces.HkSq α 0 f
      ≤ C1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkNorm α 0 f
        ≤ max 1 (Real.sqrt C1) * Work.Spaces.HkNorm α 0 (Work.Spaces.pthIter 2 V) := by
    intro f hf
    have h1 : Real.sqrt (Work.Spaces.HkSq α 0 f)
        ≤ Real.sqrt (C1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V)) :=
      Real.sqrt_le_sqrt hf
    calc Work.Spaces.HkNorm α 0 f = Real.sqrt (Work.Spaces.HkSq α 0 f) := rfl
      _ ≤ Real.sqrt (C1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V)) := h1
      _ = Real.sqrt C1 * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V)) :=
          Real.sqrt_mul hC1pos.le _
      _ ≤ max 1 (Real.sqrt C1)
            * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 V)) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 (Real.sqrt C1)) (Real.sqrt_nonneg _)
      _ = max 1 (Real.sqrt C1) * Work.Spaces.HkNorm α 0 (Work.Spaces.pthIter 2 V) := rfl
  exact ⟨⟨fun z hz => (hmain z hz).2.2.1, houtV⟩,
    ⟨fun z hz => (hmain z hz).2.2.2, hout1⟩, norm_le V hSqV, norm_le (Work.Spaces.pth V) hSq1⟩

end Work.FTS.EllipticEst.H2W
