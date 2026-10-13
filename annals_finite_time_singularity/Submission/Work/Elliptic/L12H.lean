import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.HardyLeft
import Submission.Work.Elliptic.HardyRight
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.Elliptic.L12TermHigh
import Submission.Work.Elliptic.L12k0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `Qang g 0 z = z * L12dens g z`. -/
theorem Qang0_eq (g : ℝ → ℝ → ℝ) {z : ℝ} (hz : z ≠ 0) :
    Qang g 0 z = z * L12dens g z := by
  rw [L12dens_eq_Qang_div, mul_div_cancel₀ _ hz]

theorem L12H : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd g → Work.Spaces.HkMem α 4 g → Work.Elliptic.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.L12 g z) ∧
      Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.L12 g z) ≤ C * Work.Spaces.HkNorm α 4 g := by
  refine ⟨1 + (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      * (111 * (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)), ?_, ?_⟩
  · have h2 : (0:ℝ) ≤ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
    have h3 : (0:ℝ) ≤ (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
    nlinarith [mul_nonneg h2 (by linarith : (0:ℝ) ≤ 111 * (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2))]
  · intro α g hα hα1 hsm hmem h0
    set u : ℝ → ℝ := fun z => L12 g z with hu
    set hh : ℝ → ℝ → ℝ := fun z θ => u z with hhu
    obtain ⟨hint, hderiv, hcontAt⟩ := Work.Elliptic.L12densFacts α g hsm hmem
    have hcontd : ContinuousOn (L12dens g) (Set.Ioi (0:ℝ)) :=
      fun z hz => (hcontAt z hz).continuousWithinAt
    obtain ⟨hval, htend, hcontu⟩ := Work.Elliptic.L12_values g hint h0
    have hid : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
        Work.Spaces.DzIter k (fun z θ => L12 g z) z θ = - Qang g (k - 1) z :=
      fun k hk hk4 z hz θ => Work.Elliptic.L12Iterate α g hsm hderiv hk hk4 hz θ
    set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθ
    set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2 with hAK
    -- integrability and bound for the `Qang g 0` term
    have hQaesm : AEStronglyMeasurable (fun z => (Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (volume.restrict Work.Spaces.Iz) := by
      rw [← restrict_Ioi_eq_restrict_Iz]
      have hcont1 : ContinuousOn (fun z : ℝ => (z * L12dens g z) ^ 2 * (Work.Spaces.w z) ^ 2)
          (Set.Ioi (0:ℝ)) := by
        refine ContinuousOn.mul (ContinuousOn.pow (continuousOn_id.mul hcontd) 2) ?_
        simp only [Work.Spaces.w]
        refine ContinuousOn.pow ?_ 2
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro z hz
        exact pow_ne_zero 2 (ne_of_gt hz)
      refine MeasureTheory.AEStronglyMeasurable.congr
        (hcont1.aemeasurable measurableSet_Ioi).aestronglyMeasurable ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
      have hz0 : z ≠ 0 := ne_of_gt hz
      change (z * L12dens g z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
      rw [← Qang0_eq g hz0]
    obtain ⟨hMasterInt, hMasterBound⟩ :=
      Work.Elliptic.integrableOn_w_sq_mul_int_sq α g hsm hmem (j := 0) (by norm_num)
    have hMasterInt' : MeasureTheory.IntegrableOn (fun z => AK * ((Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2))) Work.Spaces.Iz :=
      hMasterInt.const_mul AK
    have hQint : MeasureTheory.IntegrableOn
        (fun z => (Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hMasterInt' hQaesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h | h
      · subst h
        simp [Work.Spaces.w]
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        have hcs := Work.Elliptic.Qang_sq_le g hsm 0 (z := z) (by linarith)
        have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := by
          have := Work.Elliptic.one_le_w h
          nlinarith
        calc (Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ (AK * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2))
                * (Work.Spaces.w z) ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
              simpa only [hAK] using hcs
          _ = AK * ((Work.Spaces.w z) ^ 2
                * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2)) := by ring
    have hAKnn : 0 ≤ AK := by
      rw [hAK]
      refine MeasureTheory.integral_nonneg_of_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
    have hQbound : (∫ z in Work.Spaces.Iz, (Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 4 g := by
      refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hMasterInt' ?_) ?_
      · exact Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
        rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h | h
        · subst h
          simp [Work.Spaces.w]
        · have hcs := Work.Elliptic.Qang_sq_le g hsm 0 (z := z) (by linarith)
          calc (Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
              ≤ (AK * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2))
                  * (Work.Spaces.w z) ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                simpa only [hAK] using hcs
            _ = AK * ((Work.Spaces.w z) ^ 2
                  * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2)) := by ring
      · rw [MeasureTheory.integral_const_mul]
        exact mul_le_mul_of_nonneg_left hMasterBound hAKnn
    obtain ⟨hsin, hInt0, hk0⟩ := Work.Elliptic.L12k0 α g hsm hmem hint hderiv hcontd hcontu htend h0 hQint
    have hIntHigh : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧ (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter i (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ AK * Work.Spaces.HkSq α 4 g :=
      fun i hi hi4 => Work.Elliptic.L12TermHigh α g hsm hmem hid hi hi4
    have hIntEach : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz := by
      intro i hi
      rw [Finset.mem_range] at hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact hInt0
      · exact (hIntHigh i h (by omega)).1
    have hSig : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
          (Work.Elliptic.DzdIter i (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 111 * AK * Work.Spaces.HkSq α 4 g := by
      rw [MeasureTheory.integral_finsetSum (Finset.range 5) hIntEach]
      rw [Finset.sum_range_succ']
      have h0 : (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 0 (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 107 * AK * Work.Spaces.HkSq α 4 g :=
        le_trans hk0 (by linarith [hQbound])
      have hhigh : ∀ i ∈ Finset.range 4, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter (i + 1) (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ AK * Work.Spaces.HkSq α 4 g := by
        intro i hi
        rw [Finset.mem_range] at hi
        exact (hIntHigh (i + 1) (by omega) (by omega)).2
      refine le_trans (add_le_add (Finset.sum_le_sum hhigh) h0) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have hCθnn : 0 ≤ Cθ := by
      rw [hCθ]
      refine MeasureTheory.integral_nonneg_of_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
    have hC1 : 0 ≤ Cθ * (111 * AK) := mul_nonneg hCθnn (mul_nonneg (by norm_num) hAKnn)
    refine ⟨?_, ?_⟩
    · constructor
      · intro z hz
        change MeasureTheory.Integrable
          (fun θ => Work.Spaces.HkIntegrand α 4 hh z θ) (volume.restrict Work.Spaces.Iθ)
        refine MeasureTheory.Integrable.congr
          (f := fun θ => ((∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2)
              * (Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
        · exact hsin.const_mul _
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
          beta_reduce
          rw [hhu, Work.Elliptic.HkIntegrand_rad α 4 u z hθ]
      · change MeasureTheory.Integrable
          (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 hh z θ)
          (volume.restrict Work.Spaces.Iz)
        refine MeasureTheory.Integrable.congr
          (f := fun z => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ) ?_ ?_
        · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hIntEach).mul_const Cθ
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
          simp only [Work.Spaces.Iθ, hCθ]
          rw [setIntegral_congr_fun
            (f := fun θ => Work.Spaces.HkIntegrand α 4 hh z θ)
            (g := fun θ => ((∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2)
              * (Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            measurableSet_Icc (fun θ hθ => by
              beta_reduce
              rw [hhu, Work.Elliptic.HkIntegrand_rad α 4 u z hθ])]
          rw [MeasureTheory.integral_const_mul, ← Finset.sum_mul]
    · have hHkSq_eq := Work.Elliptic.HkSq_rad α 4 (fun z => L12 g z)
      have hK : Work.Spaces.HkSq α 4 (fun z θ => L12 g z)
          ≤ Cθ * (111 * AK) * Work.Spaces.HkSq α 4 g := by
        rw [hHkSq_eq]
        have h2 : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
            ≤ 111 * AK * Work.Spaces.HkSq α 4 g := hSig
        calc (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ
            ≤ (111 * AK * Work.Spaces.HkSq α 4 g) * Cθ :=
              mul_le_mul_of_nonneg_right h2 hCθnn
          _ = Cθ * (111 * AK) * Work.Spaces.HkSq α 4 g := by ring
      have hsqrt : Real.sqrt (Cθ * (111 * AK)) ≤ 1 + Cθ * (111 * AK) := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith [sq_nonneg (Cθ * (111 * AK))]
      calc Work.Spaces.HkNorm α 4 (fun z θ => L12 g z)
          = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => L12 g z)) := rfl
        _ ≤ Real.sqrt (Cθ * (111 * AK) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hK
        _ = Real.sqrt (Cθ * (111 * AK)) * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
              rw [Real.sqrt_mul (x := Cθ * (111 * AK)) (y := Work.Spaces.HkSq α 4 g) hC1]
        _ ≤ (1 + Cθ * (111 * AK)) * Real.sqrt (Work.Spaces.HkSq α 4 g) :=
              mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
        _ = (1 + (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              * (111 * (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2))) * Work.Spaces.HkNorm α 4 g := by
              simp only [hCθ, hAK, Work.Spaces.HkNorm]

end Work.Elliptic
