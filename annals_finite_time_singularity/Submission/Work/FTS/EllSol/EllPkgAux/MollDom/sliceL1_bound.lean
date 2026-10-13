import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.EllipticEst.Core.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The integral of a constant over the angular interval. -/
theorem integral_Iθ_const (c : ℝ) : ∫ s in Work.Spaces.Iθ, c = c * (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- The `L¹`-bound for the angular slices of a trace-class datum: the slice of `G`, and the
slice of `D_zG`, are dominated by the local (`L¹` in `w`) functions `MGf G` and
`1 + dIntS G` respectively.  Both are ``honest'' integrals (the slice integrands are
integrable by the honesty component `SliceHonestOpen` of `TraceClass`), and the constant is
the one of `mollSliceBound` inflated by the length `π/2 ≤ 3` of the angular interval and by
the Cauchy–Schwarz factor `√(π/2) ≤ 2`. -/
theorem sliceL1_bound {G : ℝ → ℝ → ℝ} (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    ∃ C : ℝ, 0 < C ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn (fun w => C * Work.FTS.EllSol.EllPkgAux.MGf G w) (Set.Icc a b)) ∧
      (∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ, |G w s| ≤ C * Work.FTS.EllSol.EllPkgAux.MGf G w) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
        (fun w => C * (1 + Work.EllipticEst.Core.dIntS G w)) (Set.Icc a b)) ∧
      (∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ, |Work.Spaces.Dz G w s| ≤ C * (1 + Work.EllipticEst.Core.dIntS G w)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
  obtain ⟨hsl, hintMG⟩ := hC₀ G hT hF
  obtain ⟨-, -, -, -, -, -, -, hhon⟩ := hT
  refine ⟨3 * C₀ + 3, by linarith, ?_, ?_, ?_, ?_⟩
  · -- ## local integrability of `C * MGf G`
    intro a b ha hab
    change MeasureTheory.Integrable
      (fun w : ℝ => (3 * C₀ + 3) * Work.FTS.EllSol.EllPkgAux.MGf G w)
      (volume.restrict (Set.Icc a b))
    exact (hintMG a b ha hab).const_mul (3 * C₀ + 3)
  · -- ## the `L¹`-bound for the slice of `G`
    intro w hw
    have hMGnn : 0 ≤ Work.FTS.EllSol.EllPkgAux.MGf G w := by
      have h2 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
      have h3 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
      have h4 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := Real.sqrt_nonneg _
      simp only [Work.FTS.EllSol.EllPkgAux.MGf]
      linarith
    have hone_int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ)
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    have hconst_int : MeasureTheory.IntegrableOn
        (fun _ : ℝ => C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) Work.Spaces.Iθ := by
      change MeasureTheory.Integrable
        (fun _ : ℝ => C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) (volume.restrict Work.Spaces.Iθ)
      simpa only [mul_one] using
        hone_int.const_mul (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w)
    have hmono : (∫ s in Work.Spaces.Iθ, |G w s|)
        ≤ ∫ s in Work.Spaces.Iθ, C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w :=
      MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun s : ℝ => |G w s|)
        (g := fun _ : ℝ => C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w)
        (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hconst_int
        (by
          filter_upwards [Work.FTS.EllSol.EllPkgAux.ae_mem_Ioo_Iθ] with s hs
          exact hsl w hw s hs.1 hs.2)
    have hstep : (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * (Real.pi / 2)
        ≤ (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * 3 := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt hC₀pos) hMGnn)
      linarith [Real.pi_lt_four]
    have hstep2 : (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * 3
        ≤ (3 * C₀ + 3) * Work.FTS.EllSol.EllPkgAux.MGf G w := by
      nlinarith [hC₀pos, hMGnn]
    calc (∫ s in Work.Spaces.Iθ, |G w s|)
        ≤ ∫ s in Work.Spaces.Iθ, C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w := hmono
      _ = (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * (Real.pi / 2) := integral_Iθ_const _
      _ ≤ (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * 3 := hstep
      _ ≤ (3 * C₀ + 3) * Work.FTS.EllSol.EllPkgAux.MGf G w := hstep2
  · -- ## local integrability of `C * (1 + dIntS G)`
    intro a b ha hab
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun w hw => le_trans ha.le hw.1
    have hd : MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z)
        (Set.Icc a b) := (hF.2.2.2).mono_set hsub
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    change MeasureTheory.Integrable
      (fun w : ℝ => (3 * C₀ + 3) * (1 + Work.EllipticEst.Core.dIntS G w))
      (volume.restrict (Set.Icc a b))
    exact (h1.add hd).const_mul (3 * C₀ + 3)
  · -- ## the `L¹`-bound for the slice of `D_zG`
    intro w hw
    have hW2pos : 0 < (Work.Spaces.w w) ^ 2 := pow_pos (Work.FTS.EllSol.EllPkgAux.w_pos hw) 2
    have hW2ne : (Work.Spaces.w w) ^ 2 ≠ 0 := ne_of_gt hW2pos
    -- honesty of the `D_zG`-slice, with the radial weight stripped off
    have hDz : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ := by
      have h0 := (hhon.2.2 w hw).const_mul (((Work.Spaces.w w) ^ 2)⁻¹)
      refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show ((Work.Spaces.w w) ^ 2)⁻¹ * ((Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      rw [show (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * ((Work.Spaces.Dz G w θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) from by ring]
      rw [← mul_assoc, inv_mul_cancel₀ hW2ne, one_mul]
    -- the same integrability with the weight written out
    have hDz2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ] at hDz
      exact hDz.congr (Filter.Eventually.of_forall (fun θ => by
        show (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.Dz G w θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]))
    -- the weighted Cauchy–Schwarz bound
    have hAbs := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
      (h := fun s : ℝ => Work.Spaces.Dz G w s) hDz2
    have hSnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
      intro θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.EllPkgAux.thEta_nonneg_of_mem_Iθ hθ)
    have hdIntS_eq : Work.EllipticEst.Core.dIntS G w
        = (Work.Spaces.w w) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
    have hDnn : 0 ≤ Work.EllipticEst.Core.dIntS G w := by
      rw [hdIntS_eq]
      exact mul_nonneg (le_of_lt hW2pos) hSnn
    have hSle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ Work.EllipticEst.Core.dIntS G w := by
      rw [hdIntS_eq]
      exact le_mul_of_one_le_left hSnn (Work.FTS.EllSol.EllPkgAux.one_le_w_sq hw)
    -- the two forms of the weight
    have haux : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.Dz G w θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      rw [Work.Spaces.Iθ]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
      intro θ _
      simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
    have hs : Real.sqrt (Real.pi / 2) ≤ 3 * C₀ + 3 := by
      have h2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
        calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
              Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
          _ = 2 := Real.sqrt_sq (by norm_num)
      linarith
    calc (∫ s in Work.Spaces.Iθ, |Work.Spaces.Dz G w s|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
          show (∫ s in Set.Icc (0 : ℝ) (Real.pi / 2), |Work.Spaces.Dz G w s|) ≤ _
          rw [← haux]
          exact hAbs
      _ ≤ Real.sqrt (Real.pi / 2) * (1 + Work.EllipticEst.Core.dIntS G w) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              ≤ 1 + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
                Work.FTS.EllSol.EllPkgAux.sqrt_le_one_add_self hSnn
            _ ≤ 1 + Work.EllipticEst.Core.dIntS G w := by linarith
      _ ≤ (3 * C₀ + 3) * (1 + Work.EllipticEst.Core.dIntS G w) :=
          mul_le_mul_of_nonneg_right hs (by linarith)

end Work.FTS.EllSol.EllPkgAux.MollDom
