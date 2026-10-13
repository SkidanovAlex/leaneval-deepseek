import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
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

/-- **The `L¹`-bound for the angular slices of `D_z²G`.**

`TraceClass G` carries, as its last component, `SliceHonestOpen G`, whose *second* conjunct is
exactly the honesty of the `D_z(D_zG)`-slice with the full weight `(w z)² sin(2θ)^{-η}`:

  `IntegrableOn (fun θ => (D_z(D_z G) z θ)² * (w z)² * thEta θ) Iθ`  for `z > 0`.

Dividing the constant weight `(w z)² > 0` off and rewriting `thEta θ = sin(2θ)^{-99/100}` puts
this in the shape required by the weighted Cauchy–Schwarz inequality
`Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted`, which bounds
`∫_{Iθ} |D_z²G|` by `√(π/2) · √(∫_{Iθ} (D_z²G)² thEta)`.  Since `1 ≤ (w z)²` for `z > 0`, the
weighted square integral is dominated by `ddIntS G z`, and `√a ≤ 1 + a` turns the square root
into the affine bound `1 + ddIntS G z`.  The constant `4` absorbs `√(π/2) < 2`.

The first conjunct is the radial local integrability of `1 + ddIntS G z`, which is exactly the
`ddIntS`-component of `FourInts G`, restricted to `[a,b] ⊆ [0,∞)`. -/
theorem ddG_sliceL1_bound {G : ℝ → ℝ → ℝ} (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    ∃ C : ℝ, 0 < C ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
        (fun w => C * (1 + Work.EllipticEst.Core.ddIntS G w)) (Set.Icc a b)) ∧
      (∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.Spaces.Dz G) w s| ≤ C * (1 + Work.EllipticEst.Core.ddIntS G w)) := by
  obtain ⟨-, -, -, -, -, -, -, hhon⟩ := hT
  refine ⟨4, by norm_num, ?_, ?_⟩
  · -- ## local integrability of `4 * (1 + ddIntS G)`
    intro a b ha hab
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun w hw => le_trans ha.le hw.1
    have hd : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) (Set.Icc a b) :=
      (hF.2.1).mono_set hsub
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    change MeasureTheory.Integrable
      (fun w : ℝ => 4 * (1 + Work.EllipticEst.Core.ddIntS G w))
      (volume.restrict (Set.Icc a b))
    exact (h1.add hd).const_mul 4
  · -- ## the `L¹`-bound for the slice of `D_z²G`
    intro w hw
    have hW2pos : 0 < (Work.Spaces.w w) ^ 2 := pow_pos (Work.FTS.EllSol.EllPkgAux.w_pos hw) 2
    have hW2ne : (Work.Spaces.w w) ^ 2 ≠ 0 := ne_of_gt hW2pos
    -- honesty of the `D_z²G`-slice, with the radial weight stripped off
    have hdd : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      have h0 := (hhon.2.1 w hw).const_mul (((Work.Spaces.w w) ^ 2)⁻¹)
      refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show ((Work.Spaces.w w) ^ 2)⁻¹
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
        = (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      rw [show (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2
              * ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) from by ring]
      rw [← mul_assoc, inv_mul_cancel₀ hW2ne, one_mul]
    -- the same integrability with the weight written out
    have hdd2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ] at hdd
      exact hdd.congr (Filter.Eventually.of_forall (fun θ => by
        show (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]))
    -- the weighted Cauchy–Schwarz bound
    have hAbs := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
      (h := fun s : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) w s) hdd2
    have hSnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
      intro θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.EllPkgAux.thEta_nonneg_of_mem_Iθ hθ)
    have hddIntS_eq : Work.EllipticEst.Core.ddIntS G w
        = (Work.Spaces.w w) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := rfl
    have hSle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ Work.EllipticEst.Core.ddIntS G w := by
      rw [hddIntS_eq]
      exact le_mul_of_one_le_left hSnn (Work.FTS.EllSol.EllPkgAux.one_le_w_sq hw)
    -- the two forms of the weight
    have haux : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      rw [Work.Spaces.Iθ]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
      intro θ _
      simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
    have hs : Real.sqrt (Real.pi / 2) ≤ 4 := by
      have h2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
        calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
              Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
          _ = 2 := Real.sqrt_sq (by norm_num)
      linarith
    calc (∫ s in Work.Spaces.Iθ, |Work.Spaces.Dz (Work.Spaces.Dz G) w s|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
          show (∫ s in Set.Icc (0 : ℝ) (Real.pi / 2),
              |Work.Spaces.Dz (Work.Spaces.Dz G) w s|) ≤ _
          rw [← haux]
          exact hAbs
      _ ≤ Real.sqrt (Real.pi / 2) * (1 + Work.EllipticEst.Core.ddIntS G w) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)
              ≤ 1 + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ) :=
                Work.FTS.EllSol.EllPkgAux.sqrt_le_one_add_self hSnn
            _ ≤ 1 + Work.EllipticEst.Core.ddIntS G w := by linarith
      _ ≤ 4 * (1 + Work.EllipticEst.Core.ddIntS G w) :=
          mul_le_mul_of_nonneg_right hs (by linarith)

end Work.FTS.EllSol.EllPkgAux.MollDom
