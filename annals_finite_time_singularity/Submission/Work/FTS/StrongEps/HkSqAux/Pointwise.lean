/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/HkSqAux/Pointwise.lean`

The pointwise half of **E1** for the log-coordinate mollifier `Jeps ρ ε`: for a profile `f` which
is `C^n` on the open quadrant for every `n` and every `(z,θ) ∈ Quad`,

  `HkIntegrand α k (J_ε f) z θ ≤ e^{2cε} ∫_p Jker ρ ε p · HkIntegrand α k f (z e^{-p₁}) (thShift θ p₂) dp`

(`HkIntegrand_Jeps_le_integral`), together with the elementary bookkeeping it needs:

* the log-coordinate identities `zShift (e^s) p = e^{s-p}`, `thShift (arctan (e^ζ)) p = arctan (e^{ζ-p})`;
* continuity of the two weights and of the weighted slot derivatives on the compact shift regions
  `Kz z ε ×ˢ Kth θ ε` and on the ball `closedBall 0 ε`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.slot_sq_bound
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : ℝ → ℝ → ℝ}

/-! ## The two shifts in the log coordinates -/

theorem zShift_exp (s p : ℝ) : zShift (Real.exp s) p = Real.exp (s - p) := by
  rw [zShift, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]

theorem thShift_arctan_exp (ζ p : ℝ) :
    thShift (Real.arctan (Real.exp ζ)) p = Real.arctan (Real.exp (ζ - p)) := by
  rw [thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]

/-! ## Continuity of the weights on the compact shift region -/

theorem continuousOn_w_region {z θ : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1) (Kz z ε ×ˢ Kth θ ε) := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun q hq => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Kz_subset_pos hz hε hq.1))

theorem continuousOn_sin_rpow_region {z θ ε c : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2)) ^ c) (Kz z ε ×ˢ Kth θ ε) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun q hq => Or.inl (ne_of_gt (sin_two_pos (Kth_subset hθ hq.2))))

theorem continuousOn_wdiv_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_w_region hz hε).div (continuousOn_sin_rpow_region (z := z) (ε := ε) hθ)
    (fun q hq => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos (Kth_subset hθ hq.2)) _))

theorem continuousOn_Wt_region {α z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) (Kz z ε ×ˢ Kth θ ε) := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact (continuousOn_w_region hz hε).mul
    (continuousOn_sin_rpow_region (z := z) (ε := ε) (c := -(Work.Spaces.gam α / 2)) hθ)

/-! ## Continuity of the weighted slots on the compact region -/

theorem continuousOn_wdiv_mixed_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ =>
        Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.mixed j i f q.1 q.2) (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_wdiv_region hz hε hθ).mul
    ((continuousOn_mixed_Quad hf j i).mono (Kz_prod_Kth_subset_Quad hz hε hθ))

theorem continuousOn_Wt_mixed_region {α z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ =>
        Work.Spaces.Wt α q.1 q.2 * Work.Spaces.mixed j i f q.1 q.2)
      (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_Wt_region hz hε hθ).mul
    ((continuousOn_mixed_Quad hf j i).mono (Kz_prod_Kth_subset_Quad hz hε hθ))

/-! ## Continuity of the weighted slots on the ball of the shift -/

theorem continuousOn_shift_ball {z θ ε : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {A : ℝ → ℝ → ℝ} (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) (Kz z ε ×ˢ Kth θ ε)) :
    ContinuousOn (fun p : ℝ × ℝ => A (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
  hA.comp (continuous_shift_pair z θ).continuousOn
    (mapsTo_ball_region hθ (self_mem_Ioo_div_two hz))

/-- Continuity of the unweighted `D_z`-iterates and of the mixed derivatives on the compact
    shift region. -/
theorem continuousOn_DzIter_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.DzIter i f q.1 q.2) (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_mixed_Quad hf i 0).mono (Kz_prod_Kth_subset_Quad hz hε hθ)

theorem continuousOn_mixed_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_mixed_Quad hf j i).mono (Kz_prod_Kth_subset_Quad hz hε hθ)

/-! ## The two slot bounds -/

theorem exp_sq_eq (c X : ℝ) : (Real.exp (c * X)) ^ 2 = Real.exp (2 * c * X) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The *unweighted* slot bound: `D (J_ε f)` is, in `L²` at a fixed point, dominated by the
average of `D f` at the shifted point.  This is `slot_sq_bound` with the constant weight `1`. -/
theorem slot_z_base (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) :
    (Work.Spaces.DzIter i (Jeps ρ ε f) z θ) ^ 2
      ≤ ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  have hcomm : Work.Spaces.DzIter i (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p
          * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2) := by
    have h : Work.Spaces.DzIter i (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.DzIter i f) z θ := by
      have h0 := mixed_Jeps ρ hρ hε hf hz hθ i 0
      simpa only [Work.Spaces.mixed_zero_right] using h0
    rw [h, Jeps_eq_integral ρ ε _ hz hθ]
  have hb := slot_sq_bound (c := 0) ρ hρ hε (fun g => Work.Spaces.DzIter i g)
    (fun _ _ => (1 : ℝ)) f hcomm zero_le_one (fun p => by simp)
    (by
      have h := continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.DzIter i f z' θ')
        (continuousOn_DzIter_region hz hε hθ hf i)
      simpa using h)
  simpa using hb

theorem slot_mixed_base (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    (Work.Spaces.mixed j i (Jeps ρ ε f) z θ) ^ 2
      ≤ ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  have hcomm : Work.Spaces.mixed j i (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p
          * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2) := by
    rw [mixed_Jeps ρ hρ hε hf hz hθ j i, Jeps_eq_integral ρ ε _ hz hθ]
  have hb := slot_sq_bound (c := 0) ρ hρ hε (fun g => Work.Spaces.mixed j i g)
    (fun _ _ => (1 : ℝ)) f hcomm zero_le_one (fun p => by simp)
    (by
      have h := continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.mixed j i f z' θ')
        (continuousOn_mixed_region hz hε hθ hf j i)
      simpa using h)
  simpa using hb

/-- **The `z`-slot bound**: the weighted `i`-th `D_z`-derivative of `J_ε f`, squared, is bounded
by the average of the same slot of `f` at the shifted point, with the weight ratio `e^{2c|p|}`
taken inside the integral (where `|p| ≤ 2ε` on the support of the kernel). -/
theorem slot_z_exp (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ c : ℝ}
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (zShift z p.1)
            / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) :
    (Work.Spaces.DzIter i (Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hWdef
  have hWnn : 0 ≤ W := by
    rw [hWdef]
    exact div_nonneg (by rw [Work.Spaces.w]; positivity)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
  have hbase := slot_z_base (f := f) hρ hε hf hz hθ i
  -- integrability of the two integrands
  have h1int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (W ^ 2 * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2)) :=
    integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      W ^ 2 * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2)
      (((continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.DzIter i f z' θ')
        (continuousOn_DzIter_region hz hε hθ hf i)).pow 2).const_mul (W ^ 2))
  have h2int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.w (zShift z p.1)
        / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2)) := by
    refine integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.w (zShift z p.1)
        / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2) ?_
    have hcont := continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.w z' / (Real.sin (2 * θ')) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter i f z' θ') (continuousOn_wdiv_mixed_region hz hε hθ hf i 0)
    have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
    exact hexp.continuousOn.mul (hcont.pow 2)
  calc (Work.Spaces.DzIter i (Jeps ρ ε f) z θ * W) ^ 2
      = W ^ 2 * (Work.Spaces.DzIter i (Jeps ρ ε f) z θ) ^ 2 := by ring
    _ ≤ W ^ 2 * ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg W)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (W ^ 2 * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.w (zShift z p.1)
            / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)
              * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2) :=
        integral_mono h1int h2int (fun p => by
          refine mul_le_mul_of_nonneg_left ?_ (Jker_nonneg ρ hρ ε p)
          have hWs : 0 ≤ Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2) :=
            div_nonneg (by rw [Work.Spaces.w]; positivity)
              (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
          have h1 : W ≤ Real.exp (c * (|p.1| + |p.2|))
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)) := by
            rw [hWdef]
            exact hW p
          have hsq : W ^ 2 ≤ (Real.exp (c * (|p.1| + |p.2|))
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            pow_le_pow_left₀ hWnn h1 2
          refine mul_le_mul_of_nonneg_right hsq (sq_nonneg _) |>.trans (le_of_eq ?_)
          rw [mul_pow, exp_sq_eq]
          ring)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring

/-- **The mixed-slot bound**, the companion of `slot_z_exp` for the mixed derivatives
`D_z^j D_θ^i f`. -/
theorem slot_mixed_exp (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {z θ c : ℝ}
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ
      ≤ Real.exp (c * (|p.1| + |p.2|)) * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  set W : ℝ := Work.Spaces.Wt α z θ with hWdef
  have hWnn : 0 ≤ W := by
    rw [hWdef, Work.Spaces.Wt]
    exact mul_nonneg (by rw [Work.Spaces.w]; positivity)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
  have hbase := slot_mixed_base (f := f) hρ hε hf hz hθ j i
  have h1int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (W ^ 2 * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2)) :=
    integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      W ^ 2 * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2)
      (((continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.mixed j i f z' θ')
        (continuousOn_mixed_region hz hε hθ hf j i)).pow 2).const_mul (W ^ 2))
  have h2int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2)) := by
    refine integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2) ?_
    have hcont := continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.Wt α z' θ' * Work.Spaces.mixed j i f z' θ')
      (continuousOn_Wt_mixed_region hz hε hθ hf j i)
    have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
    exact hexp.continuousOn.mul (hcont.pow 2)
  calc (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * W) ^ 2
      = W ^ 2 * (Work.Spaces.mixed j i (Jeps ρ ε f) z θ) ^ 2 := by ring
    _ ≤ W ^ 2 * ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg W)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (W ^ 2 * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2) :=
        integral_mono h1int h2int (fun p => by
          refine mul_le_mul_of_nonneg_left ?_ (Jker_nonneg ρ hρ ε p)
          have hWs : 0 ≤ Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
            rw [Work.Spaces.Wt]
            exact mul_nonneg (by rw [Work.Spaces.w]; positivity)
              (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
          have h1 : W ≤ Real.exp (c * (|p.1| + |p.2|))
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
            rw [hWdef]
            exact hW p
          have hsq : W ^ 2 ≤ (Real.exp (c * (|p.1| + |p.2|))
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2 :=
            pow_le_pow_left₀ hWnn h1 2
          refine mul_le_mul_of_nonneg_right hsq (sq_nonneg _) |>.trans (le_of_eq ?_)
          rw [mul_pow, exp_sq_eq]
          ring)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring

end Work.FTS.StrongEps.HkSqAux
