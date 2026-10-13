import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.StepFacts.SlotAux.RouteAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- context: namespace Work.FTS.StrongEps.StepFacts. `mixed j i = D_z^j D_θ^i`, `DthIter i = D_θ^i`,
-- `Wt α z θ = w z * sin(2θ)^{-γ/2}` with `w z = (1+z)²/z²`; the conclusions are stated as a triple conjunction.
theorem slot_route_bounds (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) :
    (∀ {α c z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
      {j i : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i)
      (hcomm : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = ∫ p : ℝ × ℝ,
            deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
            * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))
      (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)),
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ (∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
          * ∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
    ∧ (∀ {c z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
      {j : ℕ} (hj : 1 ≤ j)
      (hcomm : Work.Spaces.DzIter j (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = ∫ p : ℝ × ℝ,
            deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
            * Work.Spaces.DzIter (j - 1) f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))
      (hW : ∀ p : ℝ × ℝ,
        Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          ≤ Real.exp (c * (|p.1| + |p.2|))
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2))),
      (Work.Spaces.DzIter j (Work.FTS.StrongEps.Jeps ρ ε f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
          * ∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.DzIter (j - 1) f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                    / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                      ^ (Work.Spaces.eta / 2))) ^ 2)
    ∧ (∀ {α c z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
      {i : ℕ} (hi : 2 ≤ i)
      (hcomm : Work.Spaces.DthIter i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = 2 * ∫ p : ℝ × ℝ,
            deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2
            * Work.Spaces.DthIter (i - 1) f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))
      (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)),
      (Work.Spaces.DthIter i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 4 * (∫ p : ℝ × ℝ,
              |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|)
          * ∫ p : ℝ × ℝ,
              |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.DthIter (i - 1) f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the mixed `z`-slots, with the `Wt`-weight
    intro α c z θ hz hθ j i hj hi hcomm hW
    have hKint : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|) := by
      simpa only [mul_one] using
        srb_integrable_abs_deriv_fst_mul ρ hρ hε
          (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.mixed (j - 1) i f x y)
        (HkSqAux.continuousOn_mixed_region hz hε hθ hf (j - 1) i)
    have hWc : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ (A := fun x y => Work.Spaces.Wt α x y)
        (HkSqAux.continuousOn_Wt_region hz hε hθ)
    have hQ : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
      have hB : ContinuousOn (fun p : ℝ × ℝ =>
          Real.exp (2 * c * (|p.1| + |p.2|))
            * (Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2)
                * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
          (Metric.closedBall (0 : ℝ × ℝ) ε) :=
        (srb_continuous_exp_two c).continuousOn.mul ((hG.mul hWc).pow 2)
      simpa only [mul_assoc] using srb_integrable_abs_deriv_fst_mul ρ hρ hε hB
    have hK2 : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * (Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α z θ) ^ 2) :=
      srb_integrable_abs_deriv_fst_mul ρ hρ hε
        ((hG.mul continuousOn_const).pow 2)
    exact srb_cs_core
      (K := fun p : ℝ × ℝ => deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1)
      (G := fun p : ℝ × ℝ =>
        Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2))
      (W := fun p : ℝ × ℝ => Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (W₀ := Work.Spaces.Wt α z θ) (c := c)
      (M := Work.Spaces.mixed j i (Jeps ρ ε f) z θ)
      (srb_Wt_nonneg α hz hθ) hW hKint hQ hK2 hcomm
  · -- the pure `z`-slots, with the `η`-weight
    intro c z θ hz hθ j hj hcomm hW
    have hKint : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|) := by
      simpa only [mul_one] using
        srb_integrable_abs_deriv_fst_mul ρ hρ hε
          (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.DzIter (j - 1) f x y)
        (HkSqAux.continuousOn_DzIter_region hz hε hθ hf (j - 1))
    have hWc : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.w (zShift z p.1)
          / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.w x / (Real.sin (2 * y)) ^ (Work.Spaces.eta / 2))
        (HkSqAux.continuousOn_wdiv_region hz hε hθ)
    have hQ : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      have hB : ContinuousOn (fun p : ℝ × ℝ =>
          Real.exp (2 * c * (|p.1| + |p.2|))
            * (Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2)
                * (Work.Spaces.w (zShift z p.1)
                    / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (Metric.closedBall (0 : ℝ × ℝ) ε) :=
        (srb_continuous_exp_two c).continuousOn.mul ((hG.mul hWc).pow 2)
      simpa only [mul_assoc] using srb_integrable_abs_deriv_fst_mul ρ hρ hε hB
    have hK2 : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * (Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      srb_integrable_abs_deriv_fst_mul ρ hρ hε
        ((hG.mul continuousOn_const).pow 2)
    exact srb_cs_core
      (K := fun p : ℝ × ℝ => deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1)
      (G := fun p : ℝ × ℝ => Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2))
      (W := fun p : ℝ × ℝ =>
        Work.Spaces.w (zShift z p.1)
          / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))
      (W₀ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) (c := c)
      (M := Work.Spaces.DzIter j (Jeps ρ ε f) z θ)
      (srb_wdiv_nonneg hz hθ) hW hKint hQ hK2 hcomm
  · -- the pure `θ`-slots, with the `Wt`-weight and the factor `2` of the routed identity
    intro α c z θ hz hθ i hi hcomm hW
    have hKint : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2|) := by
      simpa only [mul_one] using
        srb_integrable_abs_deriv_snd_mul ρ hρ hε
          (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.DthIter (i - 1) f x y)
        (HkSqAux.continuousOn_mixed_region hz hε hθ hf 0 (i - 1))
    have hWc : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ (A := fun x y => Work.Spaces.Wt α x y)
        (HkSqAux.continuousOn_Wt_region hz hε hθ)
    have hQ : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
      have hB : ContinuousOn (fun p : ℝ × ℝ =>
          Real.exp (2 * c * (|p.1| + |p.2|))
            * (Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2)
                * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
          (Metric.closedBall (0 : ℝ × ℝ) ε) :=
        (srb_continuous_exp_two c).continuousOn.mul ((hG.mul hWc).pow 2)
      simpa only [mul_assoc] using srb_integrable_abs_deriv_snd_mul ρ hρ hε hB
    have hK2 : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2|
          * (Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α z θ) ^ 2) :=
      srb_integrable_abs_deriv_snd_mul ρ hρ hε
        ((hG.mul continuousOn_const).pow 2)
    rw [hcomm]
    exact srb_cs_core_four
      (K := fun p : ℝ × ℝ => deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2)
      (G := fun p : ℝ × ℝ =>
        Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2))
      (W := fun p : ℝ × ℝ => Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (W₀ := Work.Spaces.Wt α z θ) (c := c)
      (I := ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2
        * Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2))
      (srb_Wt_nonneg α hz hθ) hW hKint hQ hK2 rfl

end Work.FTS.StrongEps.StepFacts
