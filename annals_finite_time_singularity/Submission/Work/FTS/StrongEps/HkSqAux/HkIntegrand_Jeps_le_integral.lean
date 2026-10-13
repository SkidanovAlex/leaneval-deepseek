/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/HkSqAux/HkIntegrand_Jeps_le_integral.lean`

The weighted pointwise `E1` bound for the log-coordinate mollifier `Jeps ρ ε`, in the form of a
single inequality for the whole `H^k`-integrand: for a profile `f` which is `C^n` on the open
quadrant for every `n` and every `(z,θ) ∈ Quad`,

  `HkIntegrand α k (J_ε f) z θ
     ≤ ∫ p, Jker ρ ε p · e^{2c(|p₁|+|p₂|)} · HkIntegrand α k f (z e^{-p₁}) (thShift θ p₂) dp`

where the weights `w z / sin(2θ)^{η/2}` and `Wt α z θ = w z · sin(2θ)^{-γ/2}` are the paper's,
and the hypotheses `hWη`, `hWγ` are exactly the two shift-comparison inequalities for those
weights (they hold with a universal `c`, cf. `HkSqAux/wdiv_shift_le.lean` and
`HkSqAux/Wt_shift_le.lean`).

This is the "sum of the single-slot bounds" companion of
`Submission/Work/FTS/StrongEps/HkSqAux/Pointwise.lean`, where the two kinds of slot
(`D_z`-slots and mixed slots) are controlled separately by `slot_z_exp` and `slot_mixed_exp`.

## Proof structure

`HkIntegrand` is, by definition, the sum of its `D_z`-part `HkZPart` and its mixed part
`HkMPart`; the latter is also written as a sum `HkMPartF` over the *filtered* set of admissible
pairs `(i,j)` (`HkMPart_eq_HkMPartF`), which is the form in which the per-slot bounds
(`slot_z_exp`, `slot_mixed_exp`) are applied.

* `sum_le_integral_of_slots` — the abstract bookkeeping: if each of the finitely many slots is
  bounded by the corresponding integral and each of those integrands is integrable, then so is
  the whole sum.  (It is `Finset.sum_le_sum` followed by `integral_finsetSum`, and
  `Finset.mul_sum` to pull the kernel out of the finite sum.)
* `integrable_kernel_mul_slot_sum` — the same exchange for integrability alone.
* `integrable_slot_z_exp`, `integrable_slot_mixed_exp` — the two slot integrands are integrable
  (`integrable_Jker_mul` + the continuity of the shifted weighted slot on the ball of radius
  `ε`, which is `continuousOn_shift_ball` applied to the slot-continuity lemmas of `Pointwise`).
* the two halves `hZ`, `hM` of the estimate, and the final assembly: the integral of the sum is
  the sum of the integrals, and `HkZPart + HkMPart` is `HkIntegrand`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.HkSqAux.Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option maxHeartbeats 1000000

/-! ## The two parts of `HkIntegrand` -/

/-- The `D_z`-part of `HkIntegrand`: the sum of the squared weighted `D_z`-slots. -/
def HkZPart (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed part of `HkIntegrand`: the sum over the admissible pairs `(i,j)` of the squared
weighted mixed slots (`i ≥ 1`, `i + j ≤ k`), the inadmissible pairs contributing `0`. -/
def HkMPart (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    if 1 ≤ i ∧ i + j ≤ k then
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0

/-- The mixed part of `HkIntegrand` as a sum over the *filtered* set of admissible pairs
`(i,j)`: the form in which the per-slot bounds apply (no `if`). -/
def HkMPartF (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ q ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
      (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k),
    (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2

theorem HkIntegrand_eq_parts (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ = HkZPart k f z θ + HkMPart α k f z θ := rfl

theorem HkMPart_eq_HkMPartF (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkMPart α k f z θ = HkMPartF α k f z θ := by
  simp only [HkMPart, HkMPartF]
  rw [Finset.sum_filter, Finset.sum_product]

/-! ## Two elementary `Finset`-versus-integral lemmas -/

/-- **Summation of finitely many slot bounds.**  If the slots `a i` are dominated by the
integrals of `K · F i`, and each of those integrands is integrable, then the sum of the slots is
dominated by `∫ p, K p · ∑ i, F i p`.

This is `Finset.sum_le_sum` followed by the exchange of the finite sum with the integral
(`integral_finsetSum`) and `Finset.mul_sum` to pull the factor `K p` out of the finite sum. -/
theorem sum_le_integral_of_slots {ι : Type*} (K : ℝ × ℝ → ℝ) (s : Finset ι) (a : ι → ℝ)
    (F : ι → ℝ × ℝ → ℝ)
    (h : ∀ i ∈ s, a i ≤ ∫ p : ℝ × ℝ, K p * F i p)
    (hint : ∀ i ∈ s, Integrable (fun p : ℝ × ℝ => K p * F i p)) :
    ∑ i ∈ s, a i ≤ ∫ p : ℝ × ℝ, K p * ∑ i ∈ s, F i p := by
  calc ∑ i ∈ s, a i ≤ ∑ i ∈ s, ∫ p : ℝ × ℝ, K p * F i p := Finset.sum_le_sum h
    _ = ∫ p : ℝ × ℝ, ∑ i ∈ s, K p * F i p :=
        (MeasureTheory.integral_finsetSum s hint).symm
    _ = ∫ p : ℝ × ℝ, K p * ∑ i ∈ s, F i p := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        exact (Finset.mul_sum s (fun i => F i p) (K p)).symm

/-- Integrability of `p ↦ K p · ∑ i ∈ s, F i p` from the integrability of each of the terms.
The proof exchanges the finite sum with the integral (as a sum of functions). -/
theorem integrable_kernel_mul_slot_sum {ι : Type*} (K : ℝ × ℝ → ℝ) (s : Finset ι)
    (F : ι → ℝ × ℝ → ℝ) (hint : ∀ i ∈ s, Integrable (fun p : ℝ × ℝ => K p * F i p)) :
    Integrable (fun p : ℝ × ℝ => K p * ∑ i ∈ s, F i p) := by
  have h : (fun p : ℝ × ℝ => K p * ∑ i ∈ s, F i p)
      = fun p : ℝ × ℝ => ∑ i ∈ s, K p * F i p := by
    funext p
    exact Finset.mul_sum s (fun i => F i p) (K p)
  rw [h]
  exact MeasureTheory.integrable_finsetSum s hint

/-! ## Integrability of the two slot integrands -/

/-- The right-hand integrand of `slot_z_exp` is integrable: it is
`Jker ρ ε p · (e^{2c|p|} · (weighted slot)²)`, and the second factor is continuous on the
compact ball of radius `ε` (`integrable_Jker_mul`). -/
theorem integrable_slot_z_exp (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ c : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (i : ℕ) :
    Integrable (fun p : ℝ × ℝ => (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
            * (Work.Spaces.w (zShift z p.1)
                / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  refine (integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|))
        * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
            * (Work.Spaces.w (zShift z p.1)
                / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2) ?_).congr
    (Eventually.of_forall fun p => by ring)
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
        * (Work.Spaces.w (zShift z p.1)
            / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.DzIter i f z' θ'
        * (Work.Spaces.w z' / (Real.sin (2 * θ')) ^ (Work.Spaces.eta / 2)))
      ((continuousOn_DzIter_region hz hε hθ hf i).mul
        (continuousOn_wdiv_region (z := z) (ε := ε) hz hε hθ))
  have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
  exact hexp.continuousOn.mul (hcont.pow 2)

/-- The right-hand integrand of `slot_mixed_exp` is integrable (companion of
`integrable_slot_z_exp`). -/
theorem integrable_slot_mixed_exp (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {α z θ c : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j i : ℕ) :
    Integrable (fun p : ℝ × ℝ => (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
            * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
  refine (integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|))
        * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
            * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) ?_).congr
    (Eventually.of_forall fun p => by ring)
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.mixed j i f z' θ' * Work.Spaces.Wt α z' θ')
      ((continuousOn_mixed_region hz hε hθ hf j i).mul
        (continuousOn_Wt_region (z := z) (ε := ε) (α := α) hz hε hθ))
  have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
  exact hexp.continuousOn.mul (hcont.pow 2)

/-! ## The estimate -/

theorem HkIntegrand_Jeps_le_integral (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) {z θ c : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (k : ℕ)
    (hWη : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  -- the `D_z`-half: sum the single-slot bounds `slot_z_exp`
  have hZ : HkZPart k (Jeps ρ ε f) z θ ≤ ∫ p : ℝ × ℝ,
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkZPart k f (zShift z p.1) (thShift θ p.2) :=
    sum_le_integral_of_slots
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := Finset.range (k + 1))
      (a := fun i => (Work.Spaces.DzIter i (Jeps ρ ε f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (F := fun i p => (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => slot_z_exp (ρ := ρ) (ε := ε) (f := f) hρ hε hf hWη hz hθ i)
      (fun i _ => integrable_slot_z_exp ρ hρ hε hf hz hθ i)
  -- the mixed half: sum the single-slot bounds `slot_mixed_exp` over the admissible pairs
  have hM : HkMPartF α k (Jeps ρ ε f) z θ ≤ ∫ p : ℝ × ℝ,
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkMPartF α k f (zShift z p.1) (thShift θ p.2) :=
    sum_le_integral_of_slots
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
        (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k))
      (a := fun q : ℕ × ℕ =>
        (Work.Spaces.mixed q.2 q.1 (Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2)
      (F := fun q : ℕ × ℕ => fun p : ℝ × ℝ =>
        (Work.Spaces.mixed q.2 q.1 f (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
      (fun q _ => slot_mixed_exp (ρ := ρ) (ε := ε) (f := f) hρ hε hf hα hWγ hz hθ q.2 q.1)
      (fun q _ => integrable_slot_mixed_exp ρ hρ hε hf hz hθ q.2 q.1)
  -- integrability of the two assembled integrands
  have hintZ : Integrable (fun p : ℝ × ℝ =>
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkZPart k f (zShift z p.1) (thShift θ p.2)) :=
    integrable_kernel_mul_slot_sum
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := Finset.range (k + 1))
      (F := fun i p => (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => integrable_slot_z_exp ρ hρ hε hf hz hθ i)
  have hintM : Integrable (fun p : ℝ × ℝ =>
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkMPartF α k f (zShift z p.1) (thShift θ p.2)) :=
    integrable_kernel_mul_slot_sum
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
        (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k))
      (F := fun q : ℕ × ℕ => fun p : ℝ × ℝ =>
        (Work.Spaces.mixed q.2 q.1 f (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
      (fun q _ => integrable_slot_mixed_exp ρ hρ hε hf hz hθ q.2 q.1)
  calc Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ
      = HkZPart k (Jeps ρ ε f) z θ + HkMPartF α k (Jeps ρ ε f) z θ := by
        rw [HkIntegrand_eq_parts, HkMPart_eq_HkMPartF]
    _ ≤ (∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkZPart k f (zShift z p.1) (thShift θ p.2))
        + ∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkMPartF α k f (zShift z p.1) (thShift θ p.2) := add_le_add hZ hM
    _ = ∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkZPart k f (zShift z p.1) (thShift θ p.2)
          + (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkMPartF α k f (zShift z p.1) (thShift θ p.2) :=
        (MeasureTheory.integral_add hintZ hintM).symm
    _ = ∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
          * (HkZPart k f (zShift z p.1) (thShift θ p.2)
              + HkMPartF α k f (zShift z p.1) (thShift θ p.2)) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        dsimp only
        rw [← HkMPart_eq_HkMPartF, HkIntegrand_eq_parts]

end Work.FTS.StrongEps.HkSqAux
