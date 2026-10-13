import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.biotSavart_decay
import Submission.Work.FTS.PressureOn.biotSavartDecayExplicit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

/-- **A uniform-in-time bound for the Biot–Savart field of a bounded, uniformly supported family
of vorticities.**  If all the slices `ω(·,s)`, `s ∈ [0,S]`, are bounded by `M ≥ 0` and vanish off
the closed ball of radius `R`, then there is a single constant `B ≥ 0` bounding
`‖biotSavart (ω(·,s)) x‖` for *all* `s ∈ [0,S]` and *all* `x ∈ ℝ³`.

The point is that the explicit estimate `Work.FTS.PressureOn.biotSavartDecayExplicit` supplies a
constant depending only on `M` and on the radius — never on the slice — so it can be used
simultaneously for every `s`.  Since the statement does not assume `0 ≤ R`, the radius is first
replaced by `R' = max R 0`, which only enlarges the support; the constant is then
`3 M R' (1 + 4R'²)`, and the weight `(1 + ‖x‖²)⁻¹` is dropped because it is `≤ 1`. -/
theorem biotSavart_uniform_bound {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S M R : ℝ} (hM : 0 ≤ M) (hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 S, ∀ x,
      ‖Work.LWP.biotSavart (fun y => ω y s) x‖ ≤ B := by
  -- Step 0: replace the radius `R` by `R' = max R 0 ≥ 0`; this only enlarges the support.
  set R' : ℝ := max R 0 with hR'def
  have hR' : 0 ≤ R' := le_max_right R 0
  have hRR' : R ≤ R' := le_max_left R 0
  refine ⟨3 * M * R' * (1 + 4 * R' ^ 2), by positivity, ?_⟩
  intro s hs x
  have hg : ∀ y, ‖ω y s‖ ≤ M := fun y => hbdd s hs y
  have hsup' : ∀ y, ω y s ≠ 0 → y ∈ Metric.closedBall (0 : Work.LWP.R3) R' := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (hsupp s hs y hy) hRR'
  -- the explicit estimate, with a constant independent of the slice `s`
  have hb := biotSavartDecayExplicit hR' hM hg hsup' x
  refine hb.trans ?_
  have hden : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hC : (0 : ℝ) ≤ 3 * M * R' * (1 + 4 * R' ^ 2) := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2)]
  nlinarith [hC, hden, sq_nonneg ‖x‖]

end Work.FTS.PressureOn.Connect
