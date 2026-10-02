import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mandelbar set lies in the disk of radius `2`

For the quadratic antiholomorphic family `z ↦ z̄² + c`, the critical orbit always starts as
`0 ↦ c`, so a parameter `c` whose critical orbit is bounded must satisfy `‖c‖ ≤ 2`: if `‖c‖ > 2`
the critical orbit diverges to infinity.

The proof uses only the norm lower bound `‖z̄² + c‖ ≥ ‖z‖² - ‖c‖` (`norm_Td_ge`) applied along the
orbit: writing `b n = ‖(Tantibar c)^[n] c‖` for the norms of the orbit *starting at the critical
value* `c`, one has `b 0 = ‖c‖` and `b (n+1) ≥ b n² - ‖c‖`, whence by induction
`b n ≥ ‖c‖ (‖c‖ - 1)^n`.  Since `‖c‖ > 2` this grows without bound, contradicting boundedness of
the critical orbit.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-- Norm lower bound for the mandelbar iterator: `‖z̄² + c‖ ≥ ‖z‖² - ‖c‖`. -/
theorem tantibar_norm_ge (c z : ℂ) :
    ‖z‖ ^ 2 - ‖c‖ ≤ ‖LeanEval.ComplexAnalysis.Tantibar c z‖ :=
  norm_Td_ge 2 c z

/-- **The mandelbar set is contained in the closed disk of radius `2`.**  A parameter `c` whose
critical orbit `n ↦ (Tantibar c)^[n] 0` is bounded satisfies `‖c‖ ≤ 2`. -/
theorem norm_le_two_of_mem_mandelbar {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ‖c‖ ≤ 2 := by
  by_contra hle
  rw [not_le] at hle
  obtain ⟨M, hM⟩ := hc
  have hc0 : LeanEval.ComplexAnalysis.Tantibar c 0 = c := by
    simp [LeanEval.ComplexAnalysis.Tantibar]
  -- One step of the recurrence for the orbit norms, starting at the critical value `c`.
  have hstep : ∀ n : ℕ,
      ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ ^ 2 - ‖c‖ ≤
        ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n+1]) c‖ := by
    intro n
    rw [Function.iterate_succ_apply']
    exact tantibar_norm_ge c ((LeanEval.ComplexAnalysis.Tantibar c)^[n] c)
  -- Geometric lower bound for the orbit norms.
  have hb : ∀ n : ℕ,
      ‖c‖ * (‖c‖ - 1) ^ n ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hpn : (1 : ℝ) ≤ (‖c‖ - 1) ^ n := one_le_pow₀ (by linarith)
        have hRle : ‖c‖ ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ := by
          calc ‖c‖ = ‖c‖ * 1 := (mul_one _).symm
            _ ≤ ‖c‖ * (‖c‖ - 1) ^ n := mul_le_mul_of_nonneg_left hpn (by linarith)
            _ ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ := ih
        calc ‖c‖ * (‖c‖ - 1) ^ (n + 1)
            = ‖c‖ * (‖c‖ - 1) ^ n * (‖c‖ - 1) := by rw [pow_succ]; ring
          _ ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ * (‖c‖ - 1) :=
                mul_le_mul_of_nonneg_right ih (by linarith)
          _ ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ *
                (‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ - 1) :=
                mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ = ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ ^ 2 -
                ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ := by ring
          _ ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ ^ 2 - ‖c‖ := by linarith
          _ ≤ ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n+1]) c‖ := hstep n
  -- Boundedness of the critical orbit, transported to the orbit starting at `c`.
  have hbM : ∀ n : ℕ, ‖((LeanEval.ComplexAnalysis.Tantibar c)^[n]) c‖ ≤ M := by
    intro n
    have h := hM (n + 1)
    rw [Function.iterate_succ_apply, hc0] at h
    exact h
  -- The geometric lower bound diverges, contradiction.
  have htend : Tendsto (fun n : ℕ => ‖c‖ * (‖c‖ - 1) ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < ‖c‖ - 1)).const_mul_atTop
      (by linarith : 0 < ‖c‖)
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop M).exists
  linarith [hb n, hbM n, hn]

end Work.Escape
