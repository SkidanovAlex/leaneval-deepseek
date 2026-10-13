/-
  WilG4c — `StepHigherMain`: the assembly of BNZ §5.4 (`Work.WilkG4c.StepHigher`).

  This file collects the pieces of the §5.4 reduction.  The design is recorded in
  `Submission/Work/WilG4c/StepHigherPlan.md`, notably its §6 (the corrected design):

  * the `γ`-choice is the *pure* near-maximiser of `CurveFamAlpha_list_pure` (BNZ's `S_{i,α}`,
    no threshold — the threshold alternative of `CurveFamAlpha` cannot be validated by the
    engine, see §6.2 of the plan);
  * the `x`-charts are the *shrunk and shifted* charts `φ'(s) = φ(c + s/4)`, `c ∈ {j/10 : j ≤ 15}`,
    which cancel the factor `4` introduced by the surrogate `(∂_M f + 2)/4` (§6.5);
  * the points where no near-maximiser exists (a finite set, by `hbdd_sup_finite`) are handled
    by continuity (`subdiv_normle_multi_bad`);
  * the engine `Work.WilkG4c.curve_bound` is applied to the pair (`pullX F φ'`, `γ ∘ φ'`), which
    makes the base hypothesis `hbase` literally the Corollary 19 conclusion (`h1`).

  This file currently contains the elementary chart algebra and the interfaces; the remaining
  pieces are stated below with `sorry` and are being proved in parallel.
-/
import Mathlib
import Submission.Work.WilG4c.CanonIndex
import Submission.Work.WilG4c.Pullback
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.FLemAPI

set_option autoImplicit false
noncomputable section
open Classical

open scoped BigOperators Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The shrunk and shifted chart `φ'(s) = φ(c + s/4)` -/

/-- The chart shrunk by a factor `4` and shifted by `c`: `φ'(s) = φ(c + s/4)`, i.e. the affine
coefficients `(α + β·c, β/4)` of the chart `α + β·(c + ·/4)`. -/
def shrunkCoeff {p : ℕ} (α β : (Fin p → ℝ) → ℝ) (c : ℝ) :
    ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ) :=
  (fun l => α l + β l * c, fun l => β l / 4)

/-- The shrunk chart point is the original chart point at `c + t 0 / 4` in the `x`-coordinate
(the `y`-coordinates are untouched). -/
theorem chartPt_shrunkCoeff {p n : ℕ} (α β : (Fin p → ℝ) → ℝ) (c : ℝ) (l : Fin p → ℝ)
    (t : Fin (n + 1) → ℝ) :
    chartPt (shrunkCoeff α β c).1 (shrunkCoeff α β c).2 l t
      = chartPt α β l (Fin.cons (c + t 0 / 4) (Fin.tail t)) := by
  rw [chartPt, chartPt]
  simp only [shrunkCoeff, Prod.fst, Prod.snd, pt, Fin.cons_zero, Fin.tail_cons]
  congr 1
  ring

/-- The shrunk chart still maps the open cube into itself (when `0 ≤ c ≤ 3/4`). -/
theorem chartPt_shrunkCoeff_mem_openCube {p n : ℕ} {α β : (Fin p → ℝ) → ℝ} {c : ℝ}
    {l : Fin p → ℝ} (hα : 0 ≤ α l) (hβ : 0 < β l) (hαβ : α l + β l ≤ 1) (hc0 : 0 ≤ c)
    (hc3 : c ≤ 3 / 4) {t : Fin (n + 1) → ℝ} (ht : t ∈ openCube (n + 1)) :
    chartPt (shrunkCoeff α β c).1 (shrunkCoeff α β c).2 l t ∈ openCube (n + 1) := by
  refine chartPt_mem_openCube (n := n) ?_ ?_ ?_ ht
  · simp only [shrunkCoeff, Prod.fst]
    have := mul_nonneg hc0 hβ.le
    linarith
  · simp only [shrunkCoeff, Prod.snd]
    linarith
  · simp only [shrunkCoeff, Prod.fst, Prod.snd]
    nlinarith

/-! ## 2. Composing affine `x`-pullbacks -/

/-- Two successive affine `x`-pullbacks are one affine `x`-pullback. -/
theorem pullX_pullX {k p n : ℕ} (F : Family k p (n + 1)) (α β α' β' : (Fin p → ℝ) → ℝ) :
    pullX (pullX F α β) α' β'
      = pullX F (fun l => α l + β l * α' l) (fun l => β l * β' l) := by
  funext i l t
  rw [pullX_apply, pullX_apply, pullX_apply]
  simp only [chartPt, pt, Fin.cons_zero, Fin.tail_cons]
  congr 1
  ring

end Work.WilkG4c
