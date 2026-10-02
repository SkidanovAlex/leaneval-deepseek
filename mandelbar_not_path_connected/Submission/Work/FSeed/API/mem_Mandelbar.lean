/-
# Membership of a root-parabolic parameter in the mandelbar

A parameter `c` carrying a `Work.EL.RootParabolic` structure (declared in
`Submission/Work/ELTop/Defs.lean`, produced by `Submission/Work/FSeed/Classify.lean`) — a simple parabolic cycle of exact
period `5` at `z₁` whose basin attracts the critical orbit under the second return map
`F c = T_c^[10]` — lies in the mandelbar, i.e. the critical orbit `n ↦ T_c^[n] 0` of the
antiholomorphic quadratic map `T_c(z) = z̄² + c` is bounded.

The proof is a direct boundedness argument.  From the hypothesis that
`(F c)^[q] c → z₁` we obtain a bound `B` for the norms of all `(F c)^[q] c`.  An arbitrary
iterate `T_c^[m] c` decomposes as `m = 10 q + r` with `r < 10` and equals
`T_c^[r] ((F c)^[q] c)`; applying the elementary growth estimate
`‖T_c w‖ ≤ ‖w‖² + ‖c‖` `r` times turns the bound `B` into the explicit bound
`growthBound c B r = ((x ↦ x² + ‖c‖)^[r]) B`, and only the ten values `r < 10` occur.
-/
import Mathlib
import Submission.Work.FSeed.RootParabolic
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FSeed.API

open Filter Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- The iterated norm-growth bound of the tricorn: the `r`-fold iterate of `x ↦ x² + ‖c‖`
applied to `B`.  It dominates the norm of `T_c^[r] w` whenever `‖w‖ ≤ B`. -/
def growthBound (c : ℂ) (B : ℝ) (r : ℕ) : ℝ := ((fun x : ℝ => x ^ 2 + ‖c‖)^[r]) B

@[simp] theorem growthBound_zero (c : ℂ) (B : ℝ) : growthBound c B 0 = B := rfl

/-- The recursion satisfied by `growthBound`: one more iterate squares and adds `‖c‖`. -/
theorem growthBound_succ (c : ℂ) (B : ℝ) (r : ℕ) :
    growthBound c B (r + 1) = growthBound c B r ^ 2 + ‖c‖ := by
  simp only [growthBound, Function.iterate_succ_apply']

theorem growthBound_nonneg {c : ℂ} {B : ℝ} (hB : 0 ≤ B) (r : ℕ) :
    0 ≤ growthBound c B r := by
  induction r with
  | zero => simpa using hB
  | succ r ih =>
    rw [growthBound_succ]
    have h1 := sq_nonneg (growthBound c B r)
    have h2 := norm_nonneg c
    linarith

/-- **The iterated growth bound.**  If `‖w‖ ≤ B` then `‖T_c^[r] w‖ ≤ growthBound c B r`: each
application of `T_c` sends a point of norm at most `x` to a point of norm at most `x² + ‖c‖`. -/
theorem norm_orbit_le_growthBound {c : ℂ} {B : ℝ} (hB : 0 ≤ B) :
    ∀ (r : ℕ) (w : ℂ), ‖w‖ ≤ B → ‖Work.ParamRays.orbit c w r‖ ≤ growthBound c B r := by
  intro r
  induction r with
  | zero => intro w hw; simpa using hw
  | succ r ih =>
    intro w hw
    rw [Work.ParamRays.orbit_succ, growthBound_succ]
    have h1 := Work.ParamRays.norm_Tantibar_le c (Work.ParamRays.orbit c w r)
    have h2 := ih w hw
    have h3 := growthBound_nonneg (c := c) hB r
    have h4 := norm_nonneg (Work.ParamRays.orbit c w r)
    nlinarith [h1, h2, h3, h4]

theorem mem_Mandelbar {c : ℂ} (d : Work.EL.RootParabolic c) :
    c ∈ LeanEval.ComplexAnalysis.Mandelbar := by
  rw [Work.ParamRays.mem_mandelbar_iff_bounded]
  -- The critical orbit of the second return map `F c` converges, hence is bounded.
  have hconv : Tendsto (fun q : ℕ => (Work.FSeed.F c)^[q] c) atTop (nhds d.z₁) :=
    Work.FSeed.root_tendsto_critOrbit d
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hconv)
  have hBq : ∀ q : ℕ, ‖(Work.FSeed.F c)^[q] c‖ ≤ B := fun q => hB _ ⟨q, rfl⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg c) (by simpa using hBq 0)
  -- `F c` is the tenth iterate of `T_c`.
  have h10 : (Tantibar c)^[10] = Work.FSeed.F c :=
    funext (Work.FSeed.Tantibar_iterate_ten c)
  have hF : ∀ q : ℕ, (Work.FSeed.F c)^[q] c = (Tantibar c)^[10 * q] c := by
    intro q
    rw [← h10, Function.iterate_mul]
  have horbit : ∀ q : ℕ, Work.ParamRays.orbit c c (10 * q) = (Work.FSeed.F c)^[q] c := by
    intro q
    show (Tantibar c)^[10 * q] c = (Work.FSeed.F c)^[q] c
    rw [← hF q]
  -- Every iterate of the critical point `c` splits as `10 q + r`, `r < 10`.
  have key : ∀ m : ℕ, ‖Work.ParamRays.orbit c c m‖ ≤ growthBound c B (m % 10) := by
    intro m
    have hsplit : Work.ParamRays.orbit c c m =
        Work.ParamRays.orbit c ((Work.FSeed.F c)^[m / 10] c) (m % 10) := by
      conv_lhs => rw [show m = 10 * (m / 10) + m % 10 from (Nat.div_add_mod m 10).symm]
      rw [Work.ParamRays.orbit_add, horbit (m / 10)]
    rw [hsplit]
    exact norm_orbit_le_growthBound hB0 (m % 10) _ (hBq (m / 10))
  refine ⟨∑ r ∈ Finset.range 10, growthBound c B r, fun n => ?_⟩
  rcases n with _ | k
  · simp only [Work.ParamRays.orbit_zero, norm_zero]
    exact Finset.sum_nonneg fun r _ => growthBound_nonneg (c := c) hB0 r
  · rw [Work.ParamRays.orbit_one_add]
    have hz : Tantibar c 0 = c := by simp [Tantibar]
    rw [hz]
    exact le_trans (key k) (Finset.single_le_sum (fun r _ => growthBound_nonneg (c := c) hB0 r)
      (Finset.mem_range.mpr (Nat.mod_lt k (by norm_num))))

end

end Work.FSeed.API
