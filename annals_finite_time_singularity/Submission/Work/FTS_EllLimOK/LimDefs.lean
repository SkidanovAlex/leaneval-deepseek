/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.LimDefs` — the vocabulary of the compactness (`ClosedCompact`) argument

This module fixes the small vocabulary shared by the modules of the `ClosedCompact` workstream
(the proof of `Closed.LocalBound → Closed.ClosedCompact`):

* `wt` is the growth weight of `Closed.LocalBound`:
  `wt z θ = (1 + 1/z + 1/(θ(π/2-θ))) / (1+z)`;
* `P6` is the list of the six pairs `(j,i)` with `j + i ≤ 2`, and `fam6 G n p` is the
  `Fin 6`-valued vector of the six mixed jets `D_z^j D_θ^i (G n)` at the point `p` — the family
  to which the Arzelà–Ascoli extraction of
  `Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin` is applied;
* `idx6` is the index of a pair in `P6` and `idx6_spec` its characteristic property.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- The growth weight of `Closed.LocalBound`:
`(1 + 1/z + 1/(θ(π/2-θ))) / (1+z)`.  It is continuous (hence locally bounded) on the open
quadrant, and decays like `1/z` in the far field. -/
def wt (z θ : ℝ) : ℝ := (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z)

/-- The six pairs `(j,i)` with `j + i ≤ 2`, in a fixed order. -/
def P6 : Fin 6 → ℕ × ℕ := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)]

/-- The `Fin 6`-valued vector of the six mixed jets of order `≤ 2` of `G n` at the point `p`. -/
def fam6 (G : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  fun m => Work.Spaces.mixed (P6 m).1 (P6 m).2 (G n) p.1 p.2

/-- Every pair `(c,d)` with `c + d ≤ 2` occurs in the list `P6`. -/
theorem P6_surj (c d : ℕ) (h : c + d ≤ 2) : ∃ m : Fin 6, P6 m = (c, d) := by
  have hc : c ≤ 2 := by omega
  have hd : d ≤ 2 := by omega
  interval_cases c <;> interval_cases d <;> first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩
    | exact ⟨5, by decide⟩
    | (exfalso; omega)

/-- The index of a pair `(c,d)` with `c + d ≤ 2` in the list `P6`. -/
noncomputable def idx6 (c d : ℕ) : Fin 6 :=
  if h : c + d ≤ 2 then Classical.choose (P6_surj c d h) else 0

/-- The characteristic property of `idx6`. -/
theorem idx6_spec {c d : ℕ} (h : c + d ≤ 2) : P6 (idx6 c d) = (c, d) := by
  rw [idx6, dif_pos h]
  exact Classical.choose_spec (P6_surj c d h)

end Work.FTS_EllLimOK
