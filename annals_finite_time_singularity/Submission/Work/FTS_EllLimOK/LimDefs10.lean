/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.LimDefs10` — the order-`3` extraction vocabulary

The order-`3` analogue of `Work.FTS_EllLimOK.LimDefs` (which fixes the six pairs `(j,i)` with
`j + i ≤ 2`): here `P10` lists the ten pairs with `j + i ≤ 3`, `fam10 G n p` is the
`Fin 10`-valued vector of the ten mixed jets `D_z^j D_θ^i (G n)` at the point `p`, and `idx10`
is the index of a pair in the list.  These are the objects to which the Arzelà–Ascoli extraction
`Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin` is applied in the
order-`3` compactness obligation `ClosedCompact3`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FinCases
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

/-- The ten pairs `(j,i)` with `j + i ≤ 3`, in a fixed order. -/
def P10 : Fin 10 → ℕ × ℕ :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

/-- The `Fin 10`-valued vector of the ten mixed jets of order `≤ 3` of `G n` at the point `p`. -/
def fam10 (G : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : Fin 10 → ℝ :=
  fun m => Work.Spaces.mixed (P10 m).1 (P10 m).2 (G n) p.1 p.2

/-- Every pair occurring in the list `P10` has total order at most `3`. -/
theorem P10_sum_le_three (m : Fin 10) : (P10 m).1 + (P10 m).2 ≤ 3 := by
  fin_cases m <;> decide

/-- Every pair `(c,d)` with `c + d ≤ 3` occurs in the list `P10`. -/
theorem P10_surj (c d : ℕ) (h : c + d ≤ 3) : ∃ m : Fin 10, P10 m = (c, d) := by
  have hc : c ≤ 3 := by omega
  have hd : d ≤ 3 := by omega
  interval_cases c <;> interval_cases d <;> first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩
    | exact ⟨5, by decide⟩
    | exact ⟨6, by decide⟩
    | exact ⟨7, by decide⟩
    | exact ⟨8, by decide⟩
    | exact ⟨9, by decide⟩
    | (exfalso; omega)

/-- The index of a pair `(c,d)` with `c + d ≤ 3` in the list `P10`. -/
noncomputable def idx10 (c d : ℕ) : Fin 10 :=
  if h : c + d ≤ 3 then Classical.choose (P10_surj c d h) else 0

/-- The characteristic property of `idx10`. -/
theorem idx10_spec {c d : ℕ} (h : c + d ≤ 3) : P10 (idx10 c d) = (c, d) := by
  rw [idx10, dif_pos h]
  exact Classical.choose_spec (P10_surj c d h)

end Work.FTS_EllLimOK
