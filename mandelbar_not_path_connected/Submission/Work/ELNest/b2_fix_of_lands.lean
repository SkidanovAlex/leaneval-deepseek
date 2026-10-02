/-
# EL nest: `b₂` is fixed by `f_c²` (the field `NestData.b2_fix` is derivable)

`Tsq c b₂ = b₂` follows from the three tripod rays landing at `b₂`: the ray of angle `22/63` maps
to the ray of angle `25/63` under `T_c`, so `T_c b₂` is the landing point of the ray of angle
`25/63` as well, hence `T_c b₂ = b₂`; applying the same argument once more gives `Tsq c b₂ = b₂`.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Qp_shift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- `T (22/63) = 19/63` (the ray `22/63` of the tripod at `b₂` maps to the ray `19/63` of the
tripod at `b₁`). -/
theorem T_tripod_one : Work.EL.T (22 / 63) = 19 / 63 := by
  rw [Work.EL.T, show -2 * (22 / 63 : ℝ) = 19 / 63 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr
    (show (0 : ℝ) ≤ 19 / 63 ∧ (19 / 63 : ℝ) < 1 from ⟨by norm_num, by norm_num⟩)

/-- `T^[2] (22/63) = 25/63`: the tripod of `b₂` is a `T^2`-cycle (certificate `Tq_tripod_sq`). -/
theorem T_sq_tripod : Work.EL.T^[2] (22 / 63) = 25 / 63 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    T_tripod_one, Work.EL.T, show -2 * (19 / 63 : ℝ) = 25 / 63 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr
    (show (0 : ℝ) ≤ 25 / 63 ∧ (25 / 63 : ℝ) < 1 from ⟨by norm_num, by norm_num⟩)

/-- **`b₂` is fixed by `f_c² = Tsq c`** (the field `NestData.b2_fix`, derived from the three
tripod rays landing at `b₂` together with the `T²`-cycle `22/63 ↦ 25/63`; it is therefore not an
independent assumption of the interface). -/
theorem b2_fix_of_lands (S : NestData c) : Work.Landing.Tsq c S.b2 = S.b2 := by
  have h1 : LandsN S.d.hN (Work.EL.T^[2] (22 / 63))
      ((LeanEval.ComplexAnalysis.Tantibar c)^[2] S.b2) :=
    landsN_iterate S.d.hN S.d.bottcher 2 S.b2_lands.1
  rw [T_sq_tripod] at h1
  have h2 : (LeanEval.ComplexAnalysis.Tantibar c)^[2] S.b2 = S.b2 :=
    landsN_unique h1 S.b2_lands.2.1
  rw [show Work.Landing.Tsq c = (LeanEval.ComplexAnalysis.Tantibar c)^[2] from Tsq_eq_comp c]
  exact h2

end Work.ELNest
