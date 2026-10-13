/-
  Area E7 / E2B, node `cellRefine_of_nodesB`, **part 2 of the split**: the presentation-dependent
  constants (`E2Const2`): the format and degree bounds of the cells produced in the `G`-case.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Data1

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-- The presentation-dependent constants: the format bound `Fbig` at which the `G`-case cells are
produced, the format/degree bounds `(Ag, Cbg)` of those cells and the resulting
`(AB, CB)` of the refinement. -/
noncomputable def e2bConst2 {n K F : ℕ} (c : E2Const n K F) (Fq : ℕ) (Qq : Polynomial ℕ) :
    E2Const2 c Fq Qq := by
  classical
  let Fbig : ℕ := 2 * c.Ac + c.M2 + 4 * Fq + 4
  let Ag : ℕ := (Work.WilE7.SheetData.gcase_cfs Fbig).choose
  let Cbg : Polynomial ℕ := (Work.WilE7.SheetData.gcase_cfs Fbig).choose_spec.choose
  -- the polynomial whose value at `D` is the degree budget `gcaseDeg c Fq Qq D`
  let Q0 : Polynomial ℕ :=
    Polynomial.C (2 * Fq + 2) + Polynomial.C (2 * (1 + 2 * Fq)) * (c.Dq + Qq)
  let CB : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 Cbg Q0).choose
  have hQ0 : ∀ D : ℕ, Q0.eval D
      = (2 * Fq + 2) + 2 * (1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D) := by
    intro D
    simp only [Q0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add]
  have hCB : ∀ D : ℕ, Cbg.eval (gcaseDeg c Fq Qq D) ≤ CB.eval D := by
    intro D
    have h := (Work.WilE7.Endgame.poly_comp_dominate 1 Cbg Q0).choose_spec D
    have h2 : gcaseDeg c Fq Qq D ≤ 1 * (D + Q0.eval D) := by
      simp only [gcaseDeg]
      rw [hQ0 D]
      omega
    exact le_trans (Work.WilE7.coreLT_succ.eval_mono_nat Cbg h2) h
  let AB : ℕ := max Ag c.Fp0
  exact ⟨AB, CB, Fbig, Ag, Cbg, rfl, rfl, hCB, rfl, rfl⟩

end

end Work.WilE7.Endgame.E2B
