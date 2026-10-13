import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongPersist.N6.Prod6
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.P0` — the level-six bound of the single piece `NBlk 0`

`NBlk α w Φs Φg 0 = 2·(Rop α (PhiTg α w Φg)·w)`, i.e. a product `A·w` in which **both** factors
are `ℋ⁶`-priced (`HkNorm α 6 A ≤ Ce·HkNorm α 6 w` by `EllPkgK.R`, and `w` is honest to order 7 by
`ClassC`).  Unlike the pieces `4` and `8` (whose second factor `D_θw`/`D_zw` is a slot of order
one *above* the norm), no slot of order 7 occurs, so the crude level-six product rule
`N6.prod_field_of6` applies directly: with `α`-dependent constants (which the consumer `S2Stmt`
allows, since `Ct` is chosen after `α`) its `α^{-1/2}` loss is harmless and one gets
`HkSq α 6 (NBlk … 0) ≤ 4·(C·α^{-1/2}·Ce⁺·HkNorm α 6 w · HkNorm α 6 w)²`, i.e. the quadratic term.

This is a **fallback** for the `gg`-group: `Assembly.GGStmt_of_p0_p48` combines it with the
pieces `4, 8` (`N_b6_p48`) into `GGStmt`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem hkN_sq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    (Work.Spaces.HkNorm α k f) ^ 2 = Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkNorm]
  exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)

/-- The level-six bound of the piece `NBlk 0` (see `Stmts.P0Stmt`). -/
theorem N_b6_p0 : P0Stmt := by
  obtain ⟨Kmaj, hKmaj, hMaj⟩ := Work.FTS.StrongPersist.N6.prod_majorant6
  obtain ⟨Cexc, hCexc, hExc⟩ := Work.FTS.StrongPersist.N6.exc_bound6
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.StrongPersist.N6.prod_field_of6 ⟨Kmaj, hKmaj, hMaj⟩ ⟨Cexc, hCexc, hExc⟩
  intro C₀ Ce Cs α hα
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  refine ⟨4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1, by positivity, ?_⟩
  intro Φs w Φg hcls hXw hz hell hK hstar
  -- the honest `ℋ⁶`-data
  have hQoA : Work.FTS.VocabO.HQo α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) :=
    hK.R.1
  have hQow : Work.FTS.VocabO.HQo α 6 w :=
    ⟨hcls.reg, Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 6 (by norm_num) hcls.mem⟩
  have hCe0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hCell : Ce ≤ max Ce 0 := le_max_left Ce 0
  have hwnn : 0 ≤ Work.Spaces.HkNorm α 6 w := Work.Spaces.HkNorm_nonneg α 6 w
  have hA7nn : 0 ≤ 1 + Work.Spaces.HkSq α 7 w := by
    have := Work.Spaces.HkSq_nonneg α 7 w
    linarith
  -- the level-six product rule
  obtain ⟨-, hprod⟩ := hC α hα0 hα1
    (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) w hQoA hQow
  have hAnorm : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg))
      ≤ max Ce 0 * Work.Spaces.HkNorm α 6 w :=
    le_trans hK.R.2 (mul_le_mul_of_nonneg_right hCell hwnn)
  have hCα : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg hα0.le _)
  have hmain : Work.Spaces.HkNorm α 6 (fun z θ =>
        Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
      ≤ (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * (Work.Spaces.HkNorm α 6 w) ^ 2 := by
    refine le_trans hprod ?_
    calc C * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg))
          * Work.Spaces.HkNorm α 6 w
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0 * Work.Spaces.HkNorm α 6 w)
            * Work.Spaces.HkNorm α 6 w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAnorm hCα) hwnn
      _ = (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * (Work.Spaces.HkNorm α 6 w) ^ 2 := by ring
  -- transfer to `HkSq`
  have hbound : Work.Spaces.HkSq α 6 (fun z θ =>
        Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
      ≤ (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 * (Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h2 := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hmain 2
    calc Work.Spaces.HkSq α 6 (fun z θ =>
          Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
        = (Work.Spaces.HkNorm α 6 (fun z θ =>
            Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)) ^ 2 :=
          (hkN_sq α 6 _).symm
      _ ≤ ((C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * (Work.Spaces.HkNorm α 6 w) ^ 2) ^ 2 := h2
      _ = ((C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * Work.Spaces.HkSq α 6 w) ^ 2 := by
          rw [hkN_sq α 6 w]
      _ = (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 * (Work.Spaces.HkSq α 6 w) ^ 2 := by
          ring
  -- the target
  have hNB : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0
      = fun z θ => 2 * (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ
          * w z θ) := rfl
  rw [hNB, Work.FTS.StrongEps.HkSq_const_mul]
  have h6w : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hsquare : (Work.Spaces.HkSq α 6 w) ^ 2 ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
    pow_le_pow_left₀ h6w (by linarith) 2
  have hcoef : 0 ≤ 4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 := by positivity
  have hfin : (2 : ℝ) ^ 2 * Work.Spaces.HkSq α 6 (fun z θ =>
        Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
      ≤ (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1)
          * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsquare hcoef
    have h2 := mul_le_mul_of_nonneg_left hbound hcoef
    have hnn : 0 ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
    nlinarith [h2, h, hnn]
  have hfin2 : (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1)
        * (1 + Work.Spaces.HkSq α 6 w) ^ 2
      ≤ (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w)
        + (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1)
          * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h : 0 ≤ (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w) :=
      mul_nonneg (by positivity) hA7nn
    linarith
  exact le_trans hfin hfin2

end Work.FTS.StrongEps.E4R3.Nblock6
