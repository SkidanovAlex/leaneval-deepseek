import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3RhsPriced
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.Mem10Obligations =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/Mem10Obligations` — the `ℋ¹⁰` obligation of the mollifier part of `ClassC`

Lead install, 2026-10-11 (`cbc/fts_phistar_REVIEW.md` §3, `cbc/fts_mem10_install.md`).

`ClassC` gained the field `mem10 : HkMem α 10 g` (the repaired elliptic node
`PhiStar.bslOp_sol_exists_pp 8` needs two orders of slack).  Every `ClassC` element that the
tree produces is a log-mollified profile `J_ε f` (possibly corrected by `Pz`), and `SoftClass`
(the mollifier part of `ClassC`, `MolClassC.lean`) gained the matching field `mem10`, supplied
in `softClass_Jeps` by

  `Work.FTS.StrongEps.HkMem_Jeps_ten_of_eight` — `J_ε : ℋ⁸ → ℋ¹⁰`, for **every** `ε > 0`.

**Status: DISCHARGED.**  The declaration now lives in
`Submission/Work/FTS/StrongEps/HkMem_Jeps_ten_of_eight.lean` (module
`Submission.Work.FTS.StrongEps.HkMem_Jeps_ten_of_eight`), which this file imports; the proof goes
through the scale-free two-order gain `TenOfEight.HkMem_Jeps_gain_pos`
(`Submission/Work/FTS/StrongEps/TenOfEight/GainAll.lean`), which removes the `ε ≤ 1` restriction of
`EpsE4Thr.HkMem_Jeps_gain` by replacing the routed density `LamFull ρ ε c M` with a scale-free one
(the kernel factor `max 1 (ε⁻¹^M)`).  The boundary-vanishing hypothesis of the `EpsE4Thr` form is
*unused* there (`J_ε f` reads `f` only on the open quadrant), so it does not appear in the
delivered statement.

The statement, byte-for-byte as installed:

```lean
theorem HkMem_Jeps_ten_of_eight {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α 8 f) :
    Work.Spaces.HkMem α 10 (Jeps ρ ε f)
```
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3DataFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo)
open Work.Spaces (HkMem HkSq HkNorm)

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-- **S6's package `L3Data`, uniformly in `Ce`.**  There are constants `α₂, C3 > 0`, `Cpow ≥ 0`
such that for *every* elliptic perturbation constant `Ce` the package `L3Data α₂ Ce C3 Cpow`
holds.  Consequently `Dbd.dbd_of_eq` applies with the caller's own `Ce`. -/
theorem L3Data_exists : ∃ α₂ C3 Cpow : ℝ, 0 < α₂ ∧ 0 < C3 ∧ 0 ≤ Cpow ∧
    ∀ Ce : ℝ, L3Data α₂ Ce C3 Cpow := by
  obtain ⟨α₂l, C3l, hα₂l, hC3l, hlin⟩ := L3_lin_mem
  obtain ⟨α₂r, C3r, Cpow, hα₂r, hC3r, hCpow, hrhs⟩ := L3RhsPriced
  refine ⟨min α₂l α₂r, max (max C3l C3r) 0, Cpow, lt_min hα₂l hα₂r, ?_, hCpow, ?_⟩
  · exact lt_of_lt_of_le hC3l (le_trans (le_max_left _ _) (le_max_left _ _))
  intro Ce
  refine ⟨⟨lt_of_lt_of_le hC3l (le_trans (le_max_left _ _) (le_max_left _ _)),
    lt_min hα₂l hα₂r, hCpow⟩, ?_, ?_⟩
  · intro α hα f hf
    have hαl : α ∈ Set.Ioc 0 α₂l := ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩
    obtain ⟨hm, hb⟩ := hlin α hαl f hf
    refine ⟨hm, le_trans hb ?_⟩
    have hx : (0 : ℝ) ≤ (1 + Xn α f) ^ 4 :=
      pow_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 4 f]) 4
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  · intro α hα E Φs Φ f Cs μ lam M hell hf hM hμ hlam
    have hαr : α ∈ Set.Ioc 0 α₂r := ⟨hα.1, le_trans hα.2 (min_le_right _ _)⟩
    obtain ⟨hm, hb⟩ := hrhs α hαr Ce Cs E Φs Φ f μ lam M hell hf hM hμ hlam
    refine ⟨hm, le_trans hb ?_⟩
    have hB : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.1.le _
    have hC : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
    have hY : (0 : ℝ) ≤ (1 + HkNorm α 6 f) ^ 2 := by positivity
    have h1 : C3r * (1 + |Ce| + |Cs|) ^ 4 ≤ max C3l C3r * (1 + |Ce| + |Cs|) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have h1' : max C3l C3r * (1 + |Ce| + |Cs|) ^ 4
        ≤ max (max C3l C3r) 0 * (1 + |Ce| + |Cs|) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have h2 : C3r * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow)
        ≤ max (max C3l C3r) 0 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h1') hB
    have h3 : C3r * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4
        ≤ max (max C3l C3r) 0 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 :=
      mul_le_mul_of_nonneg_right h2 hC
    exact mul_le_mul_of_nonneg_right h3 hY

end Work.FTS.StrongPersist
end
end
