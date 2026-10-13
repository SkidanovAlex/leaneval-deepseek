/-
# `Work.FTS.StrongPersist.H6Aux.IPChains` — the level chains for `IPnG`

The concrete pairing of the strong route is `IP6 1 1 1 1 1 1 1 1 1 1 α = IPnG 1 1 α 5`
(`rfl`), the five-fold recursion `HkIPStep 1 1` on top of `H1IP α`.  The level-six
pairing bound `H6Lin` is proved here by running the paper's *commutator* induction at the
level of the family `IPnG 1 1 α n`, `n ≤ 5`, so this module collects the three level-wise
inputs of that induction:

* `commSm_IPnG` — additivity of `IPnG 1 1 α n` on `Q0Sm (n+1)`-smooth, `ℋ^{n+1}`-honest
  arguments (`CommSm`, the open-quadrant package of `CoercivityFix.Transfer`);
* `CSQ_IPnG` — the Cauchy–Schwarz bound `|IPnG 1 1 α n X Y| ≤ CC·|X|_{ℋ^{n+1}}·|Y|_{ℋ^{n+1}}`
  for such arguments (`CSQ`), with an existential constant;
* `lo_IPnG` — the slot cover `HkSq α (n+1) f ≤ IPnG 1 1 α n f f` on the honest class
  (`H1IP_le_self_SO` at `n = 0` and the recursion `lo_step_SO` with unit coefficients).

Everything rests on proved material of `Work.FTS.CoercivityFix.Transfer` and
`Work.FTS.StrongPersist.IP6_lo_coeffs`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityFix.Transfer.CommSm_L1
import Submission.Work.FTS.CoercivityFix.Transfer.CommSm_succ
import Submission.Work.FTS.CoercivityFix.Transfer.CSQ_one
import Submission.Work.FTS.CoercivityFix.Transfer.CSQ_succ
import Submission.Work.FTS.IPGen.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)
open Work.FTS.IPGen (IPnG IPnG_zero IPnG_succ)
open Work.FTS.CoercivityFix.Transfer (CommSm CSQ CommSm_L1 CommSm_succ CSQ_one CSQ_succ)

set_option autoImplicit false

/-- **Additivity of the `n`-fold pairing.**  `CommSm α (n+1) (IPnG 1 1 α n)`, i.e. `IPnG 1 1 α n`
is additive on `C^{n+1}`-on-the-open-quadrant arguments in `ℋ^{n+1}`, for every `n`. -/
theorem commSm_IPnG (α : ℝ) (hα : 0 < α) (n : ℕ) :
    CommSm α (n + 1) (IPnG 1 1 α n) := by
  induction n with
  | zero => exact CommSm_L1 α hα
  | succ n ih =>
      have h := CommSm_succ α hα (n + 1) (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ)) ih
      have he : Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) := by
        rw [← IPnG_succ]
      rwa [he] at h

/-- **Cauchy–Schwarz for the `n`-fold pairing.**  There is a constant `CC` with
`|IPnG 1 1 α n X Y| ≤ CC·|X|_{ℋ^{n+1}}·|Y|_{ℋ^{n+1}}` for `C^{n+1}`-on-the-open-quadrant
arguments `X, Y ∈ ℋ^{n+1}`. -/
theorem CSQ_IPnG (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∃ CC : ℝ, 0 < CC ∧ CSQ α (n + 1) (IPnG 1 1 α n) CC := by
  induction n with
  | zero => exact CSQ_one α hα
  | succ n ih =>
      obtain ⟨CC, hCC, hCSQ⟩ := ih
      refine ⟨3 * max 1 (max 1 1) * CC, by positivity, ?_⟩
      have h := CSQ_succ α hα (n + 1) (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ))
        hCC.le zero_le_one zero_le_one hCSQ
      have he : Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) := by
        rw [← IPnG_succ]
      rwa [he] at h

/-- **The slot cover of the `n`-fold pairing.**  `HkSq α (n+1) f ≤ IPnG 1 1 α n f f` for every
`f` smooth on the open quadrant with honest `ℋ^{n+1}`-integral. -/
theorem lo_IPnG (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f ≤ IPnG 1 1 α n f f := by
  induction n with
  | zero =>
      intro f hs hm
      simpa only [IPnG_zero] using Work.FTS.StrongPersist.H1IP_le_self_SO (α := α) hs hm
  | succ n ih =>
      have h := Work.FTS.StrongPersist.lo_step_SO (α := α) hα (k := n + 1) (IP := IPnG 1 1 α n)
        (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ)) (by omega) le_rfl le_rfl ih
      intro f hs hm
      have he : Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) := by
        rw [← IPnG_succ]
      rw [← he]
      exact h f hs hm

/-! ## The uniform-in-`α` versions -/

/-- **Cauchy–Schwarz for the `n`-fold pairing, uniformly in `α ∈ (0,1]`.** -/
theorem CSQ_IPnG_unif (n : ℕ) :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α ∈ Set.Ioc 0 1, CSQ α (n + 1) (IPnG 1 1 α n) CC := by
  induction n with
  | zero =>
      refine ⟨(10 : ℝ) ^ 22, by norm_num, fun α hα => ?_⟩
      exact fun X Y _ _ hX hY =>
        Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα.1 X Y hX hY
  | succ n ih =>
      obtain ⟨CC, hCC, h⟩ := ih
      refine ⟨3 * max 1 (max 1 1) * CC, by positivity, fun α hα => ?_⟩
      have hstep := Work.FTS.CoercivityFix.Transfer.CSQ_succ α hα.1 (n + 1)
        (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ)) hCC.le zero_le_one zero_le_one (h α hα)
      rwa [show Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) from by
        rw [← IPnG_succ]] at hstep

end Work.FTS.StrongPersist.H6Aux
