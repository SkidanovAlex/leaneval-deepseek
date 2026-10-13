/-
# `GalFields/Norm/RadA4/continuousOn_Efun_four` — continuity of the order-`4` integrand

`E1Parts/RadABnd.continuousOn_Efun` proves that the explicit expression `Efun α f j` of the
order-`j` radial integrand is continuous on `(0,∞)` for `j ≤ 3`.  The consumer
`RadA4.Own` needs the same statement for `j ≤ 4` (the order-`4` slot of `radA α f`).

Nothing new is needed beyond smoothness: `Efun` is a finite sum of products of the blocks
`D_z^b (ampA α)`, `D_z^j (ampB α)`, `L₁₂ f`, `Qang f (j - b - 1)` and the weight `w`.  At
order `4` we need `b = 4` in the first block, so we use the `C^5`-smoothness
`E2pkg.contDiffOn_ampA_five` / `E2pkg.contDiffOn_ampB_five` instead of the `C^3` versions
`contDiffOn_ampA` / `contDiffOn_ampB`, and `Zop`-iterates of order up to `4` cost one fewer
derivative than before.  The remaining inputs (`L12f_contDiffOn`, `QangDiff`) are stated for
all orders up to `4` already.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.H2.QangDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `Big` is continuous on `(0,∞)` for `j ≤ 4`.  This is `E1Parts.continuousOn_Big` one order
up: the multiplier smoothness is `C^5` (`E2pkg.contDiffOn_ampA_five`) instead of `C^3`, so
that the `b = 4` `Zop`-iterate is covered. -/
theorem continuousOn_Big_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 4) :
    ContinuousOn (Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j) (Set.Ioi (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  have hLcont : ContinuousOn (fun z : ℝ => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn α hα hα1 f hsm hmem).continuousOn
  have hAsm : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α
  have hBsm : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α
  have hAcont : ∀ b : ℕ, b ≤ 4 → ContinuousOn (fun z : ℝ =>
      Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
      (Set.Ioi (0 : ℝ)) := by
    intro b hb
    have hZ : ContinuousOn (Work.Spaces.Zop^[b]
        (Work.FTS.CoercivityFix.Transfer.ampA α)) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn (n := 5 - b)
        (hu := hAsm.of_le (by exact_mod_cast (by omega : b + (5 - b) ≤ 5)))
    simpa only [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter] using hZ
  have hBcont : ContinuousOn (fun z : ℝ =>
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z)
      (Set.Ioi (0 : ℝ)) := by
    have hZ : ContinuousOn (Work.Spaces.Zop^[j]
        (Work.FTS.CoercivityFix.Transfer.ampB α)) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn (n := 0)
        (hu := hBsm.of_le (by exact_mod_cast (by omega : j + 0 ≤ 5)))
    simpa only [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter] using hZ
  have hcondcont : ∀ b : ℕ, ContinuousOn (fun z : ℝ =>
      if j - b = 0 then Work.Coercivity.L12f f z
      else - Work.Elliptic.Qang f (j - b - 1) z) (Set.Ioi (0 : ℝ)) := by
    intro b
    by_cases h : j - b = 0
    · rw [show (fun z : ℝ => if j - b = 0 then Work.Coercivity.L12f f z
          else - Work.Elliptic.Qang f (j - b - 1) z) = fun z : ℝ => Work.Coercivity.L12f f z
          from by funext z; rw [if_pos h]]
      exact hLcont
    · rw [show (fun z : ℝ => if j - b = 0 then Work.Coercivity.L12f f z
          else - Work.Elliptic.Qang f (j - b - 1) z)
          = fun z : ℝ => - Work.Elliptic.Qang f (j - b - 1) z
          from by funext z; rw [if_neg h]]
      exact ((Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).2 (j - b - 1) (by omega)).neg
  have hfun : Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j = fun z : ℝ =>
      -(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
    funext z; rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Big_eq]
  rw [hfun]
  refine ContinuousOn.add ?_ (continuousOn_const.mul hBcont)
  refine ContinuousOn.neg ?_
  refine continuousOn_finsetSum _ fun b hb => ?_
  have hb4 : b ≤ 4 := by
    have := Finset.mem_range.mp hb
    omega
  exact (continuousOn_const.mul (hAcont b hb4)).mul (hcondcont b)

/-- **Continuity of the order-`4` radial integrand.**  `Efun α f j` is continuous on `(0,∞)`
for `j ≤ 4`; this is `E1Parts.continuousOn_Efun` (the `j ≤ 3` version) one order up. -/
theorem continuousOn_Efun_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 4) :
    ContinuousOn (Work.FTS.CoercivityFix.Transfer.E1Parts.Efun α f j) (Set.Ioi (0 : ℝ)) := by
  have hbig := continuousOn_Big_four α hα hα1 f hf hj
  have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
    have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hfun : Work.FTS.CoercivityFix.Transfer.E1Parts.Efun α f j = fun z : ℝ =>
      Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z
        * Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z
        * (Work.Spaces.w z * Work.Spaces.w z) := by
    funext z; rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Efun_eq_Big]
  rw [hfun]
  exact (hbig.mul hbig).mul (hwcont.mul hwcont)

end Work.FTS.GalFields.Norm.RadA4
