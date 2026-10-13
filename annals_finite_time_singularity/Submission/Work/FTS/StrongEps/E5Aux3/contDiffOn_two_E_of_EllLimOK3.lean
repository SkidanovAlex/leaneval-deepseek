/-
# `E5Aux3/contDiffOn_two_E_of_EllLimOK3.lean` — Gap 1 without the pinning (PROVED)

curric-46 lead install (2026-10-11), ruling `cbc/fts_strongeps_c1c5_ruling.md` §1: the `hsmE`
input of `E5Law` / `E5_law_of_data` (`ContDiffOn ℝ 2 (uncurry (E f)) Q0`) is the middle conjunct
of `EllLimOK3`, under exactly the hypotheses with which E5 already applies `EllLimOK`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsLimitDefsG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem contDiffOn_two_E_of_EllLimOK3 {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E)
    {fn : ℕ → Fn} {f : Fn} {B : ℝ}
    (hC : ∀ n, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd)
    (hj : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) :
    ContDiffOn ℝ 2 (Function.uncurry (E f)) Work.FTS.EllipticEst.Q0 := by
  have h3 := (h fn f B hC hB h4 hj).2.1
  have hQ : Work.FTS.EllipticEst.Q0 = Work.Construction.Qd := rfl
  rw [hQ]
  exact h3.of_le (by norm_num)

end Work.FTS.StrongEps
