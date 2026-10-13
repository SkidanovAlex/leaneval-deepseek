/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Law.lean` — the elliptic-law clause of `E5`

The clause `EpsLimPkg.law` of the limit package says that the *limit* family satisfies the
positivised elliptic law

  `IsBslSolPos α (Ftau α g τ) (slice (PsiCan Φs E g) τ)`.

`Ftau α g τ = F_* + slice g τ` and `PsiCan Φs E g τ = Φs + E (slice g τ)`, so the clause is the
**sum** of two laws:

* the *star* law `IsBslSolPos α (Fstar α) Φs`, which is the field `sol` of `StarPkgo2` (the
  delivered `Work.Elliptic.IsBslSol`, transported by `IsBslSol.toPos`);
* the *perturbation* law `IsBslSolPos α (slice g τ) (E (slice g τ))`, which is the conclusion of
  the frozen hypothesis `EllLimOK α E` applied to the class-`C` approximants
  `fn n = slice (JfamP ρ (ε n) (G n)) τ` whose limit is `slice g τ`.

`bslOp` is a linear second-order operator (`Work.Elliptic.bslOp_add`), so the sum of two laws is
the law of the sum (`Work.FTS_EllLimOK.IsBslSolPos_add`, whose only extra hypothesis is joint `C²`
regularity of the two stream functions on the open quadrant).  The smoothness of `E f` is *not*
part of `EllLimOK`'s conclusion; it is a consequence of the slot convergence of order `≤ 2` of
`E (fn n) → E f` together with the `SmoothOpen` clause of `EllPkgGo` at the approximants, and is
therefore taken here as the explicit hypothesis `hsmE` (see `E5Law_aux` below for the reduction to
the slot-convergence form).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The star law at `Qd` -/

/-- `SmoothOpen Φs` gives joint `C²` on the open quadrant `Qd` (the two sets are the same). -/
theorem contDiffOn_two_of_smoothOpen_Qd {F : Fn} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd :=
  h.forall 2

/-! ## The clause -/

/-- **The `law` clause of `E5` at a limit slice.**

Given the two laws `IsBslSolPos α (Fstar α) Φs` (`hstar.sol.toPos`) and the perturbation law
`IsBslSolPos α f (E f)` produced by `EllLimOK α E` from the class-`C` approximants `fn n → f`
(with uniform `ℋ⁶`-bound `B` and `C⁴` limit), together with the joint `C²`-smoothness of `Φs` and
of `E f` on the open quadrant, the *sum* is the law of the limit family:
`IsBslSolPos α (Ftau α g τ) (slice (PsiCan Φs E g) τ)`. -/
theorem E5Law {α Cs B τ : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {fn : ℕ → Fn} {f : Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hELL : EllLimOK α E)
    (hclass : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B)
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hslot : ∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (fn n) z θ) Filter.atTop
        (𝓝 (Work.Spaces.mixed j i f z θ)))
    (hsmE : ContDiffOn ℝ 2 (Function.uncurry (E f)) Work.FTS.EllipticEst.Q0)
    (hfs : slice g τ = f) :
    Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α g τ)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) := by
  obtain ⟨hsolE, _⟩ := hELL fn f B hclass hB hc4 hslot
  have hs : Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Fstar α) Φs :=
    Work.FTS.StrongGlobal.IsBslSol.toPos hstar.sol
  have hsmΦ : ContDiffOn ℝ 2 (Function.uncurry Φs) Work.Construction.Qd :=
    contDiffOn_two_of_smoothOpen_Qd hstar.smooth
  have hsmE' : ContDiffOn ℝ 2 (Function.uncurry (E f)) Work.Construction.Qd := hsmE
  have hadd := Work.FTS_EllLimOK.IsBslSolPos_add hs hsolE hsmΦ hsmE'
  have hF : (fun z θ => Work.Construction.Fstar α z θ + f z θ)
      = Work.Construction.Ftau α g τ := by
    funext z θ
    rw [Work.Construction.Ftau, ← congrFun (congrFun hfs z) θ]
    rfl
  have hΨ : (fun z θ => Φs z θ + E f z θ)
      = Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ := by
    funext z θ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply, hfs]
  exact hadd.congr hF hΨ

end Work.FTS.StrongEps
