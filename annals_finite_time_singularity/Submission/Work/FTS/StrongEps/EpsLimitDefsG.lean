/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLimitDefsG.lean` — E5 vocabulary of the C1–C5 ruling

curric-46 lead install (2026-10-11) of `cbc/fts_strongeps_c1c5_ruling.{md,lean}` §1 and §5
(reviewed GO-WITH-FIXES, `cbc/fts_strongeps_c1c5_ruling_REVIEW.md`).

* `EllLimOK3` — StrongEps copy of the frozen `Work.FTS.FinalV2.EllLimOK3` (the import
  `EpsLimit → FinalV2.Defs` would be cyclic); `GlobalStrong2Prime.ellLimOK3_iff` is `Iff.rfl`.
  Its middle conjunct is Gap 1 (`E5Aux3/contDiffOn_two_E_of_EllLimOK3`), so the pinning (C1)
  is not needed.
* `ExistsLimG` — E5's new conclusion: ONE global family with a limit package on every horizon
  (replaces `ExistsLimH`, whose uniqueness clause needs the false (C5) `ℋ⁴`-Lipschitz datum).

These live in their own module (not `EpsLimitDefs.lean`) so that the install does not force a
rebuild of every StrongEps module importing `EpsLimitDefs`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsLimitDefs

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

/-- Verbatim copy of `Work.FTS.FinalV2.EllLimOK3`. -/
def EllLimOK3 (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ContDiffOn ℝ 3 (Function.uncurry (E f)) Work.Construction.Qd ∧
    ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

theorem EllLimOK3.toEllLimOK {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E) : EllLimOK α E := by
  intro fn f B hC hB h4 hj
  obtain ⟨hlaw, -, hconv⟩ := h fn f B hC hB h4 hj
  exact ⟨hlaw, fun j i hji z θ hzθ => hconv j i (by omega) z θ hzθ⟩

/-- **E5's new conclusion**: ONE family `g`, a limit package on every horizon. -/
def ExistsLimG (α C₀ K : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) : Prop :=
  ∃ g : Fam, ∀ T : ℝ, 0 < T → ∃ Cd : ℝ, 0 < Cd ∧ EpsLimPkg α C₀ K Cd T Φs E g₀ g

end Work.FTS.StrongEps
