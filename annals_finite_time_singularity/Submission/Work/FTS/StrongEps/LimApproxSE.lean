/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/LimApproxSE.lean` — the approximation clause of the strong output

The FinalV2 design (`sources/ftsV2/fts_final_redesign.md` §G2) enriches the output of
`global_strong2` by the clause `LimApprox` (`Submission/Work/FTS/FinalV2/Defs.lean`): on every
horizon the solution is the limit of **class-`C`** families with uniform `ℋ⁴`-smallness, a uniform
`ℋ⁶`-bound, a uniform `ℋ⁴`-Lipschitz modulus in `τ`, `C⁴`-jet convergence on `Qd` and convergence
of the modulation.

That definition lives in `FinalV2.Defs`, whose import cone contains `StrongEps.EpsODE`; putting it
into `EpsLimPkg` directly would create an import cycle
(`StrongEps.EpsLimit → FinalV2.Defs → Final.Defs → StrongEps.EpsODE → StrongEps.EpsLimit`).
This module therefore carries a **verbatim duplicate** under the names
`Work.FTS.StrongEps.LimApproxOn` (the horizon-`[0,T]` form, which is what `EpsLimPkg` can glue
piecewise) and `Work.FTS.StrongEps.LimApproxSE` (the `∀ T > 0` form, definitionally the same shape
as `FinalV2.LimApprox`).  The identification with the frozen definition is proved downstream, in
`GlobalStrong2Prime.lean`, in the file that is allowed to import both.

Nothing here is analytic: the module only fixes vocabulary.
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-- **The approximation clause of the strong output at the horizon `[0,T]`** (the G2 clause of the
FinalV2 design): there are class-`C` families `gn`, a uniform `ℋ⁶`-bound `B` and a uniform
`ℋ⁴`-Lipschitz modulus `L` such that the `ℋ⁴`-size of `gn` is uniformly `≤ C₀α²`, its `τ`-modulus
is `≤ L|τ-τ'|`, every mixed slot of order `≤ 4` converges pointwise on `Qd` to that of `g`, and the
modulation converges.

This is the horizon-restricted form: it is what an `EpsLimPkg` can carry (`EpsLimPkg` is stated on
`[0,T]` and glued across the covering pieces of `Assembly.lean`). -/
def LimApproxOn (α C₀ T : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  ∃ (gn : ℕ → Fam) (B L : ℝ),
    (∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (gn n) τ) ∧
        Work.FTS.Nonlin.Xn α (slice (gn n) τ) ≤ C₀ * α ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 α (slice (gn n) τ) ≤ B) ∧
    (∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.mixed j i (slice g τ) z θ))) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n : ℕ => muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ)
        Filter.atTop (𝓝 (muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ)))

/-- **The approximation clause of the strong output** (the `FinalV2.LimApprox` shape, with the
`∀ T > 0` quantifier outermost). -/
def LimApproxSE (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  ∀ T : ℝ, 0 < T → LimApproxOn α C₀ T Φs E g

/-- The horizon-restricted form is monotone in the horizon. -/
theorem LimApproxOn.mono {α C₀ T T' : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (h : LimApproxOn α C₀ T Φs E g) (hT : T' ≤ T) (hT0 : 0 ≤ T') :
    LimApproxOn α C₀ T' Φs E g := by
  obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := h
  refine ⟨gn, B, L, ?_, ?_, ?_, ?_⟩
  · intro n τ hτ
    exact hb n τ ⟨hτ.1, le_trans hτ.2 hT⟩
  · intro n τ hτ τ' hτ'
    exact hlip n τ ⟨hτ.1, le_trans hτ.2 hT⟩ τ' ⟨hτ'.1, le_trans hτ'.2 hT⟩
  · intro τ hτ j i hji z θ hzθ
    exact hjet τ ⟨hτ.1, le_trans hτ.2 hT⟩ j i hji z θ hzθ
  · intro τ hτ
    exact hmu τ ⟨hτ.1, le_trans hτ.2 hT⟩

/-- The full form restricts to a horizon. -/
theorem LimApproxSE.on {α C₀ : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (h : LimApproxSE α C₀ Φs E g) {T : ℝ} (hT : 0 < T) : LimApproxOn α C₀ T Φs E g :=
  h T hT

end Work.FTS.StrongEps
