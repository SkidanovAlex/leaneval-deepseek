/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StrongEpsP/FirstStepP.lean` — the bootstrap value of the
`P₀`-scheme

The restart-and-concatenate induction of the `P₀`-scheme (`StrongEpsP.EpsGlue_of_glueP`) needs, on
top of the local step `hstep` and the a-priori bound `EpsAprioriBddHP`, the *bootstrap value*
`Xn6 α g₀ ≤ M`: the datum is of `ℋ⁶`-size at most the constant `M` of the a-priori bound.  This is
exactly the argument of `Work.FTS.StrongEps.GlueParts.FirstStep` (the unprojected sibling): feed
`hstep` the legitimate threshold `M' = Xn6 α g₀` (so that the local solution's slices are bounded
by `2 Xn6 g₀ + 1`), restrict the step to the sub-horizon `T' = min δ T ≤ T` so that the a-priori
bound applies, and read off the value at fake time `0`, where the slice is the datum.

Nothing here uses the *scheme* — only that `IsEpsSolP`'s first conjunct says that the zero slice is
the datum, `Xn6` is nonnegative, and `EpsRegP`/`IsEpsSolP` are monotone in the horizon.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The bootstrap value of the `P₀`-scheme**: under the local step `hstep` and the sub-horizon
a-priori bound `EpsAprioriBddHP`, the datum itself satisfies `Xn6 α g₀ ≤ M`. -/
theorem FirstStepP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M)
    (hstep : ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Fn, EpsDatumP α ρ ε h₀ →
      Xn6 α h₀ ≤ M' →
      ∃ h : Fam, IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) δ, Xn6 α (slice h τ) ≤ 2 * M' + 1)
    (hd : EpsDatumP α ρ ε g₀) (hAp : EpsAprioriBddHP α ρ ε T Φs E g₀ M) :
    Xn6 α g₀ ≤ M := by
  -- The size of the datum is a legitimate threshold for the local step.
  have hM₀ : (0 : ℝ) ≤ Xn6 α g₀ := Work.Spaces.HkNorm_nonneg α 6 g₀
  obtain ⟨δ, hδ, hstep'⟩ := hstep (Xn6 α g₀) hM₀
  obtain ⟨h, hsol, hreg, _hb⟩ := hstep' g₀ hd le_rfl
  -- Restrict the step to the sub-horizon `T' = min δ T ≤ T`, so that the a-priori bound applies.
  set T' : ℝ := min δ T with hT'def
  have hT'pos : 0 < T' := lt_min hδ hT
  have hT'leT : T' ≤ T := min_le_right δ T
  have hT'leδ : T' ≤ δ := min_le_left δ T
  have hsol' : IsEpsSolP α ρ ε T' Φs E g₀ h := IsEpsSolP.mono hsol hT'leδ
  have hreg' : EpsRegP α ρ ε T' h := hreg.mono hT'leδ
  have hbdd := hAp T' hT'pos hT'leT h hsol' hreg'
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T' := ⟨le_rfl, hT'pos.le⟩
  have hfin := hbdd 0 h0
  -- At fake time `0` the slice is the datum.
  rw [IsEpsSolP.slice_zero hsol] at hfin
  exact hfin

end Work.FTS.StrongEps.StrongEpsP
