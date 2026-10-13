import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.GlueParts.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.GlueParts

theorem FirstStep {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn} {M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M)
    (hstep : ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Work.FTS.Galerkin.Fn, Work.FTS.StrongEps.EpsDatum α ρ ε h₀ →
      Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M' →
      ∃ h : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSol α ρ ε δ Φs E h₀ h ∧
        Work.FTS.StrongEps.EpsReg α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) δ, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice h τ) ≤ 2 * M' + 1)
    (hd : Work.FTS.StrongEps.EpsDatum α ρ ε g₀) (hAp : Work.FTS.StrongEps.EpsAprioriBddH α ρ ε T Φs E g₀ M) :
    Work.FTS.StrongGlobal.Xn6 α g₀ ≤ M := by
  -- The size of the datum is a legitimate threshold for the local step.
  have hM₀ : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g₀ :=
    Work.Spaces.HkNorm_nonneg α 6 g₀
  obtain ⟨δ, hδ, hstep'⟩ := hstep (Work.FTS.StrongGlobal.Xn6 α g₀) hM₀
  obtain ⟨h, hsol, hreg, _hb⟩ := hstep' g₀ hd le_rfl
  -- Restrict the step to the sub-horizon `T' = min δ T ≤ T`, so that the a-priori bound applies.
  set T' : ℝ := min δ T with hT'def
  have hT'pos : 0 < T' := lt_min hδ hT
  have hT'leT : T' ≤ T := min_le_right δ T
  have hT'leδ : T' ≤ δ := min_le_left δ T
  have hsol' : Work.FTS.StrongEps.IsEpsSol α ρ ε T' Φs E g₀ h := hsol.mono hT'leδ
  have hreg' : Work.FTS.StrongEps.EpsReg α ρ ε T' h := hreg.mono hT'leδ
  have hbdd := hAp T' hT'pos hT'leT h hsol' hreg'
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T' := ⟨le_rfl, hT'pos.le⟩
  have hfin := hbdd 0 h0
  -- At fake time `0` the slice is the datum.
  rw [Work.FTS.StrongEps.IsEpsSol.slice_zero hsol] at hfin
  exact hfin

end Work.FTS.StrongEps.GlueParts
