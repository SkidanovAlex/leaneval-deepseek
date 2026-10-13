/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StrongEpsP/EpsGlue_of_glueP.lean` — the `P₀`-scheme's
restart-and-concatenate induction

The `P₀`-corrected twin of `Work.FTS.StrongEps.EpsGlue_of_glue` (`GlueParts/Induction.lean`): given
the local step `hstep` for the projected scheme `IsEpsSolP`, the a-priori bound `EpsAprioriBddHP`,
the two junction glues `hSol` (`IsEpsSolP` concatenation) and `hReg` (`EpsRegP` concatenation) as
hypotheses, and the bootstrap value `Xn6 α g₀ ≤ M`, it produces a regular `P₀`-solution on the
whole `[0,T]` with `Xn6 ≤ M` on every slice.

The argument is the restart-and-concatenate induction: `hor n = min T ((n+1)δ)` is the horizon
after `n` steps, each step restarts at the current slice and concatenates the new piece, and the
a-priori bound keeps every restart datum at size `≤ M` so that the *same* `δ` serves at every step.

Nothing about the scheme is used beyond

* `EpsRegP.mono` / `IsEpsSolP.mono` (horizon monotonicity),
* `epsRHSP_congr` (the projected right-hand side is slice-determined), and
* `shiftFam`/`concat`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem EpsGlue_of_glueP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn} {M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hd : Work.FTS.StrongEps.EpsDatumP α ρ ε g₀)
    (hstep : ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsDatumP α ρ ε h₀ →
      Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M' →
      ∃ h : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ h ∧
        Work.FTS.StrongEps.EpsRegP α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice h τ) ≤ 2 * M' + 1)
    (hAp : Work.FTS.StrongEps.EpsAprioriBddHP α ρ ε T Φs E g₀ M)
    (hSol : ∀ (t δ : ℝ) (G H : Work.FTS.Galerkin.Fam), 0 ≤ t → 0 < δ →
      Work.FTS.StrongEps.IsEpsSolP α ρ ε t Φs E g₀ G →
      Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E (Work.FTS.Galerkin.slice G t) H →
      Work.FTS.StrongEps.IsEpsSolP α ρ ε (t + δ) Φs E g₀
        (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t))
    (hReg : ∀ (t δ : ℝ) (G H : Work.FTS.Galerkin.Fam) (R : Work.FTS.Galerkin.Fn),
      0 ≤ t → 0 < δ → Work.FTS.StrongEps.EpsRegP α ρ ε t G →
      Work.FTS.StrongEps.EpsRegP α ρ ε δ H →
      (∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0) →
      (∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t) →
      (∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) →
      Work.FTS.StrongEps.EpsRegP α ρ ε (t + δ)
        (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t))
    (hFirst : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ M) :
    ∃ g : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g ∧
      Work.FTS.StrongEps.EpsRegP α ρ ε T g ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ M := by
  obtain ⟨δ, hδpos, hδstep⟩ := hstep M hM
  -- a number of steps that covers `[0,T]`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ (N : ℝ) * δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
    exact ⟨N, by rw [div_lt_iff₀ hδpos] at hN; linarith⟩
  -- the horizons of the iteration
  let hor : ℕ → ℝ := fun n => min T (((n : ℝ) + 1) * δ)
  have hhor_pos : ∀ n, 0 < hor n := by
    intro n
    show 0 < min T (((n : ℝ) + 1) * δ)
    exact lt_min hT (by positivity)
  have hhor_le : ∀ n, hor n ≤ T := by
    intro n
    show min T (((n : ℝ) + 1) * δ) ≤ T
    exact min_le_left _ _
  -- the first step (`n = 0`)
  have hzero : ∃ g : Fam, IsEpsSolP α ρ ε (hor 0) Φs E g₀ g ∧ EpsRegP α ρ ε (hor 0) g ∧
      ∀ τ ∈ Set.Icc 0 (hor 0), Xn6 α (slice g τ) ≤ M := by
    have h0 : hor 0 = min T δ := by
      show min T ((((0 : ℕ) : ℝ) + 1) * δ) = min T δ
      norm_num
    rw [h0]
    obtain ⟨h, hsol, hreg, -⟩ := hδstep g₀ hd hFirst
    exact ⟨h, IsEpsSolP.mono hsol (min_le_right _ _), EpsRegP.mono hreg (min_le_right _ _),
      hAp (min T δ) (lt_min hT hδpos) (min_le_left _ _) h
        (IsEpsSolP.mono hsol (min_le_right _ _)) (EpsRegP.mono hreg (min_le_right _ _))⟩
  -- the iteration
  have hpoint : ∀ n : ℕ, ∃ g : Fam, IsEpsSolP α ρ ε (hor n) Φs E g₀ g ∧
      EpsRegP α ρ ε (hor n) g ∧ ∀ τ ∈ Set.Icc 0 (hor n), Xn6 α (slice g τ) ≤ M := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
      obtain ⟨g, hsol, hreg, hbnd⟩ := ih
      by_cases hcase : hor n = T
      · -- the horizon has already reached `T`; keep the same family
        have hnext : hor (n + 1) = T := by
          have h1 : T ≤ (((n : ℝ) + 1) * δ) := by
            have h2 : min T (((n : ℝ) + 1) * δ) ≤ ((n : ℝ) + 1) * δ := min_le_right _ _
            have h3 : min T (((n : ℝ) + 1) * δ) = T := hcase
            linarith
          show min T ((((n + 1 : ℕ) : ℝ) + 1) * δ) = T
          rw [show (((n + 1 : ℕ) : ℝ) + 1) * δ = ((n : ℝ) + 2) * δ by push_cast; ring]
          exact min_eq_left (by linarith)
        refine ⟨g, ?_, ?_, ?_⟩
        · rw [hnext, ← hcase]; exact hsol
        · rw [hnext, ← hcase]; exact hreg
        · rw [hnext, ← hcase]; exact hbnd
      · -- extend by one step
        have hXn : ((n : ℝ) + 1) * δ < T := by
          by_contra hcon
          exact hcase (by
            show min T (((n : ℝ) + 1) * δ) = T
            exact min_eq_left (not_lt.mp hcon))
        have hnn : hor n = ((n : ℝ) + 1) * δ := by
          show min T (((n : ℝ) + 1) * δ) = ((n : ℝ) + 1) * δ
          exact min_eq_right (le_of_lt hXn)
        have hnnonneg : 0 ≤ hor n := le_of_lt (hhor_pos n)
        -- the restart
        have hdd : EpsDatumP α ρ ε (slice g (hor n)) := hreg.2 (hor n) ⟨hnnonneg, le_rfl⟩
        have hbd : Xn6 α (slice g (hor n)) ≤ M := hbnd (hor n) ⟨hnnonneg, le_rfl⟩
        obtain ⟨H, hHsol, hHreg, -⟩ := hδstep (slice g (hor n)) hdd hbd
        have hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ (hor n) = H z θ 0 := by
          intro z θ hz hθ hθ'
          exact (hHsol.1 z θ).symm
        -- the junction value of the scheme's source term
        let hR : Fn := fun z θ => epsRHSP α ρ ε Φs E g (hor n) z θ
        have hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => g z θ s) (hR z θ) (Set.Icc 0 (hor n)) (hor n) := by
          intro z θ hz hθ hθ'
          exact hsol.2 z θ (hor n) hz ⟨hθ, hθ'⟩ ⟨hnnonneg, le_rfl⟩
        have hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => H z θ s) (hR z θ) (Set.Icc 0 δ) 0 := by
          intro z θ hz hθ hθ'
          have h1 := hHsol.2 z θ 0 hz ⟨hθ, hθ'⟩ ⟨le_rfl, le_of_lt hδpos⟩
          have h2 : hR z θ = epsRHSP α ρ ε Φs E H 0 z θ := by
            have h3 : epsRHSP α ρ ε Φs E g (hor n) = epsRHSP α ρ ε Φs E H 0 :=
              epsRHSP_congr (W := g) (W' := H) (τ := hor n) (τ' := 0)
                (funext fun z => funext fun θ => (hHsol.1 z θ).symm)
            exact congrFun (congrFun h3 z) θ
          rw [h2]; exact h1
        -- the glued family
        have hFsol : IsEpsSolP α ρ ε (hor n + δ) Φs E g₀
            (concat g (shiftFam H (hor n)) (hor n)) :=
          hSol (hor n) δ g H hnnonneg hδpos hsol hHsol
        have hFreg : EpsRegP α ρ ε (hor n + δ) (concat g (shiftFam H (hor n)) (hor n)) :=
          hReg (hor n) δ g H hR hnnonneg hδpos hreg hHreg hval hderG hderH
        have hle : hor (n + 1) ≤ hor n + δ := by
          have hnext : hor (n + 1) = min T (((n : ℝ) + 2) * δ) := by
            show min T ((((n + 1 : ℕ) : ℝ) + 1) * δ) = min T (((n : ℝ) + 2) * δ)
            rw [show (((n + 1 : ℕ) : ℝ) + 1) * δ = ((n : ℝ) + 2) * δ by push_cast; ring]
          rw [hnext, hnn]
          exact le_trans (min_le_right _ _) (by linarith)
        refine ⟨concat g (shiftFam H (hor n)) (hor n), IsEpsSolP.mono hFsol hle,
          EpsRegP.mono hFreg hle, ?_⟩
        exact hAp (hor (n + 1)) (hhor_pos (n + 1)) (hhor_le (n + 1)) _
          (IsEpsSolP.mono hFsol hle) (EpsRegP.mono hFreg hle)
  obtain ⟨g, hsol, hreg, hbnd⟩ := hpoint N
  have hhorN : hor N = T := by
    show min T ((((N : ℕ) : ℝ) + 1) * δ) = T
    exact min_eq_left (by push_cast; linarith)
  exact ⟨g, by rwa [hhorN] at hsol, by rwa [hhorN] at hreg, by rwa [hhorN] at hbnd⟩

end Work.FTS.StrongEps.StrongEpsP
