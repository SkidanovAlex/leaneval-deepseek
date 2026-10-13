/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlueParts/Induction.lean` — the restart-and-concatenate induction

The continuation half of `Work.FTS.StrongEps.EpsGlue`, isolated from the two junction glues it
consumes: given

* a local step `hstep` (for every `M' ≥ 0` a `δ > 0` and, for every datum of `Xn6`-size `≤ M'`, a
  regular `ε`-solution on `[0,δ]`),
* the a-priori bound `hAp` for the fixed datum `g₀` and constant `M`,
* the two **glue lemmas** as hypotheses (`hSol` for `IsEpsSol`, `hReg` for `EpsReg`),
* the bootstrap value `Xn6 α g₀ ≤ M` (`hFirst`, supplied by `Work.FTS.StrongEps.GlueParts.FirstStep`),

the conclusion is a regular `ε`-solution on the whole `[0,T]` with `Xn6 ≤ M`.

The proof restarts the step every `δ` and concatenates: `Pf n` is the family on
`[0, min T ((n+1)δ)]`; the induction step either stops (the horizon has reached `T`) or glues the
restart at the datum `slice g (min T ((n+1)δ))`, keeps the horizon `min T ((n+2)δ)` and re-applies
`hAp` to obtain the `ℋ⁶`-bound `≤ M` on the new piece (the a-priori bound is exactly what keeps
every restart datum at size `≤ M`, so the *same* `δ` can be used at every step).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.GlueParts.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 Xn6 concat)

/-- **The restart-and-concatenate induction** (the continuation half of `EpsGlue`), with the two
junction glues as explicit hypotheses. -/
theorem EpsGlue_of_glue {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hd : EpsDatum α ρ ε g₀)
    (hstep : ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Fn, EpsDatum α ρ ε h₀ →
      Xn6 α h₀ ≤ M' →
      ∃ h : Fam, IsEpsSol α ρ ε δ Φs E h₀ h ∧ EpsReg α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) δ, Xn6 α (slice h τ) ≤ 2 * M' + 1)
    (hAp : EpsAprioriBddH α ρ ε T Φs E g₀ M)
    (hSol : ∀ (t δ : ℝ) (G H : Fam), 0 ≤ t → 0 < δ → IsEpsSol α ρ ε t Φs E g₀ G →
      IsEpsSol α ρ ε δ Φs E (slice G t) H →
      IsEpsSol α ρ ε (t + δ) Φs E g₀ (concat G (shiftFam H t) t))
    (hReg : ∀ (t δ : ℝ) (G H : Fam) (R : Fn), 0 ≤ t → 0 < δ → EpsReg α ρ ε t G →
      EpsReg α ρ ε δ H →
      (∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0) →
      (∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t) →
      (∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) →
      EpsReg α ρ ε (t + δ) (concat G (shiftFam H t) t))
    (hFirst : Xn6 α g₀ ≤ M) :
    ∃ g : Fam, IsEpsSol α ρ ε T Φs E g₀ g ∧ EpsReg α ρ ε T g ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, Xn6 α (slice g τ) ≤ M := by
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
  have hzero : ∃ g : Fam, IsEpsSol α ρ ε (hor 0) Φs E g₀ g ∧ EpsReg α ρ ε (hor 0) g ∧
      ∀ τ ∈ Set.Icc 0 (hor 0), Xn6 α (slice g τ) ≤ M := by
    have h0 : hor 0 = min T δ := by
      show min T ((((0 : ℕ) : ℝ) + 1) * δ) = min T δ
      norm_num
    rw [h0]
    obtain ⟨h, hsol, hreg, -⟩ := hδstep g₀ hd hFirst
    exact ⟨h, hsol.mono (min_le_right _ _), hreg.mono (min_le_right _ _),
      hAp (min T δ) (lt_min hT hδpos) (min_le_left _ _) h
        (hsol.mono (min_le_right _ _)) (hreg.mono (min_le_right _ _))⟩
  -- the iteration
  have hpoint : ∀ n : ℕ, ∃ g : Fam, IsEpsSol α ρ ε (hor n) Φs E g₀ g ∧
      EpsReg α ρ ε (hor n) g ∧ ∀ τ ∈ Set.Icc 0 (hor n), Xn6 α (slice g τ) ≤ M := by
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
        have hdd : EpsDatum α ρ ε (slice g (hor n)) := hreg.2 (hor n) ⟨hnnonneg, le_rfl⟩
        have hbd : Xn6 α (slice g (hor n)) ≤ M := hbnd (hor n) ⟨hnnonneg, le_rfl⟩
        obtain ⟨H, hHsol, hHreg, -⟩ := hδstep (slice g (hor n)) hdd hbd
        have hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ (hor n) = H z θ 0 := by
          intro z θ hz hθ hθ'
          exact (hHsol.1 z θ).symm
        -- the junction value of the scheme's source term
        let hR : Fn := fun z θ => Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε g) (hor n)) z θ
        have hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => g z θ s) (hR z θ) (Set.Icc 0 (hor n)) (hor n) := by
          intro z θ hz hθ hθ'
          exact hsol.2 z θ (hor n) hz ⟨hθ, hθ'⟩ ⟨hnnonneg, le_rfl⟩
        have hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => H z θ s) (hR z θ) (Set.Icc 0 δ) 0 := by
          intro z θ hz hθ hθ'
          have h1 := hHsol.2 z θ 0 hz ⟨hθ, hθ'⟩ ⟨le_rfl, le_of_lt hδpos⟩
          have h2 : hR z θ = Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε H) 0) z θ := by
            have h3 : epsRHSu α ρ ε Φs E (Jfam ρ ε g) (hor n)
                = epsRHSu α ρ ε Φs E (Jfam ρ ε H) 0 :=
              epsRHSu_junction (G := g) (H := H) (t := hor n)
                (fun z θ => (hHsol.1 z θ).symm)
            exact congrFun (congrFun (congrArg (Jeps ρ ε) h3) z) θ
          rw [h2]; exact h1
        -- the glued family
        have hFsol : IsEpsSol α ρ ε (hor n + δ) Φs E g₀
            (concat g (shiftFam H (hor n)) (hor n)) :=
          hSol (hor n) δ g H hnnonneg hδpos hsol hHsol
        have hFreg : EpsReg α ρ ε (hor n + δ) (concat g (shiftFam H (hor n)) (hor n)) :=
          hReg (hor n) δ g H hR hnnonneg hδpos hreg hHreg hval hderG hderH
        have hle : hor (n + 1) ≤ hor n + δ := by
          have hnext : hor (n + 1) = min T (((n : ℝ) + 2) * δ) := by
            show min T ((((n + 1 : ℕ) : ℝ) + 1) * δ) = min T (((n : ℝ) + 2) * δ)
            rw [show (((n + 1 : ℕ) : ℝ) + 1) * δ = ((n : ℝ) + 2) * δ by push_cast; ring]
          rw [hnext, hnn]
          exact le_trans (min_le_right _ _) (by linarith)
        refine ⟨concat g (shiftFam H (hor n)) (hor n), hFsol.mono hle, hFreg.mono hle, ?_⟩
        exact hAp (hor (n + 1)) (hhor_pos (n + 1)) (hhor_le (n + 1)) _
          (hFsol.mono hle) (hFreg.mono hle)
  obtain ⟨g, hsol, hreg, hbnd⟩ := hpoint N
  have hhorN : hor N = T := by
    show min T ((((N : ℕ) : ℝ) + 1) * δ) = T
    exact min_eq_left (by push_cast; linarith)
  exact ⟨g, by rwa [hhorN] at hsol, by rwa [hhorN] at hreg, by rwa [hhorN] at hbnd⟩

end Work.FTS.StrongEps
