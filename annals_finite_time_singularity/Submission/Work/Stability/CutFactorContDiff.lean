import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The cut-off factor `x ↦ chi(ρ(x)/L)` of `ℝ³` (`ρ = ‖·‖`, `chi` the `C^∞` bump of
`Work.Stability.Cutoff`) is `C^n` for every `n`: near the origin it is identically `1` (as
`chi ≡ 1` on `[-1,1]` does it), and away from the origin it is the composition of the `C^∞` bump
`chi` with the smooth `ρ = ‖·‖`. -/
theorem CutFactorContDiff {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞)
      (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) := by
  -- It suffices to check smoothness at each point.
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Work.Cyl.rho x = 0
  · -- At the origin (the only point where `rho` vanishes) the factor is *eventually* `1`:
    -- on the ball of radius `L` we have `‖y‖ < L`, so `|rho y / L| ≤ 1` and `chi` equals `1`.
    have hx0 : x = 0 := by
      have h : ‖x‖ = 0 := by rw [← Work.Cyl.rho_eq_norm]; exact hx
      exact norm_eq_zero.mp h
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (1 : ℝ))) ?_
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds x hL) ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [hx0, sub_zero] at hy
    show Work.Stability.chi (Work.Cyl.rho y / L) = 1
    rw [Work.Cyl.rho_eq_norm]
    apply Work.Stability.chi_eq_one
    rw [abs_le]
    exact ⟨by have := div_nonneg (norm_nonneg y) hL.le; linarith,
           by rw [div_le_one hL]; linarith⟩
  · -- Off the origin, `rho = ‖·‖` is `C^∞` and `chi` is `C^∞`, so the composition is `C^n`.
    have hxne : x ≠ 0 := by
      rw [← Work.Cyl.rho_pos_iff]
      exact lt_of_le_of_ne (Work.Cyl.rho_nonneg x) (Ne.symm hx)
    have hrho : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => Work.Cyl.rho y) x := by
      have h1 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => ‖y‖) x :=
        contDiffAt_norm ℝ hxne
      exact h1.congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (funext fun y => Work.Cyl.rho_eq_norm y))
    have hchi : ContDiff ℝ (n : WithTop ℕ∞) Work.Stability.chi :=
      Work.Stability.chi_contDiff.of_le (by exact_mod_cast le_top)
    have hdiv : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) x :=
      hrho.div_const L
    -- NOTE (ChiExplicit repoint): `Work.Stability.chi` is now the *explicit* function
    -- `smoothTransition (2 - ‖·‖)`, so it unfolds to a composition; the implicit `g` and `f` of
    -- `ContDiffAt.comp` must therefore be given explicitly, otherwise the elaborator decomposes the
    -- composite as `smoothTransition ∘ (2 - ‖·‖)`.
    exact ContDiffAt.comp (g := Work.Stability.chi)
      (f := fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) x hchi.contDiffAt hdiv

end Work.Stability
