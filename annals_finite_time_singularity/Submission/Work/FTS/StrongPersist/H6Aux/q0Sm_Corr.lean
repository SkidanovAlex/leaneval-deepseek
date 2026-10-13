import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

open scoped Real Topology
open MeasureTheory Set

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The three elementary ingredients

`Corr α f = Γ(θ)·radA α f z` (`Transfer.Corr_eq_radA`), where

`radA α f z = −ampA α z·L₁₂ f(z) + (ampB α z/c(α))·L₁₂(Transport f)(0)`,

`ampA α z = 2z/(c(α)(1+z)²)`, `ampB α z = 2z²/(1+z)³`.  Each factor is smooth on its own
domain: `L₁₂ f` is `C⁶` on `(0,∞)` (order-seven honesty of `f`, `LinMem6Acf.contDiffOn6_L12_of`),
the two rational `z`-factors are `C^∞` on `(0,∞)` (their denominators do not vanish there,
`c(α) ≠ 0` from `Spaces.c_bounds`), and `Γ` is `C^∞` on `(0,π/2)` (`OpenPkg.contDiffOn_Gam_Q0`).
The lemmas below assemble them. -/

/-- `c(α) ≠ 0` for `0 < α ≤ 1` (from `1/10 ≤ c(α)`, `Work.Spaces.c_bounds`). -/
theorem c_ne_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : Work.Spaces.c α ≠ 0 := by
  have h := (Work.Spaces.c_bounds α hα hα1).1
  intro h0; rw [h0] at h; norm_num at h

/-- The nonlocal `z`-factor `ampA α = 2z/(c(α)(1+z)²)` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_ampA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) := by
  have hc := c_ne_zero hα hα1
  change ContDiffOn ℝ n (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2))
    (Set.Ioi (0 : ℝ))
  exact (((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id).div
    ((contDiffOn_const (c := Work.Spaces.c α)).mul
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 2))
    (fun z hz => mul_ne_zero hc (pow_ne_zero 2 (by linarith [show (0 : ℝ) < z from hz]))))

/-- The projector `z`-factor `ampB α = 2z²/(1+z)³` is `C^n` on `(0,∞)` (it does not depend on
`α`). -/
theorem contDiffOn_ampB (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) := by
  change ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi (0 : ℝ))
  exact (((contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_id.pow 2)).div
    (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 3)
    (fun z hz => pow_ne_zero 3 (by linarith [show (0 : ℝ) < z from hz])))

/-- **The radial profile of the transfer defect is `C⁶` on the open half-line** as soon as
`L₁₂ f` is. -/
theorem contDiffOn_radA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hL : ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 6 (fun z => Work.FTS.CoercivityFix.Transfer.radA α f z) (Set.Ioi (0 : ℝ)) := by
  have hampA := contDiffOn_ampA α hα hα1 6
  have hampB := contDiffOn_ampB α 6
  have key : ContDiffOn ℝ 6
      (fun z : ℝ => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
        + (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
    ((hampA.mul hL).neg).add ((hampB.div_const (Work.Spaces.c α)).mul contDiffOn_const)
  refine key.congr (fun z _ => ?_)
  simp only [Work.FTS.CoercivityFix.Transfer.radA]
  ring

/-- **`L₁₂ f` is `C⁶` on `(0,∞)`** for the coercivity class `H6Adm α f` with order-seven
honesty.  (The statement of `LinMem6Acf.contDiffOn6_L12_of` is phrased with
`Construction.L12`, which is `Coercivity.L12f` definitionally.) -/
theorem contDiffOn6_L12f {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) := by
  have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
  rwa [show (fun z => Work.Construction.L12 f z)
        = (fun z => Work.Coercivity.L12f f z) from rfl] at h

/-- **Finite-order regularity of the nonlocal correction.**  `Corr α f = LGammaT α f − Lhat f` is, by `Corr_eq`, the separated sum `-(2zΓ(θ)/(c(1+z)²))·L₁₂(f)(z) + (Γ(θ)/c)(2z²/(1+z)³)·L₁₂(Transport f)(0)`.  For `H6Adm α f` (giving `SmoothOpen f` and `L₁₂f(0) = 0`) and order-seven honesty `HkMem α 7 f`, the moment `L₁₂ f` is `C^6` on `(0,∞)` (`EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk`, packaged as `L6Aux.LinMem6Acf.contDiffOn6_L12_of`), so `Corr α f` is `C^6` on the open quadrant — the finite-order class the level-six additivity clause needs.  (The *infinite-order* statement is false — see `NOTES_L3_lin_FALSE.md` — but order six suffices.) -/
theorem q0Sm_Corr : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.CoercivityFix.Transfer.Q0Sm 6 (Work.FTS.CoercivityFix.Corr α f) := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f hadm h7
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the two analytic inputs
  have hL : ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn6_L12f hadm.reg.1 h7
  have hR : ContDiffOn ℝ 6 (fun z => Work.FTS.CoercivityFix.Transfer.radA α f z)
      (Set.Ioi (0 : ℝ)) := contDiffOn_radA α hα0 hα1 hL
  -- the separated product is `C⁶` on the quadrant
  have hGR : ContDiffOn ℝ 6
      (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 * Work.FTS.CoercivityFix.Transfer.radA α f p.1)
      Work.Construction.Qd := by
    have h1 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
        Work.Construction.Qd := Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 6
    exact h1.mul (hR.comp contDiffOn_fst (fun p hp => hp.1))
  -- `Corr` is that product
  have hfun : Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z := by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α f z θ
  rw [hfun]
  unfold Work.FTS.CoercivityFix.Transfer.Q0Sm
  exact hGR

end Work.FTS.StrongPersist.H6Aux
