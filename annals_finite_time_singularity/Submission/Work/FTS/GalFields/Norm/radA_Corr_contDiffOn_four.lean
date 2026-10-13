/-
# `radA α f` and `Corr α f` are `C⁴` on their domains

The transfer defect `Corr α f = 𝓛_Γ^T f − 𝓛̂ f` of the coercivity fix is a *separated* product
(`CoercivityFix.Transfer.Corr_eq_radA`)

  `Corr α f z θ = Γ(θ)·radA α f z`,
  `radA α f z = −a(z)·L₁₂(f)(z) + (b(z)/c(α))·L₁₂(Transport f)(0)`,

of the angular factor `Γ α` and a `z`-only *radial profile* `radA α f`, with
`a(z) = 2z/(c(α)(1+z)²)`, `b(z) = 2z²/(1+z)³` the two elementary rational factors.

This module proves that both objects are of class `C⁴`: `radA α f` on the open half-line
`(0,∞)`, and `Corr α f` (jointly, i.e. as a function on the *open quadrant* `Q0 = (0,∞)×(0,π/2)`)
— for a datum `f` which is `C^∞` on `Q0` (`Work.FTS.EllipticEst.SmoothOpen`) and honest in the
weighted space `ℋ⁵` (`Work.Spaces.HkMem α 5 f`).  The smoothness input is the order-`4`
regularity of the nonlocal tail integral `L₁₂ f` on `(0,∞)`, which `UopHk.contDiffOn_L12_k`
supplies from `SmoothOpen f` and `HkMem α 4 f` (and `ℋ⁵ ⟹ ℋ⁴` by
`Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen`); the rational factors are smooth because
`1/10 ≤ c(α)` (`Work.Spaces.c_bounds`) and `1 + z > 0` on `(0,∞)`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.StrongPersist.H6Aux.CorrAux
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 The nonlocal tail integral: order `4` from `ℋ⁵` -/

/-- **`L₁₂ f ∈ C⁴((0,∞))`** for a datum smooth on the open quadrant and honest in `ℋ⁵`.

`ℋ⁵` descends to `ℋ⁴` (`HkMem_of_le_of_smoothOpen`), and `contDiffOn_L12_k` with `k = 4`
gives the order-`4` regularity of the elliptic tail integral `Work.Elliptic.L12`; the
identification `Work.Construction.L12 = Work.Elliptic.L12` transfers it to the form used by
the radial profile `radA`. -/
theorem L12f_contDiffOn_four_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem
  have hEll : ContDiffOn ℝ 4 (Work.Elliptic.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem4 (by norm_num)
  have hCon : ContDiffOn ℝ 4 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact hEll
  have hfun : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
  rw [hfun]
  exact hCon

/-! ## §2 The radial profile `radA` -/

/-- **`radA α f ∈ C⁴((0,∞))`**: the two rational `z`-factors `a`, `b` are `C⁴` there (because
`c(α) ≠ 0` and `1 + z > 0`), and the only analytic input is `L₁₂ f ∈ C⁴((0,∞))`. -/
theorem radA_contDiffOn_four_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
  have h12 : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    L12f_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
      = fun z => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
    simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  exact ((((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1).of_le
      (by norm_num)).mul h12).neg).add
    (((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampB_div α).of_le
      (by norm_num)).mul contDiffOn_const)

/-! ## §3 The transfer defect `Corr` -/

/-- **`Corr α f ∈ C⁴` on the open quadrant.**  By `Corr_eq_sep` the defect is the separated
product `Γ(θ)·radA α f z`; writing `Γ α = c(α)·gamCoef α` turns it into the product of the
constant `c(α)` with the separated product `gamCoef α θ · radA α f z`, for which
`linMem_sep_mul` gives joint `C⁴`-regularity from the `C⁴`-regularity of `radA α f` alone. -/
theorem Corr_contDiffOn_four_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α f))
      Work.FTS.EllipticEst.Q0 := by
  have hradA : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
    radA_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem
  have hsep := Work.FTS.StrongPersist.linMem_sep_mul (α := α) (n := 4)
    (B := Work.FTS.CoercivityFix.Transfer.radA α f) hradA
  have hfun : Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z) := by
    funext z θ
    rw [Work.FTS.StrongPersist.H6Aux.Corr_eq_sep α f]
    show Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z
      = Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z)
    rw [congrFun (Work.FTS.StrongPersist.H6Aux.Gam_eq_c_mul_gamCoef hα hα1) θ]
    ring
  rw [hfun]
  have hconst : ContDiffOn ℝ 4 (fun _ : ℝ × ℝ => Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const
  refine (hconst.mul hsep).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair]

/-! ## §4 The requested conjunction -/

theorem radA_Corr_contDiffOn_four {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) ∧
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α f))
        Work.FTS.EllipticEst.Q0 :=
  ⟨radA_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem,
    Corr_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem⟩

end Work.FTS.GalFields.Norm
