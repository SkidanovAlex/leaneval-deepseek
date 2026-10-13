import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.StrongEps.EpsZero.L12_Dz_zero_of_slices
import Submission.Work.FTS.StrongEps.EpsZero.pz_prod_integrable_of_smoothOpen
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.Apriori.ZeroMode
import Submission.Work.FTS.Apriori.ZeroMode.L12_Dz_zero
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FTS.FinalClock.L12LinearSub
import Submission.Work.FTS.StrongEps.EpsZero.Pieces
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsZero

set_option linter.unusedVariables false

/-- **The zero mode of `D_z` on the class `C`.**

For a profile `f` of the class `C` (`SmoothOpen` on the open quadrant, `ℋ⁷`-honest, with the
`BdryTraces` boundary vanishing at level `6`) which vanishes outside the open quadrant, the
`L₁₂` zero mode of `D_z f = z ∂_z f` vanishes:

  `L₁₂(D_z f)(0) = 0`.

Route.  `ClassC` gives `SmoothOpen f` (`ClassC.reg`), `HkMem α 7 f` (`ClassC.mem`) and the
boundary traces `BdryTraces α 6 f` (`ClassC.tr`); `hzero` gives the point values at `z = 0` and
the (identically zero) slices at `θ = 0, π/2`.  Then

* `slice_facts_of_classC` produces the three *radial* slice facts: differentiability of the
  `z`-slices on `(0,∞)`, continuity of the slices on `[0,∞)` (the right limit at `0⁺` is
  `f 0 θ = 0`, from the `(a,b) = (0,0)` boundary trace `z (f w)² → 0`), and decay at `+∞`;
* `pz_prod_integrable_of_smoothOpen` gives the joint integrability of `K(θ)·∂_z f(z,θ)` on
  `(0,∞) × Iθ`, which is the Fubini input (it needs only `HkMem α 1 f`, a downward-monotonicity
  of `HkMem α 7 f`);
* `L12_Dz_zero_of_slices` concludes, by the FTC `∫_0^∞ ∂_z f(s,θ) ds = f(∞,θ) - f(0,θ) = 0`
  for a.e. `θ` and one Fubini swap. -/
theorem L12_Dz_zero_classC {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0) :
    Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := by
  obtain ⟨hdiff, hcont0, hdec⟩ := slice_facts_of_classC hC.reg hC.tr hzero
  have hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 := fun θ _ => hzero 0 θ (by simp)
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    pz_prod_integrable_of_smoothOpen hC.reg
      (Work.FTS.IPGen.HkMem_mono_le hC.reg 1 (by norm_num) hC.mem)
  exact L12_Dz_zero_of_slices hdiff hcont0 hdec hvan hint

/-- **The zero mode of `N_*` at the paper's `λ = lamfun μ`, on the class `C`.**

At `λ = lamfun μ` the coefficient of `D_z g` in `N_* μ λ g = -μ g - (μ + λ + μλ)·D_z g`
collapses: `μ + lamfun μ + μ·lamfun μ = -μ`, so that (for `μ ≠ -1`)

  `N_* μ (lamfun μ) f = μ·(D_z f - f)`.

Hence `L₁₂(N_* μ (lamfun μ) f)(0) = μ·(L₁₂(D_z f)(0) - L₁₂(f)(0)) = -μ·L₁₂(f)(0)`, the
`D_z`-zero-mode being `L12_Dz_zero_classC` and the additivity of `L₁₂(·)(0)` on the two
summands being `GalBasis.cc.L12_add_of_HkMem` (both summands are `HkMem α 4` and `SmoothOpen`:
scalar multiples of `f`, resp. of `D_z f`, the latter descending from `HkMem α 7 f` via
`IPGen.HkMem_Dz_le`). -/
theorem Nstar_zero_classC {α μ : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0)
    (hμ : μ ≠ -1) :
    Work.Construction.L12 (Work.Construction.Nstar μ (Work.Construction.lamfun μ) f) 0
      = - μ * Work.Construction.L12 f 0 := by
  -- ## the collapse of `N_*` at `λ = lamfun μ`
  have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
    have hμ1 : (1 : ℝ) + μ ≠ 0 := by
      intro h
      exact hμ (by linarith)
    rw [Work.Construction.lamfun]
    field_simp
    ring
  have hcollapse : Work.Construction.Nstar μ (Work.Construction.lamfun μ) f
      = fun z θ => -μ * f z θ + μ * Work.Spaces.Dz f z θ := by
    funext z θ
    simp only [Work.Construction.Nstar]
    rw [hcoef]
    ring
  -- ## smoothness and `ℋ⁴`-honesty of the two summands
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hC.reg
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hsmf.Dz
  have hsm_a : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -μ * f z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen]
    have h : (Function.uncurry fun z θ => -μ * f z θ)
        = fun p : ℝ × ℝ => (-μ) • Function.uncurry f p := rfl
    rw [h]
    exact ContDiffOn.const_smul _ hsmf
  have hsm_b : Work.FTS.EllipticEst.SmoothOpen (fun z θ => μ * Work.Spaces.Dz f z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen]
    have h : (Function.uncurry fun z θ => μ * Work.Spaces.Dz f z θ)
        = fun p : ℝ × ℝ => μ • Function.uncurry (Work.Spaces.Dz f) p := rfl
    rw [h]
    exact ContDiffOn.const_smul _ hsmDz
  have hmem_A : Work.Spaces.HkMem α 4 (fun z θ => -μ * f z θ) :=
    Work.FTS.GalBasis.HkMem_const_mul_all (-μ)
      (Work.FTS.IPGen.HkMem_mono_le hsmf 4 (by norm_num) hC.mem)
  have hmem_B : Work.Spaces.HkMem α 4 (fun z θ => μ * Work.Spaces.Dz f z θ) :=
    Work.FTS.GalBasis.HkMem_const_mul_all μ
      (Work.FTS.IPGen.HkMem_Dz_le hsmf
        (Work.FTS.IPGen.HkMem_mono_le hsmf 5 (by norm_num) hC.mem))
  -- ## additivity of `L₁₂(·)(0)` on the two summands
  have hadd := Work.FTS.GalBasis.cc.L12_add_of_HkMem hsm_a hsm_b hmem_A hmem_B
  -- ## the two homogeneous pieces, and the `D_z`-zero-mode
  have hDz : Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := L12_Dz_zero_classC hC hzero
  rw [hcollapse, hadd]
  simp only [Work.Construction.L12] at hDz ⊢
  rw [Work.FM.L12_const_mul, Work.FM.L12_const_mul, hDz]
  ring

end Work.FTS.StrongEps.EpsZero
