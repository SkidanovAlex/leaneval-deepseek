import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved` (RX-A2)

For a `LimApprox` datum `g` (the limit family of the strong route: on every horizon `[0,T]` it is
the `Qd`-jet limit of class-`C` approximants `gn` with uniform `ℋ⁴`-smallness `C₀ α²` and a
uniform `ℋ⁴`-Lipschitz modulus `L₀` in the fake time `τ`), the mixed slots of order `≤ 2` of the
slices `slice g τ` are

* **uniformly bounded** on the open quadrant: `|D_z^bD_θ^a g(·,·,τ)| ≤ 10/√(γ-1)·(C₀ α²)`, and
* **`τ`-Lipschitz**: `|D_z^bD_θ^a g(·,·,τ) - D_z^bD_θ^a g(·,·,τ')| ≤ C·|τ - τ'|`,

both uniformly in `τ, τ' ∈ [0,T]` and `(z,θ) ∈ Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)`.

This is the `(b,a)`-uniform form of the interior estimate that the domination arguments for the
angular parametric integrals of `coeff_C2` need.

## The proof

Both halves are limits of the corresponding bounds for the approximants `gn`.

*Uniform bound.* The class-`C` interior `L^∞`–`ℋ⁴` trade-off
`Work.FTS.StrongEps.SupPort.classC_mixed_sup_le`,
`|mixed b a f z θ| ≤ 10/√(γ-1)·Xn α f`, applied to `f = slice (gn n) τ` and combined with the
`Xn`-smallness clause `Xn α (slice (gn n) τ) ≤ C₀ α²` bounds every approximant; the `Qd`-jet
convergence clause of `LimApprox` then passes the bound to `slice g τ` (`le_of_tendsto`).

*Lipschitz bound.* `ClassC α` is a linear subspace, so the *difference*
`slice (gn n) τ - slice (gn n) τ'` is again class-`C` (`StrongEps.EComparison.classC_sub`);
`classC_mixed_sup_le` prices its slot by `Xn α` of the difference, which the Lipschitz clause of
`LimApprox` bounds by `L₀|τ - τ'|`; the additivity `mixed b a F - mixed b a G = mixed b a (F - G)`
on the open quadrant (`EllipticEst.TTSlot11Aux.mixed_sub_open`) identifies the slot of the
difference with the difference of the slots, and the jet convergence of `LimApprox` again passes
the bound to the limit.

The Lipschitz half is proved here rather than imported from
`Submission.Work.FTS_RegExport.RXT.lim_mixed_lip` because that sibling module does not currently
build (its final `le_of_tendsto` has its two arguments in the wrong order); the argument below is
the same one, written out.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXA2

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (LimApprox)

set_option autoImplicit false

theorem lim_mixed_bounds_proved {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ,
      a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (C₀ * αG ^ 2) ∧
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
            - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|
            ≤ L * |τ - τ'| := by
  obtain ⟨gn, _B, L₀, hC, hLip, hjet, _hmu⟩ := hA T hT
  have hc : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0,
    mul_nonneg hc (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  refine ⟨?_, ?_⟩
  · -- ## the uniform bound
    have h1 : ∀ n : ℕ,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
          ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (C₀ * αG ^ 2) := by
      intro n
      refine le_trans (Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1
        (hC n τ hτ).1 b a hab hzθ) ?_
      exact mul_le_mul_of_nonneg_left (hC n τ hτ).2.1 hc
    have h2 : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|) atTop
        (𝓝 |Work.Spaces.mixed b a (slice g τ) z θ|) :=
      (hjet τ hτ b a (by omega) z θ hzθ).abs
    exact le_of_tendsto h2 (Eventually.of_forall h1)
  · -- ## the τ-Lipschitz bound
    have hbd : ∀ᶠ n : ℕ in atTop,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by
      refine Eventually.of_forall (fun n => ?_)
      set F : Work.FTS.Galerkin.Fn := slice (gn n) τ with hF
      set G : Work.FTS.Galerkin.Fn := slice (gn n) τ' with hG
      have hsub : Work.FTS.ClassC.ClassC αG (fun z θ => F z θ - G z θ) :=
        Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ).1 (hC n τ' hτ').1
      have hsup := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub b a hab hzθ
      have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
        (hC n τ hτ).1.reg (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
      have hlip : Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ)
          ≤ max L₀ 0 * |τ - τ'| :=
        le_trans (hLip n τ hτ τ' hτ')
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
          = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by
            rw [hlin]
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1)
              * Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ) := hsup
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (max L₀ 0 * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left hlip hc
        _ = 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by ring
    have htend : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|) atTop
        (𝓝 |Work.Spaces.mixed b a (slice g τ) z θ
          - Work.Spaces.mixed b a (slice g τ') z θ|) :=
      ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
    exact le_of_tendsto htend hbd

end Work.FTS_RegExport.RXA2
