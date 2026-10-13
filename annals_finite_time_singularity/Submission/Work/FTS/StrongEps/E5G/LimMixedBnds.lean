/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/LimMixedBnds.lean` — the slot data of the limit family

Two bricks of the per-horizon E5 assembly (`E5G.PkgOfHlim`):

* `convLocUnifH6_const` — the convergence package of a *constant* sequence, so that the joint-`C¹`
  producer `E5Aux.c1_of_locUnif_slots_lip` can be applied with the limit family in the place of the
  approximants;
* `limMixedBndsOn` — for a `LimApproxOn` datum, the mixed slots of order `≤ 2` of the limit slices
  are uniformly bounded by `10/√(γ-1)·(C₀α²)` and are `τ`-Lipschitz, uniformly in the fake time and
  on the whole open quadrant.  This is the horizon-restricted form of
  `Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved` (whose proof only uses the horizon-`[0,T]`
  data), and it is what supplies the `hlip` input of `c1_of_locUnif_slots_lip` in the assembly —
  the *approximants'* slot Lipschitz would need the missing level-six chapter controlling the slots
  of `epsRHSP`, but the *limit's* is available from the `limApprox` clause alone.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.ConvLocUnifH6_JfamP
import Submission.Work.FTS.StrongEps.LimApproxSE
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option linter.unusedVariables false

/-- **The convergence package of a constant sequence**: a `C⁴`-profile honest in `ℋ⁶` up to `B` is
the locally uniform limit of the constant sequence of its own copies (every slot converges
trivially). -/
theorem convLocUnifH6_const {α B : ℝ} {f : Fn}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hB : Work.Spaces.HkNorm α 6 f ≤ B) :
    ConvLocUnifH6 α B (fun _ : ℕ => f) f := by
  refine ⟨?_, h4, hB⟩
  intro K hK hKQ j i hji
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Eventually.of_forall (fun _ _ _ => by simpa using hε)

/-- **The slot bounds and the slot `τ`-Lipschitz property of a `LimApproxOn` family.**  For a family
`g` which is the `Qd`-jet limit of class-`C` approximants with uniform `ℋ⁴`-smallness `C₀α²` and a
uniform `ℋ⁴`-Lipschitz modulus `L` in the fake time (`LimApproxOn α C₀ T Φs E g`), every mixed slot
of order `≤ 2` of `slice g τ` is bounded by `10/√(γ-1)·(C₀α²)` and is `τ`-Lipschitz, both on the
whole open quadrant and uniformly in `τ, τ' ∈ [0,T]`.

The proof is that of `Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved`: the class-`C` interior
`L^∞`–`ℋ⁴` trade-off `SupPort.classC_mixed_sup_le` applied to the approximants (resp. to their
* differences*, which are again class-`C` by `EComparison.classC_sub`) gives the bounds along the
sequence, and `le_of_tendsto` passes them to the limit through the `Qd`-jet convergence clause. -/
theorem limMixedBndsOn {α C₀ T : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : LimApproxOn α C₀ T Φs E g) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          |Work.Spaces.mixed b a (slice g τ) z θ|
              ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) ∧
            |Work.Spaces.mixed b a (slice g τ) z θ
                - Work.Spaces.mixed b a (slice g τ') z θ| ≤ L * |τ - τ'| := by
  obtain ⟨gn, B, L₀, hC, hLip, hjet, _hmu⟩ := hA
  have hc : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0,
    mul_nonneg hc (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  refine ⟨?_, ?_⟩
  · -- the uniform bound, as a limit of the approximants' bounds
    have h1 : ∀ n : ℕ,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
          ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
      intro n
      refine le_trans (Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1
        (hC n τ hτ).1 b a hab hzθ) ?_
      exact mul_le_mul_of_nonneg_left (hC n τ hτ).2.1 hc
    have h2 : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|) atTop
        (nhds |Work.Spaces.mixed b a (slice g τ) z θ|) :=
      (hjet τ hτ b a (by omega) z θ hzθ).abs
    exact le_of_tendsto h2 (Eventually.of_forall h1)
  · -- the `τ`-Lipschitz bound, from the difference profiles
    have hbd : ∀ᶠ n : ℕ in atTop,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| := by
      refine Eventually.of_forall (fun n => ?_)
      set F : Fn := slice (gn n) τ with hF
      set G : Fn := slice (gn n) τ' with hG
      have hsub : Work.FTS.ClassC.ClassC α (fun z θ => F z θ - G z θ) :=
        Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ).1 (hC n τ' hτ').1
      have hsup := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub b a hab hzθ
      have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
        (hC n τ hτ).1.reg (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
      have hlip : Work.FTS.Nonlin.Xn α (fun z θ => F z θ - G z θ)
          ≤ max L₀ 0 * |τ - τ'| :=
        le_trans (hLip n τ hτ τ' hτ')
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
          = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by rw [hlin]
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α
              (fun z θ => F z θ - G z θ) := hsup
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L₀ 0 * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left hlip hc
        _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| := by ring
    have h2 : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|) atTop
        (nhds |Work.Spaces.mixed b a (slice g τ) z θ
          - Work.Spaces.mixed b a (slice g τ') z θ|) :=
      ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
    exact le_of_tendsto h2 hbd

end Work.FTS.StrongEps.E5G
