import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux
import Submission.Work.FTS.StrongEps.EComparison.Reduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.lim_mixed_lip`

The slots `D_z^bD_θ^a g(·,·,τ)` of the limit family of `LimApprox` are Lipschitz in the fake
time `τ` on every horizon `[0,T]`, for `a + b ≤ 2`.

The approximating families `gn` of the `LimApprox` clause are class-`C` slices whose
`ℋ⁴`-difference is Lipschitz in `τ` (`Xn α (slice (gn n) τ - slice (gn n) τ') ≤ L|τ - τ'|`).
`ClassC` is a subspace, so the *difference* `slice (gn n) τ - slice (gn n) τ'` is again of
class `C`, and the interior `L^∞`–`ℋ⁴` trade-off `ClassC_mixed_sup_le`
(`|D_z^bD_θ^a f(z,θ)| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`) turns the `ℋ⁴`-Lipschitz bound into a
pointwise bound on every slot of the difference.  `mixed_sub_open` identifies the slot of the
difference with the difference of the slots, and the jet convergence of `LimApprox` passes the
bound to the limit.
-/

namespace Work.FTS_RegExport.RXT

open scoped Real Topology
open Filter

theorem lim_mixed_lip {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ| ≤ L * |τ - τ'| := by
  obtain ⟨gn, _B, L₀, hC, hLip, hjet, _hmu⟩ := hA T hT
  have hγ1 : 0 < Work.Spaces.gam αG - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hc : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0,
    mul_nonneg hc (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  have hbd : ∀ᶠ n : ℕ in atTop,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by
    refine Eventually.of_forall (fun n => ?_)
    set F : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ with hF
    set G : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ' with hG
    have hsub : Work.FTS.ClassC.ClassC αG (fun z θ => F z θ - G z θ) :=
      Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ).1 (hC n τ' hτ').1
    have hsup := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub b a hab hzθ
    have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
      (hC n τ hτ).1.reg (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
    have hlip : Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ) ≤ max L₀ 0 * |τ - τ'| := by
      refine le_trans (hLip n τ hτ τ' hτ') ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
        = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by rw [hlin]
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1)
            * Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ) := hsup
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (max L₀ 0 * |τ - τ'|) :=
          mul_le_mul_of_nonneg_left hlip hc
      _ = 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by ring
  have htend : Tendsto (fun n : ℕ =>
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|) atTop
      (𝓝 |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|) :=
    ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
  exact le_of_tendsto htend hbd

end Work.FTS_RegExport.RXT
