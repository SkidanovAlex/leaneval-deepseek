import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

/-!
# `C^{1,α}` is preserved by the datum scaling `x ↦ λ • F (λ • x)`

The rescaling `rescaleDatum lam F = fun x ↦ lam • F (lam • x)` of a `C^{1,α}` vector field is
again `C^{1,α}`: it is smooth (composition of the smooth `F` with the dilation), its derivative

  `fderiv ℝ (rescaleDatum lam F) x = lam ^ 2 • fderiv ℝ F (lam • x)`

is bounded by `‖lam‖^2 * C` when `‖fderiv ℝ F‖ ≤ C`, and is `α`-Hölder with constant
`‖lam^2‖ * C * ‖lam‖^α` because the dilation `x ↦ lam • x` is `‖lam‖`-Lipschitz, and a Hölder
function composed with a Lipschitz map — and then multiplied by a constant — stays Hölder.

(The conclusion holds for *every* real `lam`, including `0`: then `rescaleDatum 0 F = 0`.)
-/

/-- **The `dist`/`HolderWith` bridge.**  A pointwise bound of the form
`dist (f x) (f y) ≤ C * dist x y ^ r` (real exponent) upgrades to `HolderWith C r f`, which is
stated in terms of `edist` and the `ENNReal` power. -/
theorem holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : NNReal} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
      ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- **The derivative of the rescaled datum.**  For a differentiable field `F`,

  `fderiv ℝ (rescaleDatum lam F) x = lam ^ 2 • fderiv ℝ F (lam • x)`.

Indeed `rescaleDatum lam F = lam • (F ∘ (lam • ·))`, the chain rule gives
`fderiv ℝ (F ∘ (lam • ·)) x = (fderiv ℝ F (lam • x)).comp (lam • 1)`, and
`lam • ((fderiv ℝ F (lam • x)).comp (lam • 1)) = lam ^ 2 • fderiv ℝ F (lam • x)` because
`comp` is linear in its second argument. -/
theorem fderiv_rescaleDatum {F : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (hF : Differentiable ℝ F) (lam : ℝ) (x : Work.SolutionDelivery.R3) :
    fderiv ℝ (Work.SolutionDelivery.rescaleDatum lam F) x
      = (lam ^ 2) • fderiv ℝ F (lam • x) := by
  have hA : (fun y : Work.SolutionDelivery.R3 => lam • y)
      = ⇑(lam • (1 : Work.SolutionDelivery.R3 →L[ℝ] Work.SolutionDelivery.R3)) := by
    funext y; simp
  have hdA : DifferentiableAt ℝ (fun y : Work.SolutionDelivery.R3 => lam • y) x := by
    rw [hA]; exact ContinuousLinearMap.differentiableAt _
  have hcomp : fderiv ℝ (fun y : Work.SolutionDelivery.R3 => F (lam • y)) x
      = (fderiv ℝ F (lam • x)).comp
          (lam • (1 : Work.SolutionDelivery.R3 →L[ℝ] Work.SolutionDelivery.R3)) := by
    have h := fderiv_fun_comp (𝕜 := ℝ) x (hF (lam • x)) hdA
    have hderivA : fderiv ℝ (fun y : Work.SolutionDelivery.R3 => lam • y) x
        = (lam • (1 : Work.SolutionDelivery.R3 →L[ℝ] Work.SolutionDelivery.R3)) := by
      rw [hA]; exact ContinuousLinearMap.fderiv _
    rwa [hderivA] at h
  have hsmul : fderiv ℝ (fun y : Work.SolutionDelivery.R3 => lam • F (lam • y)) x
      = lam • fderiv ℝ (fun y : Work.SolutionDelivery.R3 => F (lam • y)) x :=
    fderiv_fun_const_smul (𝕜 := ℝ) ((hF (lam • x)).comp x hdA) lam
  change fderiv ℝ (fun y : Work.SolutionDelivery.R3 => lam • F (lam • y)) x
      = lam ^ 2 • fderiv ℝ F (lam • x)
  rw [hsmul, hcomp]
  ext v
  simp [ContinuousLinearMap.comp_apply, smul_smul, sq]

theorem isContDiffHolder_rescaleDatum {α : NNReal} {lam : ℝ}
    {F : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (h : IsContDiffHolder ℝ α F) :
    IsContDiffHolder ℝ α (Work.SolutionDelivery.rescaleDatum lam F) := by
  obtain ⟨hcd, hbdd, hholder⟩ := h
  have hF : Differentiable ℝ F := hcd.differentiable_one
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness: `F` composed with the dilation, then scaled
    have hA : ContDiff ℝ 1 (fun y : Work.SolutionDelivery.R3 => lam • y) := by
      have h' : (fun y : Work.SolutionDelivery.R3 => lam • y)
          = ⇑(lam • (1 : Work.SolutionDelivery.R3 →L[ℝ] Work.SolutionDelivery.R3)) := by
        funext y; simp
      rw [h']; exact ContinuousLinearMap.contDiff _
    have h1 : ContDiff ℝ 1 (fun y : Work.SolutionDelivery.R3 => F (lam • y)) := by
      simpa [Function.comp_def] using hcd.comp hA
    exact h1.const_smul lam
  · -- boundedness of the derivative
    have hbdd' : Bornology.IsBounded (Set.range (fderiv ℝ F)) := by
      rwa [IsBoundedFun, IsBoundedFunOn, Set.image_univ] at hbdd
    obtain ⟨C, hC⟩ := hbdd'.exists_norm_le
    have hC' : ∀ x, ‖fderiv ℝ F x‖ ≤ C := fun x => hC (fderiv ℝ F x) (Set.mem_range_self x)
    rw [IsBoundedFun, IsBoundedFunOn, Set.image_univ, isBounded_iff_forall_norm_le]
    refine ⟨‖lam ^ 2‖ * C, ?_⟩
    rintro y ⟨x, rfl⟩
    rw [fderiv_rescaleDatum hF lam x, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC' (lam • x)) (norm_nonneg _)
  · -- Hölder continuity of the derivative
    obtain ⟨C, hC⟩ := hholder
    have hdist : ∀ x y : Work.SolutionDelivery.R3,
        dist (fderiv ℝ (Work.SolutionDelivery.rescaleDatum lam F) x)
          (fderiv ℝ (Work.SolutionDelivery.rescaleDatum lam F) y)
        ≤ ((‖lam ^ 2‖₊ * C * ‖lam‖₊ ^ (α : ℝ) : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
      intro x y
      calc dist (fderiv ℝ (Work.SolutionDelivery.rescaleDatum lam F) x)
              (fderiv ℝ (Work.SolutionDelivery.rescaleDatum lam F) y)
          = dist ((lam ^ 2) • fderiv ℝ F (lam • x)) ((lam ^ 2) • fderiv ℝ F (lam • y)) := by
            rw [fderiv_rescaleDatum hF lam x, fderiv_rescaleDatum hF lam y]
        _ = ‖lam ^ 2‖ * dist (fderiv ℝ F (lam • x)) (fderiv ℝ F (lam • y)) := by
            rw [dist_eq_norm,
                show (lam ^ 2) • fderiv ℝ F (lam • x) - (lam ^ 2) • fderiv ℝ F (lam • y)
                    = (lam ^ 2) • (fderiv ℝ F (lam • x) - fderiv ℝ F (lam • y)) from
                  (smul_sub (lam ^ 2) (fderiv ℝ F (lam • x)) (fderiv ℝ F (lam • y))).symm,
                norm_smul, dist_eq_norm]
        _ ≤ ‖lam ^ 2‖ * ((C : ℝ) * dist (lam • x) (lam • y) ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left (hC.dist_le (lam • x) (lam • y)) (norm_nonneg _)
        _ = ((‖lam ^ 2‖₊ * C * ‖lam‖₊ ^ (α : ℝ) : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
            rw [dist_smul₀ lam, Real.mul_rpow (norm_nonneg lam) dist_nonneg]
            simp only [NNReal.coe_mul, NNReal.coe_rpow, coe_nnnorm]
            ring
    exact ⟨_, holderWith_of_dist_le hdist⟩

end Work.SolutionDelivery.Scaling
