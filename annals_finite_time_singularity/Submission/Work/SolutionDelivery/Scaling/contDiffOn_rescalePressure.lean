import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

/-- The `(x,t) ↦ (λx, λ²t)` change of variables that carries `univ ×ˢ Ico 0 1`
into `univ ×ˢ Ico 0 T` when `λ² = T`. -/
private def rescaleProd (lam : ℝ) : Work.SolutionDelivery.R3 × ℝ → Work.SolutionDelivery.R3 × ℝ :=
  fun z => (lam • z.1, lam ^ 2 * z.2)

private theorem contDiffOn_rescaleProd {lam : ℝ} (s : Set (Work.SolutionDelivery.R3 × ℝ)) :
    ContDiffOn ℝ 1 (rescaleProd lam) s := by
  unfold rescaleProd
  fun_prop

private theorem mapsTo_rescaleProd {lam T : ℝ} (hlam : lam ≠ 0) (hsq : lam ^ 2 = T) :
    Set.MapsTo (rescaleProd lam) (Set.univ ×ˢ Set.Ico 0 1) (Set.univ ×ˢ Set.Ico 0 T) := by
  have hsqpos : 0 < lam ^ 2 := by positivity
  have hTpos : 0 < T := by rw [← hsq]; exact hsqpos
  rintro ⟨x, t⟩ ⟨-, ht⟩
  simp only [rescaleProd, Set.mem_prod, Set.mem_univ, Set.mem_Ico, true_and]
  exact ⟨mul_nonneg hsqpos.le ht.1, by nlinarith [ht.2, hsqpos, hsq]⟩

/-- **The rescaling preserves the `C¹` regularity of the pressure.**  If `p` is `C¹` on the
slab `ℝ³ × [0,T)` then `(x,t) ↦ λ² p (λx) (λ²t)` is `C¹` on `ℝ³ × [0,1)`, provided `λ ≠ 0`
and `λ² = T`: the map `(x,t) ↦ (λx, λ²t)` is linear (hence smooth) and multiplies `[0,1)`
into `[0,T)`, and multiplication by the constant `λ²` is smooth. -/
theorem contDiffOn_rescalePressure {lam T : ℝ} {p : Work.SolutionDelivery.R3 → ℝ → ℝ}
    (hlam : lam ≠ 0) (hsq : lam ^ 2 = T)
    (h : ContDiffOn ℝ 1 p.uncurry (Set.univ ×ˢ Set.Ico 0 T)) :
    ContDiffOn ℝ 1 (Work.SolutionDelivery.rescalePressure lam p).uncurry
      (Set.univ ×ˢ Set.Ico 0 1) := by
  have hcomp : ContDiffOn ℝ 1 (fun z : Work.SolutionDelivery.R3 × ℝ =>
      p.uncurry (rescaleProd lam z)) (Set.univ ×ˢ Set.Ico 0 1) :=
    h.comp (contDiffOn_rescaleProd _) (mapsTo_rescaleProd hlam hsq)
  have hsmul := hcomp.const_smul (lam ^ 2)
  refine hsmul.congr ?_
  rintro ⟨x, t⟩ -
  simp only [Function.uncurry, Work.SolutionDelivery.rescalePressure,
    rescaleProd, smul_eq_mul]

end Work.SolutionDelivery.Scaling
