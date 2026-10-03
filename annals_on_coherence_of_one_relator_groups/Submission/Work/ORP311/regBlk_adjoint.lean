import Mathlib
import Submission.Work.ORP311.P311Defs

set_option autoImplicit false

open scoped InnerProductSpace

namespace Work.ORP311

open Work.ORVonNeumann

/-- The adjoint of the blockwise left regular operator `regBlk n t` is `regBlk n t⁻¹`.

Indeed `regBlk n t = ∑ i, hinclude i ∘ (λ(t) ∘ hcoord i)`, and taking adjoints termwise with
`hinclude i† = hcoord i`, `hcoord i† = hinclude i` and `λ(t)† = λ(t⁻¹)` gives the corresponding
sum for `t⁻¹`. -/
theorem regBlk_adjoint {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (t : G) : ContinuousLinearMap.adjoint (Work.ORP311.regBlk (G := G) n t) = Work.ORP311.regBlk (G := G) n t⁻¹ := by
  have hterm : ∀ i : Fin n,
      ContinuousLinearMap.adjoint ((Rep.hinclude (G := G) n i).comp
          ((Rep.leftRegOp t).comp (Rep.hcoord (G := G) n i)))
        = (Rep.hinclude (G := G) n i).comp
          ((Rep.leftRegOp t⁻¹).comp (Rep.hcoord (G := G) n i)) := by
    intro i
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      Rep.hinclude_adjoint, Rep.hcoord_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, Rep.leftRegOp_star]
    rw [ContinuousLinearMap.comp_assoc]
  simp only [Work.ORP311.regBlk, map_sum, hterm]

end Work.ORP311
