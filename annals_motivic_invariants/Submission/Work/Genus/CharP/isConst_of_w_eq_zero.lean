import Mathlib
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.Main.w_sq_eq_aeval_curveCubic
import Submission.Work.Genus.Main.curveCubic_natDegree
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

/-- **The degenerate (`w = 0`) case of the descent.**  If the "completed ordinate"
`w = 2y + a₁x + a₃` of an `F(t)`-point `(x, y)` of the Weierstrass curve `E` vanishes, then both
`x` and `y` are constants.

Indeed `w = 0` gives `A(x) = w ^ 2 = 0` for the cubic `A = Work.Genus.curveCubic E`
(`Work.Genus.Main.w_sq_eq_aeval_curveCubic`); `A` has degree `3` in characteristic `≠ 2`
(`Work.Genus.Main.curveCubic_natDegree`, using `(4 : F) = 2 * 2 ≠ 0`), so `A ≠ 0` and `x` is a root of
a non-zero polynomial over `F`, i.e. algebraic over `F`; as `F` is algebraically closed in
`F(t)` (`Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic`) `x` is constant.  Finally
`y = -(a₁x + a₃) / 2` is then a constant as well. -/
theorem isConst_of_w_eq_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (E : WeierstrassCurve F)
    {x y : RatFunc F} (h : Work.Genus.CharP.WEqn E x y)
    (hw0 : 2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃ = 0) :
    Work.Genus.CharP.IsConst x ∧ Work.Genus.CharP.IsConst y := by
  -- `2` is invertible in `F(t)` since it is invertible in `F`.
  have h2R : (2 : RatFunc F) ≠ 0 := by
    have hcast : algebraMap F (RatFunc F) (2 : F) = (2 : RatFunc F) := by
      rw [RatFunc.algebraMap_eq_C]
      exact map_ofNat RatFunc.C 2
    rw [← hcast]
    intro hh
    exact h2 ((algebraMap F (RatFunc F)).injective (by rw [hh, map_zero]))
  -- `A(x) = w ^ 2 = 0`, and `A` is a non-zero cubic, so `x` is algebraic over `F`.
  have hw_sq := Work.Genus.Main.w_sq_eq_aeval_curveCubic E h
  have haeval : Polynomial.aeval x (Work.Genus.curveCubic E) = 0 := by
    rw [← hw_sq, hw0]; ring
  have hAne : Work.Genus.curveCubic E ≠ 0 := by
    intro hzero
    have h3 : (Work.Genus.curveCubic E).natDegree = 3 :=
      Work.Genus.Main.curveCubic_natDegree E (show (4 : F) ≠ 0 by
        have : (4 : F) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2)
    rw [hzero] at h3
    simp at h3
  obtain ⟨x₀, hx₀⟩ :=
    Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic (F := F) ⟨_, hAne, haeval⟩
  -- From `w = 0` we get `y = -(a₁ x + a₃) / 2`, a constant.
  have hy : y = -(algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃) / 2 := by
    have hz : 2 * y = -(algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃) := by
      linear_combination (norm := first | refl_ring1 | ring1) hw0
    rw [eq_div_iff h2R, mul_comm]
    exact hz
  refine ⟨⟨x₀, hx₀⟩, -(E.a₁ * x₀ + E.a₃) / 2, ?_⟩
  have hconst : algebraMap F (RatFunc F) (-(E.a₁ * x₀ + E.a₃) / 2)
      = -(algebraMap F (RatFunc F) E.a₁ * algebraMap F (RatFunc F) x₀
          + algebraMap F (RatFunc F) E.a₃) / 2 := by
    simp only [map_div₀, map_neg, map_add, map_mul, map_ofNat]
  rw [hy, hx₀, ← hconst]

end Work.Genus.CharP
