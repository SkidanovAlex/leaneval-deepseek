import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Main.isCoprime_curveCubic_derivative
import Submission.Work.Genus.Main.curveCubic_natDegree
import Submission.Work.Genus.Main.w_sq_eq_aeval_curveCubic
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic
import Submission.Work.Genus.Analysis.deriv_eq_zero_of_aeval_eq_sq
import Submission.Work.Genus.Deriv.deriv_eq_zero_iff
import Submission.Work.Genus.Deriv.deriv_weierstrass
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

open Polynomial

/-- **The degenerate case of the genus chapter.**  If the "completed ordinate"
`w = 2y + a₁x + a₃` of a point `(x, y)` of the Weierstrass curve `E` vanishes, then both `x` and
`y` are constants.  Indeed `w = 0` gives `A(x) = w ^ 2 = 0` for the non-zero cubic
`A = Work.Genus.curveCubic E` (`Work.Genus.Main.w_sq_eq_aeval_curveCubic`), so `x` is algebraic
over `F` and hence constant (`Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic`); then
`y = -(a₁x + a₃)/2` is the corresponding constant. -/
private theorem aux_const_of_w_eq_zero {F : Type*} [Field F] [CharZero F]
    (E : WeierstrassCurve F) {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆)
    (hw0 : 2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃ = 0) :
    (∃ x₀ : F, x = algebraMap F (RatFunc F) x₀) ∧ (∃ y₀ : F, y = algebraMap F (RatFunc F) y₀) := by
  have h2R : (2 : RatFunc F) ≠ 0 := by
    have hcast : algebraMap F (RatFunc F) (2 : F) = (2 : RatFunc F) := by
      rw [RatFunc.algebraMap_eq_C]
      exact map_ofNat RatFunc.C 2
    rw [← hcast]
    intro h
    exact (show (2 : F) ≠ 0 by norm_num)
      ((algebraMap F (RatFunc F)).injective (by rw [h, map_zero]))
  -- `A(x) = w ^ 2 = 0`, and `A` is a non-zero cubic, so `x` is algebraic over `F`.
  have hw_sq := w_sq_eq_aeval_curveCubic E h
  have haeval : Polynomial.aeval x (Work.Genus.curveCubic E) = 0 := by
    rw [← hw_sq, hw0]; ring
  have hAne : Work.Genus.curveCubic E ≠ 0 := by
    intro hzero
    have h3 : (Work.Genus.curveCubic E).natDegree = 3 :=
      curveCubic_natDegree E (show (4 : F) ≠ 0 by norm_num)
    rw [hzero] at h3
    simp at h3
  obtain ⟨x₀, hx₀⟩ := exists_algebraMap_eq_of_isAlgebraic (F := F) ⟨_, hAne, haeval⟩
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

/-- **The algebraic core of the genus chapter: in characteristic zero every `F(t)`-point of a
non-singular Weierstrass curve over `F` is constant.**  Both coordinates of a solution of the
Weierstrass equation over `F(t)` lie in `F`.

Route: put `w = 2y + a₁x + a₃`, `A = Work.Genus.curveCubic E`.  If `w = 0` then `A(x) = 0`
(`Work.Genus.Main.w_sq_eq_aeval_curveCubic`), so `x` is algebraic over `F` (witness `A`) and hence
constant (`Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic`); then `y = -(a₁x + a₃)/2` is
constant.  If `w ≠ 0`: `A.natDegree = 3` (`Work.Genus.Main.curveCubic_natDegree`, from `CharZero`)
and `IsCoprime A A'` (`Work.Genus.Main.isCoprime_curveCubic_derivative`), so
`Work.Genus.Analysis.deriv_eq_zero_of_aeval_eq_sq` gives `x' = 0`; then
`Work.Genus.Deriv.deriv_weierstrass` gives `y' = 0` as well (in the form `w * y' = δ * x'`, so
`2 * w * y' = 0`); finally `Work.Genus.Deriv.deriv_eq_zero_iff` turns `x' = 0`, `y' = 0` into
constants. -/
theorem exists_algebraMap_of_weierstrass {F : Type*} [Field F] [CharZero F] (E : WeierstrassCurve F)
    (hΔ : E.Δ ≠ 0) {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆) :
    (∃ x₀ : F, x = algebraMap F (RatFunc F) x₀) ∧ (∃ y₀ : F, y = algebraMap F (RatFunc F) y₀) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  -- The completed ordinate `w = 2y + a₁x + a₃`.
  set w : RatFunc F := 2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃
    with hwdef
  have hw_sq : w ^ 2 = Polynomial.aeval x (Work.Genus.curveCubic E) := by
    rw [hwdef]; exact w_sq_eq_aeval_curveCubic E h
  rcases eq_or_ne w 0 with hw0 | hwne
  · exact aux_const_of_w_eq_zero E h (by rw [← hwdef]; exact hw0)
  · -- `w ≠ 0`: differentiate the equation `A(x) = w²`.
    have hA : (Work.Genus.curveCubic E).natDegree = 3 := curveCubic_natDegree E h4
    have hsq : IsCoprime (Work.Genus.curveCubic E)
        (Polynomial.derivative (Work.Genus.curveCubic E)) :=
      isCoprime_curveCubic_derivative E h2 hΔ
    have hdx : Work.Genus.deriv x = 0 :=
      Work.Genus.Analysis.deriv_eq_zero_of_aeval_eq_sq (A := Work.Genus.curveCubic E)
        h2 hA hsq hwne hw_sq.symm
    -- The differentiated Weierstrass equation gives `w * y' = 0`.
    have hdy : Work.Genus.deriv y = 0 := by
      have hw' := Work.Genus.Deriv.deriv_weierstrass E h
      rw [hdx, mul_zero] at hw'
      rw [← hwdef] at hw'
      exact (mul_eq_zero.mp hw').resolve_left hwne
    exact ⟨(Work.Genus.Deriv.deriv_eq_zero_iff x).mp hdx,
      (Work.Genus.Deriv.deriv_eq_zero_iff y).mp hdy⟩

end Work.Genus.Main
