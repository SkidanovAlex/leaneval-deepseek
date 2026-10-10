import Mathlib
import Submission.Work.MotK.KleinTwLink
import Submission.Work.MotK.TwDataMod5
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The composed source-side identity of the T-twisted link

With `x := kleinTwR a b h w` the target-side point of the twisted link (which lies on the quadric
`{kleinTwQ = 0}` as soon as `w 0 = 0`, by I2'), the projection `v = kleinTwPi p x = x - x_0·p`
satisfies, by `KleinTwStereo_pi`,

  `kleinTwStereo a b h p v = -(kleinTwBilin a b h p x) • x`.

Since `kleinTwP` is homogeneous of degree `2` (`kleinTwP_homog`), composing with I2'
(`kleinTwP (kleinTwR w) = kleinTwSDualInv w • w`) gives

  `kleinTwP (kleinTwStereo a b h p (kleinTwPi p (kleinTwR a b h w)))
     = (kleinTwBilin a b h p (kleinTwR a b h w))^2 · kleinTwSDualInv a b h w • w`.

This is the statement that `f ∘ g = id` on the source side, i.e. one of the two compositions of
the twisted Cremona map `f = P ∘ y` with the inverse link `g = π_p ∘ R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

theorem KleinTwLinkComp1 {R : Type*} [CommRing R] (a b h : R) (p w : Fin 5 → R)
    (hp : Work.MotK.kleinTwQ a b h p = 0) (hw : w 0 = 0) :
    Work.MotK.kleinTwP a b h (Work.MotK.kleinTwStereo a b h p
        (Work.MotK.kleinTwPi p (Work.MotK.kleinTwR a b h w)))
      = fun k => (Work.MotK.kleinTwBilin a b h p (Work.MotK.kleinTwR a b h w)) ^ 2
          * Work.MotK.kleinTwSDualInv a b h w * w k := by
  set x : Fin 5 → R := Work.MotK.kleinTwR a b h w with hx
  -- `x` lies on the quadric because its `0`-th coordinate is `s'(w) * w 0 = 0` (I2')
  have hx0 : Work.MotK.kleinTwQ a b h x = 0 := by
    show Work.MotK.kleinTwP a b h x 0 = 0
    rw [hx, Work.MotK.KleinTwI2inv, hw, mul_zero]
  -- the stereographic parametrisation at the projection of `x`
  have hst : Work.MotK.kleinTwStereo a b h p (Work.MotK.kleinTwPi p x)
      = fun i => -(Work.MotK.kleinTwBilin a b h p x) * x i := by
    rw [Work.MotK.KleinTwStereo_pi a b h p x hp, hx0]
    funext i
    first | refl_ring1 | ring
  rw [hst, Work.MotK.kleinTwP_homog]
  funext k
  rw [Work.MotK.KleinTwI2inv]
  first | refl_ring1 | ring

end Work.MotK
