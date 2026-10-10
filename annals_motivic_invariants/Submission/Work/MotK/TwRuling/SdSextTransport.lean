import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Kummer transport of the T-twisted ruling point

With `w^5 = h`, the sextic `kleinTwR0` of the inverse map is *weighted* homogeneous under the
Kummer substitution `y_i ↦ w^i y_i` of the coordinates and `h ↦ 1`: replacing the twisted model
at `h` by the split model at `1` rescales the ruling point `λ·A(c) + μ·B(c)` in such a way that
`kleinTwR0` picks up exactly a factor `w^3`.  This is the transport identity used to compare the
twisted ruling data with the split one; it is a pure polynomial identity in
`a, b, w, c 0, …, c 4, l, m` (with `h` rewritten to `w^5`), so it is settled by unfolding the
definitions and closing the resulting identity with `ring`.
-/

set_option maxHeartbeats 8000000

namespace Work.MotK.TwRuling

theorem SdSextTransport {R : Type*} [CommRing R] (a b h w : R) (hw : w ^ 5 = h)
    (c : Fin 5 → R) (l m : R) :
    Work.MotK.kleinTwR0 a b h (Work.MotK.kleinTwRulePt a b h c l m)
      = w ^ 3 * Work.MotK.kleinTwR0 a b 1
          (Work.MotK.kleinTwRulePt a b 1 (fun i => w ^ (i : ℕ) * c i) l (w * m)) := by
  -- replace the parameter `h` by `w ^ 5`, turning the goal into a polynomial identity
  rw [← hw]
  -- expand the twisted ruling data, the twisted Pfaffian map and the polar form
  unfold Work.MotK.kleinTwR0 Work.MotK.kleinTwRulePt Work.MotK.kleinTwRuleA Work.MotK.kleinTwRuleB
    Work.MotK.kleinTwPolarP Work.MotK.kleinTwTan Work.MotK.kleinTwBilin Work.MotK.kleinTwQ
    Work.MotK.kleinTwP Work.MotK.kleinTwP0 Work.MotK.kleinTwP1 Work.MotK.kleinTwP2
    Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  -- reduce function addition and the standard basis vectors `kleinE k = Pi.single k 1`
  simp only [Pi.add_apply, Pi.single_apply]
  -- evaluate the index arithmetic coming from `Pi.single` on `Fin 5`
  norm_num
  first | refl_ring1 | ring

end Work.MotK.TwRuling
