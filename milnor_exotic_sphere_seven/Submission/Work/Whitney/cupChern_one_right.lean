import Mathlib
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The right unit law of the graded cup product

`Work.Whitney.cupChern a b x y` is the product `x ⌣ y` of a class in `H^{2a}` with one in `H^{2b}`,
with the degree bookkeeping `2a + 2b = 2(a+b)` done by `Work.Thom.cohTransport`.  This module
proves the unit law in the second variable: for `b : ℕ` and `y ∈ H^{2b}(B;ℤ)`,

  `cupChern b 0 y 1 = y`   (up to the degree identity `2*(b+0) = 2*b`),

the class `1 ∈ H^{0}` being the unit `Work.Cohomology.oneH` (`Work.Thom.chernClass_zero_eq_oneH`
identifies `c_0` of a bundle with it).  It is what makes the `(i,j) = (b,0)` summand of the
right-hand side of the Whitney formula reduce to `c_b` of the first factor.
-/

namespace Work.Whitney

noncomputable section

variable {B : Type} [TopologicalSpace B]

theorem cupChern_one_right (b : ℕ) (y : Work.Thom.Coh ℤ (2 * b) B) :
    cupChern b 0 y
        (Work.Thom.cohTransport (by rfl : 2 * 0 = 0)
          (Work.Cohomology.oneH ℤ (ssB B)))
      = Work.Thom.cohTransport (by rfl : 2 * (b + 0) = 2 * b) y := by
  rw [cupChern_def]
  have hz : Work.Thom.cohTransport (by rfl : (2 : ℕ) * 0 = 0)
      (Work.Cohomology.oneH ℤ (ssB B)) = Work.Cohomology.oneH ℤ (ssB B) :=
    Work.Thom.cohTransport_rfl _
  rw [hz]
  have hcup : Work.Cohomology.cupH' ℤ (ssB B) (2 * b) (2 * 0) y
      (Work.Cohomology.oneH ℤ (ssB B)) = y :=
    Work.Cohomology.cupH'_one_right (R := ℤ) (X := ssB B) (2 * b) y
  rw [hcup]

end

end Work.Whitney
