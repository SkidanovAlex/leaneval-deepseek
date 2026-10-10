import Mathlib
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.CharP.natDegree_num_pow
import Submission.Work.Genus.CharP.natDegree_denom_pow
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

/-- If `x = X ^ p` with `p` prime and `x` of positive size, then `X` has strictly smaller size
than `x`.  Indeed `X ≠ 0` (else `x = 0` and `Size x = 0`), so the two degree formulae give
`Size x = p * Size X` with `p ≥ 2`, and `Size X ≠ 0` forces `Size X ≥ 1`, whence
`Size X < p * Size X = Size x`. -/
theorem size_lt_of_pow_eq {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] {x X : RatFunc F}
    (hx : x = X ^ p) (hn : 0 < Work.Genus.CharP.Size x) :
    Work.Genus.CharP.Size X < Work.Genus.CharP.Size x := by
  have hp : p.Prime := Fact.out
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Work.Genus.CharP.size_zero] at hn
    exact lt_irrefl 0 hn
  have hX0 : X ≠ 0 := fun h => hx0 (by rw [hx, h, zero_pow hp.pos.ne'])
  have hS : Work.Genus.CharP.Size x = p * Work.Genus.CharP.Size X := by
    rw [hx]
    simp only [Work.Genus.CharP.Size]
    rw [Work.Genus.CharP.natDegree_num_pow hX0 p, Work.Genus.CharP.natDegree_denom_pow hX0 p]
    first | refl_ring1 | ring
  have hSX : 0 < Work.Genus.CharP.Size X := by
    by_contra h
    have h0 : Work.Genus.CharP.Size X = 0 := Nat.eq_zero_of_not_pos h
    rw [hS, h0, mul_zero] at hn
    exact lt_irrefl 0 hn
  calc Work.Genus.CharP.Size X = 1 * Work.Genus.CharP.Size X := (one_mul _).symm
    _ < p * Work.Genus.CharP.Size X := Nat.mul_lt_mul_of_pos_right hp.one_lt hSX
    _ = Work.Genus.CharP.Size x := hS.symm

end Work.Genus.CharP
