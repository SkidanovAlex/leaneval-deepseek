import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

/-- `intDegree` of a power of a non-zero rational function: the degree at infinity is additive
under multiplication, so it is linear for powers.  (Same statement as the already proved
`Work.PointlessTwist.Kummer.intDegree_pow_of_ne_zero`; reproved here so that this file depends
only on the definitions of this chapter.) -/
private lemma intDegree_pow_eq {F : Type*} [Field F] {f : RatFunc F} (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).intDegree = (n : ℤ) * f.intDegree := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero k hf) hf, ih]
    push_cast
    first | refl_ring1 | ring

/-- The order at infinity of a power.  Follows by induction from `ordInf_mul`; there is also the
existing `Work.PointlessTwist.Kummer.intDegree_pow_of_ne_zero` for `RatFunc.intDegree`. -/
theorem ordInf_pow {F : Type*} [Field F] {f : RatFunc F} (hf : f ≠ 0) (n : ℕ) :
    Work.Genus.ordInf (f ^ n) = n * Work.Genus.ordInf f := by
  unfold Work.Genus.ordInf
  rw [intDegree_pow_eq hf n]
  first | refl_ring1 | ring

end Work.Genus.OrderInf
