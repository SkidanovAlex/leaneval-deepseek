import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- `lift` is additive in its spectator-operator argument, hence it commutes with
finite sums of spectator operators.  (This is `lift_add` iterated over the finset;
the empty case uses `lift 0 = 0`.) -/
theorem lift_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (s : Finset ι) (f : ι → E →ₗ[ℂ] E) :
    Work.BoseB4.lift (∑ i ∈ s, f i) = ∑ i ∈ s, Work.BoseB4.lift (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hzero : lift (0 : E →ₗ[ℂ] E) = 0 := by
      apply LinearMap.ext; intro Ψ; apply Finsupp.ext; intro n
      simp [lift_apply]
    simpa using hzero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lift_add, ih]

end Work.BoseB4
