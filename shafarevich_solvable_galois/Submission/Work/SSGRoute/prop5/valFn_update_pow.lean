import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.FreeGroup.Basic
import Submission.Work.SSGRoute.prop5.valFn_update_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open Work.CohomologicalShrinking

/-- The value map `valFn` is a homomorphism in each slot (`valFn_update_mul`); consequently,
replacing a slot by a power multiplies the value by the power. -/
theorem valFn_update_pow_eq_nsmul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a : Work.Shrinking.freeOperatorGroup G d) :
    ∀ n : ℕ, 1 ≤ n →
      valFn p G i j d hj hji (Function.update x k (a ^ n)) =
        n • valFn p G i j d hj hji (Function.update x k a) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [pow_succ, valFn_update_mul p G i j d hj hji x k (a ^ n) a, ih, succ_nsmul]

theorem valFn_update_pow (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a : Work.Shrinking.freeOperatorGroup G d) :
    valFn p G i j d hj hji (Function.update x k (a ^ p)) = 0 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [valFn_update_pow_eq_nsmul p G i j d hj hji x k a p hp,
    ← Nat.cast_smul_eq_nsmul (ZMod p) p _, ZMod.natCast_self p, zero_smul]

end Work.SSGRoute.prop5
