import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.PairsAux
import Submission.Work.Q44Geom.ncard_ball_le

/-!
# `Work.Q44Geom.ncard_pair_ball_le`

The set of pairs `(A, B)` of integer vectors (indexed by two monomial bases) whose
Euclidean norms are bounded by `R` and `S` respectively is exactly the product of the
two norm balls, so its cardinality is the product of the two cardinalities; each factor
is bounded by the box count `(2 * ⌈·⌉₊ + 1) ^ (number of coordinates)`, which is
`Work.Q44Geom.ncard_ball_le`.
-/

set_option autoImplicit false

namespace Work.Q44Geom

theorem ncard_pair_ball_le {d d' : ℕ} (R S : ℝ) :
    (({p : (Work.HP.Mon d 4 → ℤ) × (Work.HP.Mon d' 4 → ℤ) |
        Work.HP.eNorm p.1 ≤ R ∧ Work.HP.eNorm p.2 ≤ S} : Set _).ncard : ℝ)
      ≤ (2 * (⌈R⌉₊ : ℝ) + 1) ^ Fintype.card (Work.HP.Mon d 4)
        * (2 * (⌈S⌉₊ : ℝ) + 1) ^ Fintype.card (Work.HP.Mon d' 4) := by
  classical
  have hset : ({p : (Work.HP.Mon d 4 → ℤ) × (Work.HP.Mon d' 4 → ℤ) |
        Work.HP.eNorm p.1 ≤ R ∧ Work.HP.eNorm p.2 ≤ S} :
          Set ((Work.HP.Mon d 4 → ℤ) × (Work.HP.Mon d' 4 → ℤ)))
      = ({A : Work.HP.Mon d 4 → ℤ | Work.HP.eNorm A ≤ R} : Set (Work.HP.Mon d 4 → ℤ))
        ×ˢ ({B : Work.HP.Mon d' 4 → ℤ | Work.HP.eNorm B ≤ S} :
          Set (Work.HP.Mon d' 4 → ℤ)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_prod]
  rw [hset, Set.ncard_prod, Nat.cast_mul]
  exact mul_le_mul (ncard_ball_le (ι := Work.HP.Mon d 4) R)
    (ncard_ball_le (ι := Work.HP.Mon d' 4) S) (Nat.cast_nonneg _) (by positivity)

end Work.Q44Geom
