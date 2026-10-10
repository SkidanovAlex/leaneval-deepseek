import Mathlib
import Submission.Work.MotV5.WtDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open Polynomial

/-- Substituting `T ↦ T + c` does not increase the degree. -/
private lemma natDegree_comp_X_add_C_le {F : Type*} [Field F] (P : Polynomial F) (c : F) :
    (P.comp (X + C c)).natDegree ≤ P.natDegree := by
  calc (P.comp (X + C c)).natDegree ≤ P.natDegree * (X + C c).natDegree := natDegree_comp_le
    _ = P.natDegree * 1 := by rw [natDegree_X_add_C]
    _ = P.natDegree := by ring

theorem natDegree_kleinQPoly_le {F : Type*} [Field F] (a b : F) (P : Polynomial F) :
    (kleinQPoly a b P).natDegree ≤ 2 * P.natDegree := by
  -- Each of the three summands of the Klein polynomial has degree at most `2 * P.natDegree`.
  have hsq : (P ^ 2).natDegree ≤ 2 * P.natDegree :=
    natDegree_pow_le (p := P) (n := 2)
  have h1 : (-C (a * b) * P ^ 2).natDegree ≤ 2 * P.natDegree := by
    rw [← C_neg]
    exact le_trans (natDegree_C_mul_le _ _) hsq
  have h2 : (C (a ^ 2) * (P.comp (X + C 2)) * (P.comp (X + C 3))).natDegree
      ≤ 2 * P.natDegree := by
    calc (C (a ^ 2) * (P.comp (X + C 2)) * (P.comp (X + C 3))).natDegree
        ≤ (C (a ^ 2) * (P.comp (X + C 2))).natDegree + (P.comp (X + C 3)).natDegree :=
          natDegree_mul_le
      _ ≤ P.natDegree + P.natDegree :=
          add_le_add (le_trans (natDegree_C_mul_le _ _)
            (natDegree_comp_X_add_C_le P 2)) (natDegree_comp_X_add_C_le P 3)
      _ = 2 * P.natDegree := by ring
  have h3 : (C (b ^ 2) * (P.comp (X + C 1)) * (P.comp (X + C 4))).natDegree
      ≤ 2 * P.natDegree := by
    calc (C (b ^ 2) * (P.comp (X + C 1)) * (P.comp (X + C 4))).natDegree
        ≤ (C (b ^ 2) * (P.comp (X + C 1))).natDegree + (P.comp (X + C 4)).natDegree :=
          natDegree_mul_le
      _ ≤ P.natDegree + P.natDegree :=
          add_le_add (le_trans (natDegree_C_mul_le _ _)
            (natDegree_comp_X_add_C_le P 1)) (natDegree_comp_X_add_C_le P 4)
      _ = 2 * P.natDegree := by ring
  -- Degrees of sums and differences are bounded by the maximum of the summands.
  unfold kleinQPoly
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans (natDegree_add_le _ _) (max_le h1 h2)
  · exact h3

end Work.MotV5
