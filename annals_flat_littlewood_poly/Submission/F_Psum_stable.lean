import Mathlib
import Submission.RSPsum_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

/-- Coefficients of `P s` below `2 ^ t` agree with those of `P t`, provided `t ≤ s`. -/
lemma coeff_P_stable {t s i : ℕ} (hts : t ≤ s) (hi : i < 2 ^ t) :
    (P s).coeff i = (P t).coeff i := by
  refine Nat.le_induction (m := t) (P := fun n _ => (P n).coeff i = (P t).coeff i)
    ?base ?succ s hts
  · rfl
  · intro n htn ih
    calc
      (P (n + 1)).coeff i = (P n).coeff i := coeff_P_extend n i (by
        exact lt_of_lt_of_le hi (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) htn))
      _ = (P t).coeff i := ih

lemma Psum_stable {t s m : ℕ} (hm : m ≤ 2 ^ t) (hts : t ≤ s) : Psum s m = Psum t m := by
  rw [Psum, Psum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < m := Finset.mem_range.mp hk
  have hk2 : k < 2 ^ t := lt_of_lt_of_le hklt hm
  rw [coeff_P_stable hts hk2]

end RudinShapiro
end Submission
