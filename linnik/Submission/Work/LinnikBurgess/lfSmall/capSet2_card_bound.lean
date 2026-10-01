import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.lfSmall.capSet2_card_le
import Submission.Work.LinnikBurgess.card_hensel_le
import Submission.Work.LinnikBurgess.critN_tripleVanish_content
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.natDegree_critN_le_four
import Submission.Work.LinnikBurgess.aeval_dist_eq_norm

namespace Work.LinnikBurgess.lfSmall

theorem capSet2_card_bound {e J : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hJc : padicValNat 2 (contAB a b) = J)
    (hcoeff : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    ((capSet2 e a b).card : ℝ) ≤ (10 : ℝ) ^ 4
      * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2) :=
  capSet2_card_le he a b i hJc hcoeff hi

end Work.LinnikBurgess.lfSmall
