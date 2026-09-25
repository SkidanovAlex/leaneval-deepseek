import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj
import Submission.Work.ShafarevichKoch.GenusAux
import Submission.Work.ShafarevichKoch.conjInv_ideal_structure
import Submission.Work.ShafarevichKoch.absNorm_span_sc
import Submission.Work.ShafarevichKoch.span_sc_mul_span_sc
import Submission.Work.ShafarevichKoch.span_sc_sq_eq_of_dvd
import Submission.Work.ShafarevichKoch.absNorm_conjR
import Submission.Work.ShafarevichKoch.eq_one_of_squarefree_mul_sq_eq_sq
import Submission.Work.ShafarevichKoch.nat_eq_of_span_singleton_eq
import Submission.Work.ShafarevichKoch.conjR_mul_self
import Submission.Work.ShafarevichKoch.norm_int_pos
import Submission.Work.ShafarevichKoch.card_divisors_filter_le
import Submission.Work.ShafarevichKoch.exists_mk0Span_eq_of_twoTorsion
import Submission.Work.ShafarevichKoch.card_twoTorsion_le_32
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five
import Submission.Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN
import Submission.Work.ClassFieldTower.card_quotient_sq_eq_card_twoTorsion

/-!
# `rank₂ Cl(ℚ(√-30030)) ≤ 5`

Genus theory for the imaginary quadratic field `Kc = ℚ(√-30030)`.  The `2`-torsion classes of the
class group are the classes of the ideals `⟨d, √-30030⟩` with `d ∣ 30030` (genus descent), and
`d` and `30030/d` give the same class, so at most the `32` divisors of `30030` that are `≤ 173`
occur.  Hence `#(Cl/Cl²) = #Cl[2] ≤ 32 = 2^5`, i.e. `rank₂ Cl(Kc) ≤ 5`.

The two mathematical inputs of this file are `exists_mk0Span_eq_of_twoTorsion` (the genus descent:
every ideal class of order dividing `2` is represented by `⟨d, scR⟩`) and
`card_twoTorsion_le_32` (the counting consequence).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The `2`-rank of the class group of `Kc = ℚ(√-30030)` is at most `5`.**

`classGroupTwoRank Kc = log₂ #(Cl(Kc)/Cl(Kc)²) = log₂ #Cl(Kc)[2]`, and the `2`-torsion of
`Cl(Kc)` has at most `32 = 2^5` elements by genus theory. -/
theorem classGroupTwoRank_Kc_le :
    Work.ClassFieldTower.classGroupTwoRank Work.ClassFieldTower.Kc ≤ 5 := by
  have h1 : classGroupTwoRank Kc
      = Nat.log 2 (Nat.card {x : ClassGroup (𝓞 Kc) // x ^ 2 = 1}) := by
    rw [classGroupTwoRank, card_quotient_sq_eq_card_twoTorsion]
  rw [h1]
  calc Nat.log 2 (Nat.card {x : ClassGroup (𝓞 Kc) // x ^ 2 = 1}) ≤ Nat.log 2 32 :=
        Nat.log_mono_right card_twoTorsion_le_32
    _ = 5 := by decide

end Work.ShafarevichKoch
