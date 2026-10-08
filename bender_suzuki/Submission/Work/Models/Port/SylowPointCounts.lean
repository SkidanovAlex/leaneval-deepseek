/-
**The number of Sylow `2`-subgroups of the three Bender families equals the degree of the
Bender action.**

In each of the three families the Borel subgroup `B` is the normalizer of the unipotent radical
`U`, which is a Sylow `2`-subgroup (`Submission/ModelStructure.lean` and
`Submission/PSU3/CentralizerQuotient.lean`).  Hence the number of Sylow `2`-subgroups is the
index of `B`, i.e. the number of points of the Bender action:

* `Sz(2^(2n+1))`: `q² + 1`,
* `PSU(3,2ⁿ)`: `q³ + 1`,
* `PSL(2,2ⁿ)`: `q + 1`.

For `PSL(2,2ⁿ)` this recovers the classical fact that `PSL(2,K)` acts sharply `2`-transitively
on the `q+1` Sylow `2`-subgroups.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.ModelStructure
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.PSU3.SuzukiCondition
import Submission.Work.Models.Port.PSU3.PSU3Order
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.SuzukiSetup
import Submission.Work.Models.Port.BenderAction
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_sylow_two_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

/-! ## `Sz(2^(2n+1))` -/

namespace Submission.Sz

/-- The Sylow `2`-subgroups of `Sz(2^(2n+1))` are in bijection with the cosets of the Borel
subgroup. -/
theorem card_sylow2_eq_card_quotient (n : ℕ) :
    Nat.card (Sylow 2 (SzModel n)) = Nat.card (SzModel n ⧸ szBorelS n) := by
  rw [card_sylow2_szModel n, ← Subgroup.index_eq_card, card_szBorelS_index]

end Submission.Sz

/-! ## `PSU(3, 2ⁿ)` -/

namespace Submission.PSU3

/-- The unipotent radical `Ū` has odd index in `PSU(3,2ⁿ)`, i.e. it is a Sylow `2`-subgroup. -/
theorem not_dvd_index_psu3U (n : ℕ) (hn : 2 ≤ n) : ¬ 2 ∣ (psu3U n).index := by
  have hn1 : 1 ≤ n := by omega
  have hcard : Nat.card ↥(psu3U n) = 2 ^ (3 * n) :=
    (Submission.card_psu3U n hn).trans (card_suUS n hn1)
  have hmul := Subgroup.card_mul_index (psu3U n)
  rw [hcard] at hmul
  have hG := card_PSU3Model n hn1
  have hkey : 2 ^ (3 * n) * ((psu3U n).index * Nat.gcd 3 (2 ^ n + 1)) =
      2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by
    rw [← mul_assoc, hmul, hG, mul_assoc]
  have hcancel := Nat.mul_left_cancel (pow_pos (by norm_num : (0 : ℕ) < 2) (3 * n)) hkey
  intro h2
  have hodd : Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) :=
    (odd_two_pow_sub_one (2 * n) (by omega)).mul (odd_two_pow_add_one (3 * n) (by omega))
  have heven : Even ((psu3U n).index * Nat.gcd 3 (2 ^ n + 1)) :=
    even_iff_two_dvd.mpr (dvd_mul_of_dvd_left h2 _)
  rw [hcancel] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- The Sylow `2`-subgroups of `PSU(3,2ⁿ)` are in bijection with the cosets of the Borel
subgroup; there are `q³ + 1` of them. -/
theorem card_sylow2_eq_card_quotient (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Sylow 2 (PSU3Model n)) = Nat.card (PSU3Model n ⧸ psu3B n) := by
  have hn1 : 1 ≤ n := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (PSU3Model n) := (isPGroup_psu3U n hn1).toSylow (not_dvd_index_psu3U n hn)
  have hP : (P : Subgroup (PSU3Model n)) = psu3U n :=
    IsPGroup.toSylow_coe (isPGroup_psu3U n hn1) (not_dvd_index_psu3U n hn)
  rw [Sylow.card_eq_index_normalizer P,
    show ((P : Sylow 2 (PSU3Model n)) : Set (PSU3Model n)) = (psu3U n : Set (PSU3Model n)) from by
      rw [← Sylow.coe_coe, hP],
    psu3B_eq_normalizer n hn, Subgroup.index_eq_card]

end Submission.PSU3

/-! ## `PSL(2, 2ⁿ)` -/

namespace Submission.PSL2

/-- The Sylow `2`-subgroups of `PSL(2,2ⁿ)` are in bijection with the points of the projective
line; there are `q + 1` of them. -/
theorem card_sylow2_eq_card_quotient (n : ℕ) (hn : 1 ≤ n)
    (a : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) :
    Nat.card (Sylow 2 (PSL2Model n)) =
      Nat.card (PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) a) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  rw [Commons.GroupTheory.SL2.card_sylow_two_projectiveSpecialLinearGroup (K := GaloisField 2 n)
      hchar,
    ← Subgroup.index_eq_card,
    pSL2Stabilizer_index_eq_one_add_sylowTwo n hn a,
    GaloisField.card (p := 2) (n := n) (by omega),
    Nat.add_comm]

end Submission.PSL2
