import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.ZassenhausSuzuki.GenHypSetup
import Submission.Work.ZassenhausSuzuki.Q_suzuki_sq
import Submission.Work.ZassenhausSuzuki.numClasses_stronglyReal_general
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.normalizer_twoPoint
import Submission.Work.ZassenhausSuzuki.Odd.OddCore
import Submission.Work.ZassenhausSuzuki.Odd.OddFib
import Submission.Work.ZassenhausSuzuki.Odd.OddData
import Submission.Work.ZassenhausSuzuki.Odd.card_SRodd_eq
import Submission.Work.ZassenhausSuzuki.Odd.dvd_card_BadOdd
import Submission.Work.ZassenhausSuzuki.Odd.endgame_numeric

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Every odd-order element of a Suzuki group configuration is strongly real

The proof of `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki` by the counting argument
of Huppert–Blackburn III XI.11.6 (a) (Suzuki 1962, §10).

The two counting laws of `ℱ = IsCZ` (`sum_card_sub_one`, `sum_card_mul_card_sub_one`) are
rewritten as sums over the orders occurring in `ℱ` (`sum_card_sub_one_eq_sum_Fib`,
`sum_card_mul_card_sub_one_eq_sum_Fib`) with weight `mVal a = #(ℱ-subgroups of order a)`; the
normaliser index `kVal a` satisfies `mVal a * a * kVal a = |G|` (`mVal_mul_kVal`), takes the
values `2`, `4` (`kVal_mem`) and is `2` at `a = q - 1` (`kVal_q_sub_one`).  The orders other than
`q - 1` are pairwise coprime and coprime to `q(q-1)` (`coprime_of_mem_Vals`,
`coprime_pair_of_mem_Vals`).  The numerical lemma `endgame_numeric` then forces the "bad" set
`BadOdd` to be empty.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- The first counting law in the form used by the numerical endgame:
`Σ_a mVal a * (a - 1) = |G| - q⁴ - |BadOdd|`. -/
theorem hsum1_rat (h : SzOddHyp H Q t) :
    ∑ a ∈ Vals G, (mVal G a : ℚ) * (a - 1)
      = (Nat.card G : ℚ) - (q H : ℚ) ^ 4 - (Nat.card {y : G // BadOdd y} : ℚ) := by
  classical
  have h1 := sum_card_sub_one h
  have h2 := sum_card_sub_one_eq_sum_Fib (G := G)
  have h3 := card_SRodd_eq h
  -- `Σ_a mVal a * (a - 1) + 1 = |SRodd|`
  have hnat : (∑ a ∈ Vals G, mVal G a * (a - 1))
      + 1 = Nat.card {x : G // SRodd x} := by
    rw [← h1, h2]
    rfl
  have hnatq : ((∑ a ∈ Vals G, mVal G a * (a - 1) : ℕ) : ℚ) + 1
      = (Nat.card {x : G // SRodd x} : ℚ) := by
    rw [← hnat]
    push_cast
    ring
  have h3q : (Nat.card {x : G // SRodd x} : ℚ) + (Nat.card {y : G // BadOdd y} : ℚ)
      + (q H : ℚ) ^ 4 = (Nat.card G : ℚ) + 1 := by
    have := congrArg (fun n : ℕ => (n : ℚ)) h3
    push_cast at this
    exact this
  have hcast : ((∑ a ∈ Vals G, mVal G a * (a - 1) : ℕ) : ℚ)
      = ∑ a ∈ Vals G, (mVal G a : ℚ) * (a - 1) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have ha1 : 1 ≤ a := by have := five_le_of_mem_Vals h ha; omega
    have h1a : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by rw [Nat.cast_sub ha1, Nat.cast_one]
    rw [Nat.cast_mul, h1a]
  rw [← hcast]
  linarith

theorem odd_isStronglyReal_of_suzuki {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hG : IsSimpleGroup G)
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    (hord : Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    {x : G} (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) :
    Work.ZassenhausSuzuki.IsStronglyReal x := by
  have h : SzOddHyp H Q t := ⟨hG, hsplit, hzass, h2, hSuz, hord, hnab⟩
  -- the numerical endgame
  have hB : Nat.card {y : G // BadOdd y} = 0 :=
    endgame_numeric (q := q H) (B := Nat.card {y : G // BadOdd y})
      (V := Vals G) (m := mVal G) (k := kVal G)
      (by have := (q_structure h).2.2.1; omega)
      (fun a ha => five_le_of_mem_Vals h ha)
      (fun a ha => kVal_mem h ha)
      (fun a ha => by rw [mVal_mul_kVal h ha, card_G_eq h])
      (by
        have hh := hsum1_rat h
        rw [card_G_eq h] at hh
        push_cast at hh
        rw [show ((q H - 1 : ℕ) : ℚ) = (q H : ℚ) - 1 by
          rw [Nat.cast_sub (by have := (q_structure h).2.2.1; omega), Nat.cast_one]] at hh
        exact hh)
      (hsum2_rat h)
      (q_sub_one_mem_Vals h)
      (kVal_q_sub_one h)
      (fun a ha hane => coprime_of_mem_Vals h ha hane)
      (fun a ha hane b hb hbne hab => coprime_pair_of_mem_Vals (h := h) ha hb hab)
      (fun a ha hane => dvd_card_BadOdd h ha hane)
  by_contra hnsr
  have hbad : BadOdd x := ⟨hodd, hx1, hnsr⟩
  haveI : Nonempty {y : G // BadOdd y} := ⟨⟨x, hbad⟩⟩
  have := Nat.card_pos (α := {y : G // BadOdd y})
  omega

end Work.ZassenhausSuzuki.Odd
