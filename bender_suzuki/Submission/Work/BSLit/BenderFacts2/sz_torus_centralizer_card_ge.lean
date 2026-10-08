import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.BSLit.BenderFacts2.sz_titsTheta_orderOf_odd
import Submission.Work.BSLit.BenderFacts2.sz_center_szTwoGroupS_card
import Submission.Work.BSLit.BenderFacts2.sz_centralizer_mem_Vals
import Submission.Work.ZassenhausSuzuki.Odd.endgame_classify
import Submission.Work.ZassenhausSuzuki.Odd.OddData
import Submission.Work.ZassenhausSuzuki.Odd.q_structure
import Submission.Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki
import Submission.Work.ZassenhausSuzuki.Odd.OddFib
import Submission.Work.ZassenhausSuzuki.sqrt_orders
import Submission.Work.ZassenhausSuzuki.SzModelCoords
import Submission.Work.ZassenhausSuzuki.isSuzukiTwoGroup_of_mulEquiv
import Submission.Work.ZassenhausSuzuki.SzA.isSuzukiTwoGroup
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.isTitsTheta_titsTheta
import Submission.Work.ZassenhausSuzuki.odd_isStronglyReal
import Submission.Work.Models.Port.Sz.Simple
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.PSU3.BenderST.sz_standard_clause

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- The `Sz(2^(2n+1))` model satisfies the hypothesis bundle of the `Odd` theory
(`Work.ZassenhausSuzuki.Odd.SzOddHyp`): it is simple, `(szBorelS n, szTwoGroupS n, szWgM n)` is a
split rank-one Zassenhaus configuration, `szTwoGroupS n` is a non-abelian Suzuki `2`-group of
order `|Z|²`. -/
theorem sz_szOddHyp (n : ℕ) (hn : 1 ≤ n) :
    Work.ZassenhausSuzuki.Odd.SzOddHyp (Submission.Sz.szBorelS n)
      (Submission.Sz.szTwoGroupS n) (Submission.Sz.szWgM n) := by
  refine ⟨Submission.Sz.isSimpleGroup_SzModel n hn, Work.ZassenhausSuzuki.szSplitRankOne n hn,
    Work.ZassenhausSuzuki.szBorelS_isZassenhaus n hn, Submission.Sz.szTwoGroupS_isPGroup n,
    ?_, ?_, Work.PSU3.BenderST.sz_U_not_abelian n hn⟩
  · refine Work.ZassenhausSuzuki.isSuzukiTwoGroup_of_mulEquiv
      (Work.ZassenhausSuzuki.szAEquivSzTwoGroupS n).symm ?_
    exact Work.ZassenhausSuzuki.SzA.isSuzukiTwoGroup (Work.ZassenhausSuzuki.titsTheta n)
      (Work.ZassenhausSuzuki.titsTheta_ne_one n hn) (sz_titsTheta_orderOf_odd n)
  · rw [Submission.Sz.card_szTwoGroupS n, sz_center_szTwoGroupS_card n hn, ← pow_mul]
    congr 1
    ring

/-- **The centraliser of `u(0,c)·w` in `Sz(2^(2n+1))` has order at least `q + 1 - √(2q)`**,
`q = 2^(2n+1)`, `√(2q) = 2^(n+1)`.

`u(0,c)·w` (`c ≠ 0`) is a strongly real element which is not an involution, so its centraliser
belongs to the Bender–Suzuki family `ℱ = {C_G(x) : x strongly real, x ≠ 1, x² ≠ 1}`
(`sz_centralizer_mem_Vals`).  For the model `Sz(2^(2n+1))` the numerical endgame of
Suzuki 1962 §10 (`Work.ZassenhausSuzuki.Odd.endgame_classify`, applied to the hypothesis bundle
`sz_szOddHyp`) computes the set `Vals` of orders of the members of `ℱ` as
`{q - 1, q + 1 + 2^(n+1), q + 1 - 2^(n+1)}` (`Work.ZassenhausSuzuki.sqrt_orders`), whose minimum
is the advertised bound. -/
theorem sz_torus_centralizer_card_ge (n : ℕ) (hn : 1 ≤ n)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    2 ^ (2 * n + 1) + 1 - 2 ^ (n + 1) ≤
      Nat.card ↥(Subgroup.centralizer
        (singleton (Work.BSLit.BenderFacts2.szUgS n 0 c *
          Work.BSLit.BenderFacts2.szWgMS n) :
          Set (LeanEval.GroupTheory.Defs.SzModel n))) := by
  have h := sz_szOddHyp n hn
  have hmem := sz_centralizer_mem_Vals n hn hc
  -- The `BadOdd` elements are the odd-order elements that are not strongly real; by
  -- `odd_isStronglyReal` there are none, so the first counting relation loses its last term.
  have hBad : Nat.card {y : SzModel n // Work.ZassenhausSuzuki.Odd.BadOdd y} = 0 := by
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun y => y.2.2.2
      (Work.ZassenhausSuzuki.odd_isStronglyReal h.hG h.hsplit h.hzass h.h2 y.2.1 y.2.2.1)⟩
  have hq1 : 1 ≤ Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) := by
    have := (Work.ZassenhausSuzuki.Odd.q_structure h).2.2.1
    omega
  have hsum1 : ∑ x ∈ Work.ZassenhausSuzuki.Odd.Vals (SzModel n),
        (Work.ZassenhausSuzuki.Odd.mVal (SzModel n) x : ℚ) * ((x : ℚ) - 1)
      = (Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) ^ 2 *
          ((Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) - 1) *
          ((Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) ^ 2 + 1)
        - (Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) ^ 4 := by
    have h1 := Work.ZassenhausSuzuki.Odd.hsum1_rat h
    rw [hBad, Nat.cast_zero, sub_zero, Work.ZassenhausSuzuki.Odd.card_G_eq h] at h1
    have hcast : ((Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) ^ 2 *
        (Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) - 1) *
        (Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) ^ 2 + 1) : ℕ) : ℚ)
        = (Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) ^ 2 *
          ((Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) - 1) *
          ((Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) : ℚ) ^ 2 + 1) := by
      push_cast [Nat.cast_sub hq1]
      ring
    rw [h1, hcast]
  obtain ⟨-, a, b, hab_ne, hVeq, -, -, hsum, hprod⟩ :=
    Work.ZassenhausSuzuki.Odd.endgame_classify
      (q := Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n))
      (V := Work.ZassenhausSuzuki.Odd.Vals (SzModel n))
      (m := Work.ZassenhausSuzuki.Odd.mVal (SzModel n))
      (k := Work.ZassenhausSuzuki.Odd.kVal (SzModel n))
      hq1
      (fun x hx => Work.ZassenhausSuzuki.Odd.five_le_of_mem_Vals h hx)
      (fun x hx => Work.ZassenhausSuzuki.Odd.kVal_mem h hx)
      (fun x hx => by rw [Work.ZassenhausSuzuki.Odd.mVal_mul_kVal h hx,
        Work.ZassenhausSuzuki.Odd.card_G_eq h])
      hsum1
      (Work.ZassenhausSuzuki.Odd.hsum2_rat h)
      (Work.ZassenhausSuzuki.Odd.q_sub_one_mem_Vals h)
      (Work.ZassenhausSuzuki.Odd.kVal_q_sub_one h)
      (fun x hx hne => Work.ZassenhausSuzuki.Odd.coprime_of_mem_Vals h hx hne)
      (fun x hx hne y hy hye hxy => Work.ZassenhausSuzuki.Odd.coprime_pair_of_mem_Vals h hx hy hxy)
  -- `q = 2^(2n+1)`: `q - 1` is the order of the two-point stabiliser `B ⊓ B^w = T`.
  have hq : Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) = 2 ^ (2 * n + 1) := by
    have h1 := (Work.ZassenhausSuzuki.Odd.q_structure h).2.1
    have h2 : Submission.Blueprint.twoPoint (Submission.Sz.szBorelS n)
        (Submission.Sz.szWgM n) = Submission.Sz.szTS n :=
      Submission.Sz.szBorelS_inf_map_conj_eq n
    rw [h2] at h1
    rw [Work.Models.ModelData.card_szTS n] at h1
    have hA : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
    omega
  -- `a, b = q + 1 ± 2^(n+1)` by `sqrt_orders`.
  have hsum' : a + b = 2 * 2 ^ (2 * n + 1) + 2 := by
    rw [← hq]; exact hsum
  have hprod' : a * b = (2 ^ (2 * n + 1)) ^ 2 + 1 := by
    rw [← hq]; exact hprod
  have hoddm : Odd (2 * n + 1) := ⟨n, by ring⟩
  have hexp : (2 * n + 1 + 1) / 2 = n + 1 := by omega
  have hAn : 2 ≤ 2 ^ (n + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA2 : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  have hsqrt := Work.ZassenhausSuzuki.sqrt_orders (m := 2 * n + 1) (q := 2 ^ (2 * n + 1))
    (a := a) (b := b) hoddm rfl hsum' hprod'
  rw [hexp] at hsqrt
  have key : ∀ x : ℕ, x = Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) - 1 ∨ x = a ∨
      x = b → 2 ^ (2 * n + 1) + 1 - 2 ^ (n + 1) ≤ x := by
    intro x hx
    rcases hsqrt with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hx with hx | hx | hx <;> omega
    · rcases hx with hx | hx | hx <;> omega
  have h1 : Nat.card ↥(Subgroup.centralizer
      ({Work.BSLit.BenderFacts2.szUgS n 0 c * Work.BSLit.BenderFacts2.szWgMS n} :
        Set (LeanEval.GroupTheory.Defs.SzModel n)))
      ∈ ({Work.ZassenhausSuzuki.Odd.q (Submission.Sz.szBorelS n) - 1, a, b} : Finset ℕ) := by
    rw [← hVeq]
    exact hmem
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  exact key _ h1

end Work.BSLit.BenderFacts2
