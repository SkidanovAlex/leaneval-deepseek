import Mathlib
import Submission.Work.CORE2A.TorusDefs

/-!
# `c14_arith`: coprimality of the two numbers `mTor q`, `kTor q`

For odd `q` the two integers

* `mTor q = (q + ε)/2`, `kTor q = q - ε`,  where `ε = 1` if `q ≡ 1 (mod 4)` and `ε = -1`
  otherwise,

are coprime.  This is the arithmetic input of the `PGL₂(q)`-quotient analysis of pass 14
(`Thm26bTorusProp`): the torus of order `mTor (p^k)` meets the involution centralizer of order
`kTor (p^k)` trivially.

The proof is a case split on `q % 4`.  Since `q` is odd, `(q+1)/2` is odd when `q ≡ 1 (mod 4)`
and `(q-1)/2` is odd when `q ≡ 3 (mod 4)`; the remaining factor of the other number is the
predecessor (resp. successor) of that odd number, hence coprime to it.
-/

namespace Work.CORE2A

/-- Arithmetic core of the case `q ≡ 1 (mod 4)`:  `(q+1)/2` and `q - 1` are coprime. -/
lemma coprime_half_succ_sub_one (q : ℕ) (h4 : q % 4 = 1) :
    Nat.Coprime ((q + 1) / 2) (q - 1) := by
  -- `(q+1)/2` is odd, and `q - 1 = 2 * ((q+1)/2 - 1)`.
  have hodd : Odd ((q + 1) / 2) := by rw [Nat.odd_iff]; omega
  have hk : q - 1 = 2 * ((q + 1) / 2 - 1) := by omega
  have hconsec : Nat.Coprime ((q + 1) / 2) ((q + 1) / 2 - 1) :=
    (Nat.coprime_self_sub_right (m := 1) (by omega)).mpr (Nat.coprime_one_right _)
  have h := (Nat.coprime_two_right.mpr hodd).mul_right hconsec
  rwa [← hk] at h

/-- Arithmetic core of the case `q ≡ 3 (mod 4)`:  `(q-1)/2` and `q + 1` are coprime. -/
lemma coprime_half_pred_succ (q : ℕ) (h4 : q % 4 = 3) :
    Nat.Coprime ((q - 1) / 2) (q + 1) := by
  -- `(q-1)/2` is odd, and `q + 1 = 2 * ((q-1)/2 + 1)`.
  have hodd : Odd ((q - 1) / 2) := by rw [Nat.odd_iff]; omega
  have hk : q + 1 = 2 * ((q - 1) / 2 + 1) := by omega
  have hconsec : Nat.Coprime ((q - 1) / 2) ((q - 1) / 2 + 1) := by simp
  have h := (Nat.coprime_two_right.mpr hodd).mul_right hconsec
  rwa [← hk] at h

theorem c14_arith (q : ℕ) (hq : Odd q) : Nat.Coprime (Work.GW2.mTor q) (Work.GW2.kTor q) := by
  have h2 : q % 2 = 1 := Nat.odd_iff.mp hq
  have hcases : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases hcases with h4 | h4
  · have hm : Work.GW2.mTor q = (q + 1) / 2 := by rw [Work.GW2.mTor, h4]; simp
    have hk : Work.GW2.kTor q = q - 1 := by rw [Work.GW2.kTor, h4]; simp
    rw [hm, hk]
    exact coprime_half_succ_sub_one q h4
  · have hm : Work.GW2.mTor q = (q - 1) / 2 := by rw [Work.GW2.mTor, h4]; norm_num
    have hk : Work.GW2.kTor q = q + 1 := by rw [Work.GW2.kTor, h4]; norm_num
    rw [hm, hk]
    exact coprime_half_pred_succ q h4

end Work.CORE2A
