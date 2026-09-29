import Mathlib
import Submission.Work.Params.nt1
import Submission.Work.Params.uparfacts
import Submission.Work.Params.basic
import Submission.Work.Params.defs
import Submission.Work.Params.CoprimeG1
import Submission.Work.Params.CoprimeG2D
import Submission.Work.Params.CoprimeCross

/-!
# §5.1: the `s_i` are pairwise coprime and odd

The list `ssPar n` of the paper's §5.1 has `d' = dpar n` entries `u₀ + F·i` (`1 ≤ i ≤ d'`) followed by
`d - d'` entries `2u₀ - 1 + 2F·j` (`1 ≤ j ≤ d - d'`), where `F = (d-1)!`, `u₀ = upar n = Q·(1 + mF)`
satisfies `u₀ ≡ 1 (mod F)`.

Main facts used:
* every `s` in the list is `≡ 1 [MOD F]`, hence coprime to `F`;
* every prime `≤ d - 1` divides `F` (`nt1`), so no `s` has a prime divisor `≤ d - 1`; and the
  difference of any two entries of the same family has size `< d`;
* the "cross" combination `2·(u₀ + F·i) - (2u₀ - 1 + 2F·j) = 1 + 2F(i - j)` is (up to sign) one of
  the factors `2Fk ± 1` of `Q`, so any common prime divisor of a cross pair divides `Q` and hence `u₀`.

The three coprimality cases are delegated to `CoprimeG1`, `CoprimeG2D`, `CoprimeCross`.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- The `k`-th element of `ssPar n`. -/
private def ssElt (n k : ℕ) : ℕ :=
  if k < dpar n then upar n + Ffac * (k + 1)
  else 2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1)

theorem ssPar_eq_map (n : ℕ) : ssPar n = (List.range D).map (ssElt n) := by unfold ssPar; rfl

theorem ss_upar_modEq_one (n : ℕ) : upar n ≡ 1 [MOD Ffac] := (uparfacts n).2.2.2.1

theorem ss_Lpar_pos (n : ℕ) : 0 < Lpar n := by
  unfold Lpar
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_left 1 _)

theorem ss_upar_pos (n : ℕ) : 0 < upar n := by
  have h := (uparfacts n).1
  have h1 : 0 < Lpar n := ss_Lpar_pos n
  omega

theorem ss_upar_odd (n : ℕ) : Odd (upar n) := by
  rw [Nat.odd_iff]
  have h : upar n ≡ 1 [MOD 2] := Nat.ModEq.of_dvd Ffac_two_dvd (ss_upar_modEq_one n)
  simpa [Nat.ModEq] using h

/-- `d' = dpar n ∈ [0, d)`. -/
theorem ss_dpar_lt_D (n : ℕ) : dpar n < D := by
  have hD : 0 < D := by decide
  have hdiv : D * ((kTpar n + D - 1) / D) ≤ kTpar n + D - 1 := Nat.mul_div_le _ _
  have hle : D * krpar n ≤ kTpar n + D - 1 := by simpa [krpar] using hdiv
  have hdef : dpar n = D * krpar n - kTpar n := rfl
  omega

theorem ssElt_odd (n k : ℕ) : Odd (ssElt n k) := by
  unfold ssElt
  split_ifs with h
  · have hu := ss_upar_odd n
    obtain ⟨t, ht⟩ := Ffac_two_dvd
    exact hu.add_even ⟨t * (k + 1), by rw [ht]; ring⟩
  · have hu1 : 1 ≤ upar n := ss_upar_pos n
    have hodd : Odd (2 * upar n - 1) := ⟨upar n - 1, by omega⟩
    exact hodd.add_even ⟨Ffac * (k - dpar n + 1), by ring⟩

theorem ssElt_modEq_one (n k : ℕ) : ssElt n k ≡ 1 [MOD Ffac] := by
  unfold ssElt
  split_ifs with h
  · have hu1 : 1 ≤ upar n := ss_upar_pos n
    have hdvd : Ffac ∣ upar n - 1 :=
      (Nat.modEq_iff_dvd' hu1).mp (ss_upar_modEq_one n).symm
    have h1le : 1 ≤ upar n + Ffac * (k + 1) := by
      have hz : 0 ≤ Ffac * (k + 1) := Nat.zero_le _
      omega
    refine ((Nat.modEq_iff_dvd' h1le).mpr ?_).symm
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t + (k + 1), ?_⟩
    have hx : upar n + Ffac * (k + 1) - 1 = (upar n - 1) + Ffac * (k + 1) := by omega
    rw [hx, ht]; ring
  · have hu1 : 1 ≤ upar n := ss_upar_pos n
    have hdvd : Ffac ∣ upar n - 1 :=
      (Nat.modEq_iff_dvd' hu1).mp (ss_upar_modEq_one n).symm
    have h1le : 1 ≤ 2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1) := by omega
    refine ((Nat.modEq_iff_dvd' h1le).mpr ?_).symm
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨2 * t + 2 * (k - dpar n + 1), ?_⟩
    have hx : 2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1) - 1
        = 2 * (upar n - 1) + 2 * Ffac * (k - dpar n + 1) := by omega
    rw [hx, ht]; ring

theorem sscoprime (n : ℕ) :
    (Work.Params.ssPar n).Pairwise Nat.Coprime ∧ (∀ s ∈ Work.Params.ssPar n, Odd s) := by
  have hd : dpar n < D := ss_dpar_lt_D n
  refine ⟨?_, ?_⟩
  · rw [ssPar_eq_map n, List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_range] at hi hj
    simp only [List.getElem_range]
    unfold ssElt
    by_cases hid : i < dpar n
    · by_cases hjd : j < dpar n
      · rw [if_pos hid, if_pos hjd]
        exact CoprimeG1 n (by omega) (by omega) (by omega)
      · rw [if_pos hid, if_neg hjd]
        exact CoprimeCross n (by omega) (by omega) (by omega) (by omega)
    · by_cases hjd : j < dpar n
      · exact absurd (lt_trans hij hjd) hid
      · rw [if_neg hid, if_neg hjd]
        exact CoprimeG2D n (by omega) (by omega) (by omega)
  · intro s hs
    rw [ssPar_eq_map n, List.mem_map] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ssElt_odd n k

end Work.Params
