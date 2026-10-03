import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Evar_le_trivial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# At most seven moduli put a fixed pair of pairs in the same residue class

For a fixed pair of pairs `p ≠ q` of the box `[1,2R] × [1,2S]` with `β p ≠ 0 ≠ β q` — so by
`hcop` both `p` and `q` have coprime (in particular odd) first coordinates — the number of moduli
`d` in `(D, 2D]` such that some `a < d` satisfies
`s₁ ≡ r₁ a` and `s₂ ≡ r₂ a (mod d)` is at most `7`.

Indeed, such a `d` must divide the **nonzero** integer `n = q.1 * p.2 - p.1 * q.2`
(eliminate `a` using `gcd(rᵢ, d) = 1`).  Since `p ≠ q` together with coprimality forces `n ≠ 0`,
and `|n| ≤ (2R)(2S) + (2R)(2S) = 8RS < 8D`, the complementary divisor `|n|/d` is a positive
integer `< 4D/D = 4`, hence lies in `{1,…,7}` — and `d ↦ |n|/d` is injective.
-/

namespace Work.FIArea4.Vflip

open Finset

theorem Vcls_count_le_seven (R S D : ℕ) (β : ℕ → ℕ → ℂ) (p q : ℕ × ℕ)
    (hD : 1 ≤ D) (hRS : R * S < D)
    (hcop : ∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s))
    (hp : p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S))
    (hq : q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S))
    (hbp : β p.1 p.2 ≠ 0) (hbq : β q.1 q.2 ≠ 0) (hpq : p ≠ q) :
    ((Finset.Ioc D (2 * D)).filter
      (fun d => ∃ a ∈ Finset.range d,
        p ∈ Work.FIArea4.EvarCls R S d a ∧ q ∈ Work.FIArea4.EvarCls R S d a)).card ≤ 7 := by
  classical
  -- box bounds
  have hp1le : p.1 ≤ 2 * R := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
  have hp2le : p.2 ≤ 2 * S := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).2
  have hq1le : q.1 ≤ 2 * R := (Finset.mem_Icc.mp (Finset.mem_product.mp hq).1).2
  have hq2le : q.2 ≤ 2 * S := (Finset.mem_Icc.mp (Finset.mem_product.mp hq).2).2
  have hp1ge : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
  -- coprimality of the *first* coordinates with the second ones
  have hg1 : Nat.Coprime p.1 p.2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left p.2 2) (hcop p.1 p.2 hbp)
  have hg2 : Nat.Coprime q.1 q.2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left q.2 2) (hcop q.1 q.2 hbq)
  -- the integer difference whose divisors are the admissible moduli
  set n : ℤ := (q.1 : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (q.2 : ℤ) with hn
  have hnne : n ≠ 0 := by
    intro hz
    have hnat : q.1 * p.2 = p.1 * q.2 := by
      have h : (q.1 : ℤ) * (p.2 : ℤ) = (p.1 : ℤ) * (q.2 : ℤ) := by
        have : (q.1 : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (q.2 : ℤ) = 0 := hz
        linarith
      exact_mod_cast h
    have hdiv1 : p.1 ∣ q.1 := by
      apply hg1.dvd_of_dvd_mul_right
      rw [hnat]
      exact dvd_mul_right p.1 q.2
    have hdiv2 : q.1 ∣ p.1 := by
      apply hg2.dvd_of_dvd_mul_right
      rw [← hnat]
      exact dvd_mul_right q.1 p.2
    have h1e : p.1 = q.1 := Nat.dvd_antisymm hdiv1 hdiv2
    have h2e : p.2 = q.2 := by
      have hh : p.1 * p.2 = p.1 * q.2 := by
        calc p.1 * p.2 = q.1 * p.2 := by rw [h1e]
          _ = p.1 * q.2 := hnat
      exact Nat.mul_left_cancel (by omega) hh
    exact hpq (Prod.ext h1e h2e)
  set m : ℕ := n.natAbs with hm
  have hmpos : 0 < m := by rw [hm]; exact Int.natAbs_pos.mpr hnne
  -- the size bound `m ≤ 8 R S`
  have hbnd : m ≤ 8 * (R * S) := by
    have hA : ((q.1 : ℤ) * (p.2 : ℤ)).natAbs = q.1 * p.2 := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have hB : ((p.1 : ℤ) * (q.2 : ℤ)).natAbs = p.1 * q.2 := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have hpq1 : q.1 * p.2 ≤ 4 * (R * S) := by
      calc q.1 * p.2 ≤ (2 * R) * (2 * S) := Nat.mul_le_mul hq1le hp2le
        _ = 4 * (R * S) := by ring
    have hpq2 : p.1 * q.2 ≤ 4 * (R * S) := by
      calc p.1 * q.2 ≤ (2 * R) * (2 * S) := Nat.mul_le_mul hp1le hq2le
        _ = 4 * (R * S) := by ring
    rw [hm, hn]
    calc ((q.1 : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (q.2 : ℤ)).natAbs
        ≤ ((q.1 : ℤ) * (p.2 : ℤ)).natAbs + ((p.1 : ℤ) * (q.2 : ℤ)).natAbs :=
          Int.natAbs_sub_le _ _
      _ = q.1 * p.2 + p.1 * q.2 := by rw [hA, hB]
      _ ≤ 4 * (R * S) + 4 * (R * S) := Nat.add_le_add hpq1 hpq2
      _ = 8 * (R * S) := by ring
  have hmD : m < 8 * D :=
    lt_of_le_of_lt hbnd ((Nat.mul_lt_mul_left (by norm_num : 0 < 8)).mpr hRS)
  -- the set to be counted
  set T : Finset ℕ := (Finset.Ioc D (2 * D)).filter
      (fun d => ∃ a ∈ Finset.range d,
        p ∈ Work.FIArea4.EvarCls R S d a ∧ q ∈ Work.FIArea4.EvarCls R S d a) with hT
  change T.card ≤ 7
  -- every `d ∈ T` divides `m`, and `m / d ∈ {1,…,7}`
  have key : ∀ d ∈ T, d ∣ m ∧ m / d ∈ Finset.Icc 1 7 := by
    intro d hd
    rw [hT, Finset.mem_filter] at hd
    obtain ⟨hdIoc, a, ha, hpcls, hqcls⟩ := hd
    obtain ⟨hDd, hd2D⟩ := Finset.mem_Ioc.mp hdIoc
    have hdpos : 0 < d := by omega
    -- eliminate `a` mod `d`
    have hmod : Nat.ModEq d (q.1 * p.2) (p.1 * q.2) := by
      rw [Work.FIArea4.mem_EvarCls] at hpcls hqcls
      obtain ⟨-, -, hp2⟩ := hpcls
      obtain ⟨-, -, hq2⟩ := hqcls
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      push_cast
      rw [hp2, hq2]
      ring
    have hdvdm : d ∣ m := by
      have h1 : (d : ℤ) ∣ (p.1 * q.2 : ℤ) - (q.1 * p.2 : ℤ) := hmod.dvd
      have h2 : (p.1 * q.2 : ℤ) - (q.1 * p.2 : ℤ) = -n := by rw [hn]; ring
      rw [h2] at h1
      rw [hm]
      exact Int.natCast_dvd_natCast.mp ((Int.dvd_natAbs).mpr (dvd_neg.mp h1))
    refine ⟨hdvdm, ?_⟩
    obtain ⟨k, hk⟩ := hdvdm
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hp'
      · rw [hk, h0, Nat.mul_zero] at hmpos
        exact absurd hmpos (lt_irrefl 0)
      · exact hp'
    have hk7 : k ≤ 7 := by
      by_contra h
      have h8 : 8 ≤ k := by omega
      have h1 : (D + 1) * 8 ≤ m := by
        calc (D + 1) * 8 ≤ (D + 1) * k := Nat.mul_le_mul_left _ h8
          _ ≤ d * k := Nat.mul_le_mul_right _ (by omega)
          _ = m := hk.symm
      omega
    rw [show m / d = k by rw [hk, Nat.mul_div_right k hdpos]]
    exact Finset.mem_Icc.mpr ⟨hkpos, hk7⟩
  -- the counting map `d ↦ m / d` is injective into `{1,…,7}`
  have hmaps : Set.MapsTo (fun d => m / d) (↑T : Set ℕ) (↑(Finset.Icc 1 7) : Set ℕ) := by
    intro d hd
    exact (key d (by simpa using hd)).2
  have hinj : Set.InjOn (fun d => m / d) (↑T : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    change m / d1 = m / d2 at heq
    have hdvd1 : d1 ∣ m := (key d1 (by simpa using hd1)).1
    have hdvd2 : d2 ∣ m := (key d2 (by simpa using hd2)).1
    have hpos : 0 < m / d2 := by
      have := (key d2 (by simpa using hd2)).2
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp this).1
    have e1 : m / d2 * d1 = m := by
      rw [← heq]
      exact Nat.div_mul_cancel hdvd1
    have e2 : m / d2 * d2 = m := Nat.div_mul_cancel hdvd2
    exact Nat.mul_left_cancel hpos (by rw [e1, e2])
  have hcard : T.card ≤ (Finset.Icc 1 7 : Finset ℕ).card :=
    Finset.card_le_card_of_injOn (fun d => m / d) hmaps hinj
  rw [Nat.card_Icc] at hcard
  omega

end Work.FIArea4.Vflip
