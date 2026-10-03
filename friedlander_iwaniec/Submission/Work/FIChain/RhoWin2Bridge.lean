/-
# `Submission.Work.FIChain.RhoWin2Bridge`

The `Π`-restricted bilinear form `BformPi` at the *integral* position `N` equals the aggregate of
the `Π`-restricted window sums `Xpg`:

  `BformPi x N C Pz = ∑_{m ≤ x} |Xpg x Pz m C N|`.

Both sides carry the same `m`-outer / `n`-inner structure; for each `m ≥ 1` the two inner sums
agree because

* the extra coprimality condition `(n,m) = 1` of `BformPi` may be dropped: if `(n,m) > 1` then a
  prime divides both `n` and `m`, so `m·n` is not squarefree and `ã(mn) = 0`;
* the index set `Icc 1 (2N)` of `BformPi` and `Icc 1 x` of `Xpg` agree on the common range
  `1 ≤ n ≤ 2N ≤ x`, and outside it both summands vanish.

Everything is definitions plus the two elementary arithmetic facts below (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary arithmetic: a common prime divisor kills `ã` -/

private lemma exists_prime_dvd_of_not_coprime {a b : ℕ} (h : ¬ Nat.Coprime a b) (ha : 0 < a) :
    ∃ p, Nat.Prime p ∧ p ∣ a ∧ p ∣ b := by
  have hg : a.gcd b ≠ 1 := fun h1 => h (Nat.coprime_iff_gcd_eq_one.mpr h1)
  have hg0 : a.gcd b ≠ 0 := by
    intro h0
    have hm0 : a = 0 := Nat.eq_zero_of_zero_dvd (by rw [← h0]; exact Nat.gcd_dvd_left a b)
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left a b), hpd.trans (Nat.gcd_dvd_right a b)⟩

private lemma not_squarefree_mul_of_prime_dvd {p a b : ℕ} (hp : p.Prime) (ha : p ∣ a)
    (hb : p ∣ b) (h : a * b ≠ 0) : ¬ Squarefree (a * b) := by
  intro hsq
  have h2 : p * p ∣ a * b := by
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' * b', by ring⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) h2

/-- If a prime divides both `n ≥ 1` and `m ≥ 1`, then `ã(mn) = 0` (the product is not
squarefree). -/
private lemma atilc_mul_zero_of_not_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : ¬ Nat.Coprime n m) : atilc (m * n) = 0 := by
  have hns : ¬ Squarefree (m * n) := by
    obtain ⟨p, hp, hpn, hpm⟩ := exists_prime_dvd_of_not_coprime h hn
    exact not_squarefree_mul_of_prime_dvd hp hpm hpn (Nat.mul_ne_zero (by omega) (by omega))
  exact Submission.ASP.atil_zero_of_not_squarefree (a := Submission.ASP.FIa) hns

/-! ## 2. The cast bookkeeping on the window top -/

private lemma cast_le_two_mul {n N : ℕ} : ((n : ℝ) ≤ 2 * (N : ℝ)) ↔ n ≤ 2 * N := by
  have h2 : (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
  rw [h2, Nat.cast_le]

/-! ## 3. The bridge -/

theorem RhoWin2Bridge (x Pz N : ℕ) (C : ℝ) (h2N : 2 * N ≤ x) :
    Work.FITop.BformPi x N C Pz = ∑ m ∈ Finset.Icc 1 x, |Xpg x Pz m C ((N : ℕ) : ℝ)| := by
  rw [Work.FITop.BformPi]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
  rw [Xpg, Finset.sum_filter]
  apply congrArg abs
  -- the two index sets coincide once `Icc 1 (2N)` is written as `Icc 1 x` filtered by `n ≤ 2N`
  have hIcc : Finset.Icc 1 (2 * N) = (Finset.Icc 1 x).filter (fun n => n ≤ 2 * N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 h2N⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  rw [hIcc, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  by_cases hn2N : n ≤ 2 * N
  · rw [if_pos hn2N]
    have hleR : ((n : ℝ) ≤ 2 * (N : ℝ)) := cast_le_two_mul.mpr hn2N
    by_cases hB : m * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧ N < n
    · have hAc : m * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧ (N : ℝ) < (n : ℝ) ∧
          (n : ℝ) ≤ 2 * (N : ℝ) :=
        ⟨hB.1, hB.2.1, by exact_mod_cast hB.2.2, hleR⟩
      rw [if_pos hAc]
      by_cases hcm : Nat.Coprime n m
      · rw [if_pos ⟨hB.2.2, hB.1, hcm, hB.2.1⟩]
      · rw [if_neg (fun h => hcm h.2.2.1)]
        rw [atilc_mul_zero_of_not_coprime hm0 hn0 hcm, mul_zero]
    · have hF : ¬ (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧
          (∀ q : ℕ, Nat.Prime q → q ≤ Pz → ¬ q ∣ n)) :=
        fun h => hB ⟨h.2.1, h.2.2.2, h.1⟩
      have hA : ¬ (m * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧ (N : ℝ) < (n : ℝ) ∧
          (n : ℝ) ≤ 2 * (N : ℝ)) :=
        fun h => hB ⟨h.1, h.2.1, Nat.cast_lt.mp h.2.2.1⟩
      rw [if_neg hF, if_neg hA]
  · rw [if_neg hn2N]
    rw [if_neg (fun h => hn2N (cast_le_two_mul.mp h.2.2.2))]

end

end Work.FIChain
