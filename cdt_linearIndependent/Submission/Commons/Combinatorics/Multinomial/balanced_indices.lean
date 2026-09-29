import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.Sym.Card
import Submission.Commons.Combinatorics.Multinomial.le_central
import Submission.Commons.Combinatorics.Multinomial.sum_multinomial_eq_pow
import Submission.Commons.Combinatorics.Multinomial.card_balanced_maps

set_option linter.style.haveILetI false

namespace Commons.Combinatorics.Multinomial

/-- The multinomial coefficient attached to a tuple concentrated on a single index equals `1`. -/
private lemma multinomial_concentrated (m d : ℕ) [NeZero m] :
    Nat.multinomial (Finset.univ : Finset (Fin m))
      (fun i : Fin m => if i = 0 then d else 0) = 1 := by
  rw [Nat.multinomial]
  have hsum : ∑ i : Fin m, (if i = 0 then d else 0) = d := by
    rw [Finset.sum_eq_single (0 : Fin m)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hprod : ∏ i : Fin m, (if i = 0 then d else 0).factorial = d.factorial := by
    rw [Finset.prod_eq_single (0 : Fin m)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, hprod, Nat.div_self (Nat.factorial_pos d)]

/-- The multinomial coefficient at the balanced tuple is at least `2`. -/
private lemma two_le_central (m d : ℕ) (hm : 2 ≤ m) (hmd : m ∣ d) (hd : 0 < d) :
    2 ≤ Nat.multinomial Finset.univ (fun _ : Fin m => d / m) := by
  haveI : NeZero m := ⟨by omega⟩
  set k := d / m with hk
  have hmul : m * k = d := by rw [hk]; exact Nat.mul_div_cancel' hmd
  have hkpos : 0 < k := by
    by_contra h
    simp only [not_lt] at h
    rw [Nat.le_zero] at h
    rw [h, mul_zero] at hmul
    omega
  have hklt : k < d := by nlinarith [hkpos, hm, hmul]
  have hsum : ∑ i ∈ Finset.univ.erase (0 : Fin m), k = (m - 1) * k := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hkd : k + ∑ i ∈ Finset.univ.erase (0 : Fin m), k = d := by
    rw [hsum]
    have hh : 1 + (m - 1) = m := by omega
    calc k + (m - 1) * k = 1 * k + (m - 1) * k := by rw [Nat.one_mul]
      _ = (1 + (m - 1)) * k := by rw [Nat.add_mul]
      _ = m * k := by rw [hh]
      _ = d := hmul
  have hM : Nat.multinomial Finset.univ (fun _ : Fin m => k) =
      (d.choose k) * Nat.multinomial (Finset.univ.erase (0 : Fin m)) (fun _ : Fin m => k) := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ (0 : Fin m))]
    rw [Nat.multinomial_insert (Finset.notMem_erase _ _)]
    rw [hkd]
  have hM' : 1 ≤ Nat.multinomial (Finset.univ.erase (0 : Fin m)) (fun _ : Fin m => k) :=
    Nat.multinomial_pos _ _
  have hchoose2 : 2 ≤ d.choose k := by
    have hpos : 0 < d.choose k := Nat.choose_pos (by omega)
    have hne : d.choose k ≠ 1 := by
      intro hc
      rw [Nat.choose_eq_one_iff] at hc
      omega
    omega
  rw [hM]
  exact le_trans hchoose2 (Nat.le_mul_of_pos_right _ hM')

theorem balanced_indices (m d : ℕ) (hm : 2 ≤ m) (hmd : m ∣ d) (hd : 0 < d) :
    m ^ d < Nat.multinomial Finset.univ (fun _ : Fin m => d / m) * Nat.choose (d + m - 1) (m - 1) := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fintype {P : Fin m → ℕ // ∑ i, P i = d} :=
    Fintype.ofEquiv (Sym (Fin m) d) (Sym.equivNatSumOfFintype (Fin m) d)
  -- sum identity
  have hS : m ^ d = ∑ P : {P : Fin m → ℕ // ∑ i, P i = d},
      Nat.multinomial (Finset.univ : Finset (Fin m)) (P : Fin m → ℕ) := by
    have h1 : m ^ d = ∑ k ∈ (Finset.univ : Finset (Fin m)).piAntidiag d,
        Nat.multinomial Finset.univ k := by
      have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin m)) (fun _ => (1:ℕ)) d
      simpa using h
    rw [h1]
    rw [Finset.sum_subtype (s := (Finset.univ : Finset (Fin m)).piAntidiag d)]
    · intro x
      rw [Finset.mem_piAntidiag]
      simp
  -- cardinality
  have hcard : Fintype.card {P : Fin m → ℕ // ∑ i, P i = d}
      = Nat.choose (d + m - 1) (m - 1) := by
    have h2 : Fintype.card {P : Fin m → ℕ // ∑ i, P i = d}
        = Fintype.card (Sym (Fin m) d) :=
      Fintype.card_congr (Sym.equivNatSumOfFintype (Fin m) d).symm
    rw [h2, Sym.card_sym_eq_choose]
    simp only [Fintype.card_fin]
    rw [Nat.add_comm m d]
    rw [Nat.choose_symm_of_eq_add (show d + m - 1 = d + (m - 1) by omega)]
  -- the strict sum comparison
  set P0 : Fin m → ℕ := fun i => if i = 0 then d else 0 with hP0
  have hP0mem : ∑ i, P0 i = d := by
    rw [hP0]
    rw [Finset.sum_eq_single (0 : Fin m)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP0val : Nat.multinomial (Finset.univ : Finset (Fin m)) P0 = 1 := by
    rw [hP0]
    exact multinomial_concentrated m d
  have hM2 : 2 ≤ Nat.multinomial Finset.univ (fun _ : Fin m => d / m) :=
    two_le_central m d hm hmd hd
  have hmain : (∑ P : {P : Fin m → ℕ // ∑ i, P i = d},
        Nat.multinomial (Finset.univ : Finset (Fin m)) (P : Fin m → ℕ))
      < ∑ _ : {P : Fin m → ℕ // ∑ i, P i = d},
        Nat.multinomial Finset.univ (fun _ : Fin m => d / m) := by
    refine Finset.sum_lt_sum (fun P _ => ?_) ⟨⟨P0, hP0mem⟩, Finset.mem_univ _, ?_⟩
    · exact le_central m d (by omega) hmd (P : Fin m → ℕ) P.2
    · show Nat.multinomial (Finset.univ : Finset (Fin m)) P0 < _
      rw [hP0val]
      exact lt_of_lt_of_le (by norm_num) hM2
  have hsumM : (∑ _ : {P : Fin m → ℕ // ∑ i, P i = d},
        Nat.multinomial Finset.univ (fun _ : Fin m => d / m))
      = Nat.multinomial Finset.univ (fun _ : Fin m => d / m) * Nat.choose (d + m - 1) (m - 1) := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, Nat.mul_comm]
  calc m ^ d = ∑ P : {P : Fin m → ℕ // ∑ i, P i = d},
        Nat.multinomial (Finset.univ : Finset (Fin m)) (P : Fin m → ℕ) := hS
    _ < ∑ _ : {P : Fin m → ℕ // ∑ i, P i = d},
        Nat.multinomial Finset.univ (fun _ : Fin m => d / m) := hmain
    _ = Nat.multinomial Finset.univ (fun _ : Fin m => d / m)
          * Nat.choose (d + m - 1) (m - 1) := hsumM

end Commons.Combinatorics.Multinomial