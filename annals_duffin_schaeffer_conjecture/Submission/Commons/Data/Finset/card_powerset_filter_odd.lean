import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum.Eq

namespace Commons.Data.Finset

/-- The number of odd-cardinality subsets of a nonempty finite set `s` is
`2 ^ (s.card - 1)`. -/
theorem card_powerset_filter_odd {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s ≠ ∅) :
    (s.powerset.filter (fun t : Finset α => Odd t.card)).card = 2 ^ (s.card - 1) := by
  classical
  -- Pick a distinguished element of s.
  obtain ⟨a, ha⟩ := (Finset.nonempty_iff_ne_empty.mpr hs : s.Nonempty)
  -- The "toggle" map: adjoin or remove `a`, which flips the parity of the cardinality.
  let f : Finset α → Finset α := fun t => if a ∈ t then t.erase a else insert a t
  let oddP : Finset (Finset α) := s.powerset.filter (fun t : Finset α => Odd t.card)
  let evenP : Finset (Finset α) := s.powerset.filter (fun t : Finset α => Even t.card)
  -- f is an involution.
  have hf_invol : Function.Involutive f := by
    intro t
    by_cases hat : a ∈ t
    · have hf : f t = t.erase a := by simp [f, hat]
      have hnot : a ∉ t.erase a := by simp [hat]
      calc
        f (f t) = f (t.erase a) := by rw [hf]
        _ = insert a (t.erase a) := by simp [f, hnot]
        _ = t := Finset.insert_erase hat
    · have hf : f t = insert a t := by simp [f, hat]
      have hm : a ∈ insert a t := by simp
      calc
        f (f t) = f (insert a t) := by rw [hf]
        _ = (insert a t).erase a := by simp [f, hm]
        _ = t := Finset.erase_insert hat
  -- f maps subsets of s to subsets of s.
  have hf_pow : ∀ t : Finset α, t ∈ s.powerset → f t ∈ s.powerset := by
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    apply Finset.mem_powerset.mpr
    by_cases hat : a ∈ t
    · calc
        f t = t.erase a := by simp [f, hat]
        _ ⊆ t := Finset.erase_subset a t
        _ ⊆ s := hts
    · calc
        f t = insert a t := by simp [f, hat]
        _ ⊆ s := Finset.insert_subset ha hts
  -- f flips parity: Odd t.card ↔ Even (f t).card.
  have hflip : ∀ t : Finset α, Odd t.card ↔ Even (f t).card := by
    intro t
    by_cases hat : a ∈ t
    · -- f t = t.erase a, so (f t).card + 1 = t.card
      have hft : f t = t.erase a := by simp [f, hat]
      have hc : (f t).card + 1 = t.card := by
        rw [hft]
        exact Finset.card_erase_add_one hat
      constructor
      · intro hodd
        -- Odd t.card, t.card = (f t).card + 1  ⟹  ¬ Odd (f t).card  ⟹  Even (f t).card
        rw [← hc] at hodd
        exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd)
      · intro hev
        rw [← hc]
        exact Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr hev)
    · -- f t = insert a t, so (f t).card = t.card + 1
      have hft : f t = insert a t := by simp [f, hat]
      have hc : (f t).card = t.card + 1 := by
        rw [hft]
        exact Finset.card_insert_of_notMem hat
      constructor
      · intro hodd
        rw [hc]
        exact Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)
      · intro hev
        rw [hc] at hev
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev)
  -- The converse flip: Even t.card → Odd (f t).card (by involution).
  have hflip' : ∀ t : Finset α, Even t.card → Odd (f t).card := by
    intro t het
    have h := hflip (f t)
    rw [hf_invol t] at h
    exact h.mpr het
  -- f gives a bijection between the odd- and the even-cardinality subsets of s.
  have hcard_eq : oddP.card = evenP.card := by
    refine Finset.card_nbij' f f ?_ ?_ ?_ ?_
    · intro t ht
      change t ∈ oddP at ht
      have ht' := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨hf_pow t ht'.1, (hflip t).mp ht'.2⟩
    · intro t ht
      change t ∈ evenP at ht
      have ht' := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨hf_pow t ht'.1, hflip' t ht'.2⟩
    · intro t ht
      change t ∈ oddP at ht
      exact hf_invol t
    · intro t ht
      change t ∈ evenP at ht
      exact hf_invol t
  -- Total count: odd + even = powerset.
  have hsplit : oddP.card + evenP.card = s.powerset.card := by
    have h := Finset.card_filter_add_card_filter_not (s := s.powerset)
      (p := fun t : Finset α => Odd t.card)
    have heven_un : (s.powerset.filter (fun t : Finset α => ¬ Odd t.card)) = evenP := by
      unfold evenP
      apply Finset.filter_congr
      intro t ht
      simp [Nat.not_odd_iff_even]
    rw [heven_un] at h
    simpa [oddP] using h
  -- Thus 2 * odd = 2 ^ (s.card - 1).
  have htotal : 2 * oddP.card = 2 ^ s.card := by
    calc
      2 * oddP.card = oddP.card + oddP.card := two_mul oddP.card
      _ = oddP.card + evenP.card := by rw [hcard_eq]
      _ = s.powerset.card := hsplit
      _ = 2 ^ s.card := Finset.card_powerset s
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hs1 : 1 ≤ s.card := by omega
  have hpow : 2 ^ s.card = 2 * 2 ^ (s.card - 1) := by
    calc
      2 ^ s.card = 2 ^ ((s.card - 1) + 1) := by congr 1; exact (Nat.sub_add_cancel hs1).symm
      _ = 2 ^ (s.card - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (s.card - 1) := by rw [mul_comm]
  have hprod : 2 * oddP.card = 2 * 2 ^ (s.card - 1) := by
    rw [htotal, hpow]
  simpa [oddP] using (mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hprod)

end Commons.Data.Finset