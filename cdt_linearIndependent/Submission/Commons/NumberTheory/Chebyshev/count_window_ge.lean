import Mathlib

namespace Commons.NumberTheory.Chebyshev

theorem count_window_ge (n k l p : ℕ) (hM : 0 < max k l)
    (hp : p.Prime) (hpn : p ≤ n) (hlp : l < p) :
    ((Finset.Icc 1 ((n - k - 1) / max k l)).filter
        (fun a => p * a ≤ n - k - 1 ∧ n < p * (a + 1))).card
      = if (¬ ∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m) then 1 else 0 := by
  have hp0 : 0 < p := hp.pos
  set T : ℕ := n - k - 1 with hT
  set M : ℕ := max k l with hMdef
  have hM0 : 0 < M := by rw [hMdef]; exact hM
  -- Uniqueness: any index satisfying the two window inequalities equals T / p.
  have uniq : ∀ a : ℕ, p * a ≤ T → n < p * (a + 1) → a = T / p := by
    intro a ha hn
    have hle : a ≤ T / p := by
      rw [Nat.le_div_iff_mul_le hp0]
      rwa [Nat.mul_comm]
    have hge : T / p ≤ a := by
      by_contra h
      rw [Nat.not_le] at h
      have h1 : a + 1 ≤ T / p := Nat.succ_le_of_lt h
      have h2 : p * (a + 1) ≤ p * (T / p) := Nat.mul_le_mul_left p h1
      have h3 : p * (T / p) ≤ T := Nat.mul_div_le T p
      have h4 : T ≤ n := by omega
      have h5 : p * (a + 1) ≤ n := le_trans (le_trans h2 h3) h4
      exact absurd (lt_of_lt_of_le hn h5) (lt_irrefl n)
    omega
  -- Key equivalence.
  have hkey : n < p * (T / p + 1) ↔ ¬ ∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m := by
    constructor
    · rintro hlt ⟨m, hm, hdvd⟩
      rw [Finset.mem_erase, Finset.mem_Icc] at hm
      obtain ⟨hmne, hmlo, hmhi⟩ := hm
      have hTm : T < m := by omega
      have hpm : p * (T / p) < m := lt_of_le_of_lt (Nat.mul_div_le T p) hTm
      have hdvd' : p ∣ m - p * (T / p) := Nat.dvd_sub hdvd (dvd_mul_right p (T / p))
      have hpos : 0 < m - p * (T / p) := Nat.sub_pos_of_lt hpm
      have hle : p ≤ m - p * (T / p) := Nat.le_of_dvd hpos hdvd'
      have hge : p * (T / p + 1) ≤ m := by
        have heq : p * (T / p + 1) = p * (T / p) + p := by ring
        omega
      have : p * (T / p + 1) ≤ n := le_trans hge hmhi
      exact absurd (lt_of_lt_of_le hlt this) (lt_irrefl n)
    · intro hno
      by_contra hge
      simp only [not_lt] at hge
      refine hno ⟨p * (T / p + 1), ?_, dvd_mul_right p (T / p + 1)⟩
      rw [Finset.mem_erase, Finset.mem_Icc]
      have hlt : T < p * (T / p + 1) := Nat.lt_mul_div_succ T hp0
      refine ⟨?_, ?_, hge⟩
      · have : 0 < p * (T / p + 1) := by positivity
        omega
      · omega
  -- Membership when the inequality holds.
  have hmem_fun : n < p * (T / p + 1) →
      T / p ∈ (Finset.Icc 1 (T / M)).filter (fun a => p * a ≤ T ∧ n < p * (a + 1)) := by
    intro hlt
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.mul_div_le T p, hlt⟩
    · have hpT : p ≤ T := by
        by_contra h
        have hltp : T < p := Nat.not_le.mp h
        have hz : T / p = 0 := Nat.div_eq_of_lt hltp
        rw [hz, zero_add, Nat.mul_one] at hlt
        omega
      rw [Nat.le_div_iff_mul_le hp0]
      simpa using hpT
    · have hkp : k < p := by
        by_contra h
        have hpk : p ≤ k := Nat.not_lt.mp h
        have hTp : T + p ≤ n := by omega
        have hpdiv : p * (T / p) ≤ T := Nat.mul_div_le T p
        have hmul : p * (T / p + 1) = p * (T / p) + p := by ring
        have : p * (T / p + 1) ≤ T + p := by omega
        omega
      have hMle : M ≤ p - 1 := by
        have hk : k ≤ p - 1 := by omega
        have hl : l ≤ p - 1 := by omega
        rw [hMdef]; exact max_le hk hl
      have hMmul : M * (T / p) ≤ T := by
        have h1 : M * (T / p) ≤ (p - 1) * (T / p) := Nat.mul_le_mul_right _ hMle
        have h2 : (p - 1) * (T / p) ≤ p * (T / p) := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
        have h3 : p * (T / p) ≤ T := Nat.mul_div_le T p
        exact le_trans h1 (le_trans h2 h3)
      rw [Nat.le_div_iff_mul_le hM0]
      rw [Nat.mul_comm]
      exact hMmul
  have hFcard :
      ((Finset.Icc 1 (T / M)).filter (fun a => p * a ≤ T ∧ n < p * (a + 1))).card
        = if n < p * (T / p + 1) then 1 else 0 := by
    have hsub : ((Finset.Icc 1 (T / M)).filter
        (fun a => p * a ≤ T ∧ n < p * (a + 1))) ⊆ {T / p} := by
      intro a ha
      rw [Finset.mem_singleton]
      rw [Finset.mem_filter] at ha
      exact uniq a ha.2.1 ha.2.2
    by_cases hlt : n < p * (T / p + 1)
    · have hmem : T / p ∈ (Finset.Icc 1 (T / M)).filter
          (fun a => p * a ≤ T ∧ n < p * (a + 1)) := hmem_fun hlt
      have heq : (Finset.Icc 1 (T / M)).filter
          (fun a => p * a ≤ T ∧ n < p * (a + 1)) = {T / p} :=
        Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
      rw [heq, Finset.card_singleton, if_pos hlt]
    · have hnotmem : T / p ∉ (Finset.Icc 1 (T / M)).filter
          (fun a => p * a ≤ T ∧ n < p * (a + 1)) := by
        intro hc
        rw [Finset.mem_filter] at hc
        exact hlt hc.2.2
      have hsub' : ((Finset.Icc 1 (T / M)).filter
          (fun a => p * a ≤ T ∧ n < p * (a + 1))) ⊆ ∅ := by
        intro a ha
        have h1 := hsub ha
        rw [Finset.mem_singleton] at h1
        rw [h1] at ha
        exact False.elim (hnotmem ha)
      have heq : (Finset.Icc 1 (T / M)).filter
          (fun a => p * a ≤ T ∧ n < p * (a + 1)) = ∅ :=
        Finset.Subset.antisymm hsub' (Finset.empty_subset _)
      rw [heq, Finset.card_empty, if_neg hlt]
  rw [hFcard]
  by_cases hC : ¬ ∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m
  · rw [if_pos (hkey.mpr hC), if_pos hC]
  · rw [if_neg (fun hc => hC (hkey.mp hc)), if_neg hC]

end Commons.NumberTheory.Chebyshev
