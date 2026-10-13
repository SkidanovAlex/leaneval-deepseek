import Mathlib

open Polynomial

namespace Work.WilC4aP

/-- For every multiset `s` and every `k ≤ s.card` there is a sub-multiset of `s`
of cardinality `k`. -/
lemma Multiset.exists_sub_le_card_eq {α : Type*} (s : Multiset α) {k : ℕ} (hk : k ≤ s.card) :
    ∃ t : Multiset α, t ≤ s ∧ t.card = k := by
  induction k generalizing s with
  | zero => exact ⟨0, Multiset.zero_le s, rfl⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (lt_of_lt_of_le (Nat.succ_pos k) hk)
    obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
    have hk' : k ≤ s'.card := by rw [Multiset.card_cons] at hk; omega
    obtain ⟨t, ht, htc⟩ := ih s' hk'
    exact ⟨a ::ₘ t, by simpa using ht, by simp [htc]⟩

/-- Every monic polynomial over `ℂ` has a monic divisor of any prescribed degree
not exceeding its own. -/
theorem exists_monic_factor_of_le {p : Polynomial ℂ} (hp : p.Monic) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree = k ∧ q ∣ p := by
  have hcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hk' : k ≤ p.roots.card := by simpa [hcard] using hk
  obtain ⟨t, ht, htc⟩ := Multiset.exists_sub_le_card_eq p.roots hk'
  refine ⟨(t.map (X - C ·)).prod, monic_multisetProd_X_sub_C t, ?_, ?_⟩
  · rw [natDegree_multiset_prod_X_sub_C_eq_card, htc]
  · rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp.ne_zero]
    exact ht

end Work.WilC4aP
