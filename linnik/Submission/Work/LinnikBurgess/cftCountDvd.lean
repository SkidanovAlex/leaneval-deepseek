import Mathlib

namespace Work.LinnikBurgess

lemma cftCountDvd {p M k : ℕ} (hp : 2 ≤ p) :
    ((Finset.range (p ^ M)).filter (fun t : ℕ => p ^ k ∣ t)).card ≤ p ^ (M - k) := by
  have hp0 : 0 < p := by omega
  have hpk : 0 < p ^ k := pow_pos hp0 k
  set s : Finset ℕ := (Finset.range (p ^ M)).filter (fun t : ℕ => p ^ k ∣ t) with hs
  have hkey : p ^ M ≤ p ^ (M - k) * p ^ k := by
    by_cases hkM : k ≤ M
    · rw [← pow_add, Nat.sub_add_cancel hkM]
    · have hMk : M ≤ k := by omega
      have h0 : M - k = 0 := by omega
      rw [h0, pow_zero, one_mul]
      exact Nat.pow_le_pow_right hp0 hMk
  have hinj : Set.InjOn (fun t => t / p ^ k) ↑s := by
    intro x hx y hy hxy
    have hxd : p ^ k ∣ x := (Finset.mem_filter.mp hx).2
    have hyd : p ^ k ∣ y := (Finset.mem_filter.mp hy).2
    have hxy' : x / p ^ k = y / p ^ k := hxy
    rw [← Nat.div_mul_cancel hxd, ← Nat.div_mul_cancel hyd, hxy']
  have hsub : s.image (fun t => t / p ^ k) ⊆ Finset.range (p ^ (M - k)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
    have ht_lt : t < p ^ M := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have htd : p ^ k ∣ t := (Finset.mem_filter.mp ht).2
    simp only [Finset.mem_range]
    have h1 : t / p ^ k * p ^ k < p ^ (M - k) * p ^ k := by
      rw [Nat.div_mul_cancel htd]
      exact lt_of_lt_of_le ht_lt hkey
    exact (Nat.mul_lt_mul_right hpk).mp h1
  calc s.card = (s.image (fun t => t / p ^ k)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (p ^ (M - k))).card := Finset.card_le_card hsub
    _ = p ^ (M - k) := Finset.card_range _

end Work.LinnikBurgess
