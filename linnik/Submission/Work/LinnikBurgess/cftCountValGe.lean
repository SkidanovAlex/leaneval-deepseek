import Mathlib

namespace Work.LinnikBurgess

/-- If `p ^ k` divides `t` and `t < p ^ M`, then `t / p ^ k < p ^ (M - k)`. -/
private lemma div_pow_lt {p M k t : ℕ} (hp : 2 ≤ p) (hdiv : p ^ k ∣ t) (ht : t < p ^ M) :
    t / p ^ k < p ^ (M - k) := by
  have hp1 : 1 < p := by omega
  have hts : p ^ k * (t / p ^ k) = t := Nat.mul_div_cancel' hdiv
  have hlt : p ^ k * (t / p ^ k) < p ^ M := by rw [hts]; exact ht
  rcases Nat.lt_or_ge M k with hkM | hkM
  · have hMk : M - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hkM)
    have hs0 : t / p ^ k = 0 := by
      by_contra hsne
      have hle : p ^ k ≤ p ^ k * (t / p ^ k) :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hsne)
      have hgt : p ^ M < p ^ k := pow_lt_pow_right₀ hp1 hkM
      exact absurd (le_trans hle (le_of_lt hlt)) (not_le.mpr hgt)
    rw [hMk, pow_zero, hs0]
    omega
  · have hpk : 0 < p ^ k := pow_pos (by omega) k
    have hpow : p ^ M = p ^ k * p ^ (M - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkM]
    rw [hpow] at hlt
    exact (Nat.mul_lt_mul_left hpk).mp hlt

/-- The number of `t < p ^ M` of `p`-adic valuation at least `k` is at most `p ^ (M - k)`. -/
lemma cftCountValGe {p M k : ℕ} (hp : 2 ≤ p) :
    ((Finset.range (p ^ M)).filter (fun t : ℕ => k ≤ padicValNat p t)).card ≤ p ^ (M - k) := by
  have hp1 : p ≠ 1 := by omega
  have hle := Finset.card_le_card_of_injOn
    (s := (Finset.range (p ^ M)).filter (fun t : ℕ => k ≤ padicValNat p t))
    (t := Finset.range (p ^ (M - k))) (fun t : ℕ => t / p ^ k) ?_ ?_
  · simpa using hle
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htM, htk⟩ := ht
    have hdiv : p ^ k ∣ t := (padicValNat_dvd_iff_of_ne_one hp1 k t).mpr (Or.inr htk)
    exact Finset.mem_range.mpr (div_pow_lt hp hdiv htM)
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    obtain ⟨_, hak⟩ := ha
    obtain ⟨_, hbk⟩ := hb
    have hab' : a / p ^ k = b / p ^ k := hab
    have hda : p ^ k ∣ a := (padicValNat_dvd_iff_of_ne_one hp1 k a).mpr (Or.inr hak)
    have hdb : p ^ k ∣ b := (padicValNat_dvd_iff_of_ne_one hp1 k b).mpr (Or.inr hbk)
    have h1 : p ^ k * (a / p ^ k) = a := Nat.mul_div_cancel' hda
    have h2 : p ^ k * (b / p ^ k) = b := Nat.mul_div_cancel' hdb
    rw [← h1, ← h2, hab']

end Work.LinnikBurgess
