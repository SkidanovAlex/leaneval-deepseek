import Mathlib

namespace Work.DSTR.M110

theorem cardFixedZpowers {G : Type*} [CommGroup G] [Finite G] (z : G) {m e : ℕ}
    (hz : orderOf z = m) :
    Nat.card {x : G // x ∈ Subgroup.zpowers z ∧ x ^ e = 1} = m.gcd e := by
  have hmpos : 0 < m := by rw [← hz]; exact orderOf_pos z
  set d := m.gcd e with hd
  have hdvdm : d ∣ m := by rw [hd]; exact Nat.gcd_dvd_left m e
  have hdvde : d ∣ e := by rw [hd]; exact Nat.gcd_dvd_right m e
  have hdpos : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_left e hmpos
  set m' := m / d with hm'
  set e' := e / d with he'
  have hm_eq : d * m' = m := by rw [hm']; exact Nat.mul_div_cancel' hdvdm
  have he_eq : d * e' = e := by rw [he']; exact Nat.mul_div_cancel' hdvde
  have hm'pos : 0 < m' := by rw [hm']; exact Nat.div_pos (Nat.le_of_dvd hmpos hdvdm) hdpos
  have hm'_dvd_m : m' ∣ m := by rw [hm']; exact Nat.div_dvd_of_dvd hdvdm
  have hmd : m / m' = d := by
    rw [← hm_eq, mul_comm d m', Nat.mul_div_cancel_left d hm'pos]
  have hcop : m'.Coprime e' := by
    have h := Nat.coprime_div_gcd_div_gcd (m := m) (n := e) (Nat.gcd_pos_of_pos_left e hmpos)
    rw [← hd, ← hm', ← he'] at h
    exact h
  have hzpow_e : (z ^ m') ^ e = 1 := by
    have harith : m' * e = m * e' := by
      calc m' * e = m' * (d * e') := by rw [he_eq]
        _ = (m' * d) * e' := by rw [mul_assoc]
        _ = (d * m') * e' := by rw [mul_comm m' d]
        _ = m * e' := by rw [← hm_eq]
    rw [← pow_mul, harith, pow_mul, ← hz, pow_orderOf_eq_one, one_pow]
  have horder : orderOf (z ^ m') = d := by
    rw [orderOf_pow, hz, Nat.gcd_eq_right hm'_dvd_m, hmd]
  have hsub : {x : G | x ∈ Subgroup.zpowers z ∧ x ^ e = 1} ⊆ (Subgroup.zpowers (z ^ m') : Set G) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x z).mp (mem_powers_iff_mem_zpowers.mpr hx1)
    have hdvd : m ∣ n * e := by
      rw [← hz, orderOf_dvd_iff_pow_eq_one, pow_mul, hn, hx2]
    have h1 : d * m' ∣ n * e := by rw [hm_eq]; exact hdvd
    have h2 : d * (n * e') = n * e := by
      rw [mul_comm n e', ← mul_assoc, he_eq, mul_comm e n]
    rw [← h2] at h1
    have hdvd' : m' ∣ n * e' := Nat.dvd_of_mul_dvd_mul_left hdpos h1
    obtain ⟨t, ht⟩ := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd'
    rw [← hn, ht, pow_mul]
    exact Subgroup.npow_mem_zpowers (z ^ m') t
  have hsup : (Subgroup.zpowers (z ^ m') : Set G) ⊆ {x : G | x ∈ Subgroup.zpowers z ∧ x ^ e = 1} := by
    intro x hx
    have hx' : x ∈ Submonoid.powers (z ^ m') := mem_powers_iff_mem_zpowers.mpr hx
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x (z ^ m')).mp hx'
    refine ⟨?_, ?_⟩
    · rw [← hn]
      exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers z m') (Subgroup.npow_mem_zpowers (z ^ m') n)
    · rw [← hn, ← pow_mul, mul_comm n e, pow_mul, hzpow_e, one_pow]
  have hset : ({x : G | x ∈ Subgroup.zpowers z ∧ x ^ e = 1} : Set G) = (Subgroup.zpowers (z ^ m') : Set G) :=
    Set.Subset.antisymm hsub hsup
  have key : Nat.card {x : G // x ∈ Subgroup.zpowers z ∧ x ^ e = 1}
      = Nat.card (Subgroup.zpowers (z ^ m')) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      have h := Set.ext_iff.mp hset x
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe] at h
      exact h))
  rw [key, Nat.card_zpowers (z ^ m'), horder, hd]

end Work.DSTR.M110
