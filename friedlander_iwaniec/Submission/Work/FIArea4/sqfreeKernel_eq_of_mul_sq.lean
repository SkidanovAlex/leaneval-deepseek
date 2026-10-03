import Mathlib
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel

namespace Work.FIArea4

/-- If `a, b ≥ 1` and `a * b` is a perfect square, then `a` and `b` have the same squarefree kernel
`Work.FIArea4.sqfreeKernel m = m / (sqPart m) ^ 2`.  Proof sketch: write `a = da * sa ^ 2` and
`b = db * sb ^ 2` with `da = sqfreeKernel a`, `db = sqfreeKernel b` squarefree and `sa = sqPart a`,
`sb = sqPart b` (from `Work.FIArea4.sqfree_kernel`); then `da * db * (sa * sb) ^ 2 = t ^ 2`, whence
`sa * sb ∣ t` and `da * db = u ^ 2`; since `da`, `db` are squarefree, `da ∣ u` and `db ∣ u`; writing
`u = da * v` gives `db = da * v ^ 2`, and `db ∣ u` forces `v ^ 2 ∣ v`, so `v = 1` and `da = db`.
Useful auxiliary fact: `k ^ 2 ∣ t ^ 2 → k ∣ t` (e.g. via `Nat.factorization_le_iff_dvd` and
`Nat.factorization_pow`). -/
theorem sqfreeKernel_eq_of_mul_sq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∃ t : ℕ, a * b = t ^ 2) :
    Work.FIArea4.sqfreeKernel a = Work.FIArea4.sqfreeKernel b := by
  obtain ⟨t, ht⟩ := h
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  obtain ⟨hPa, hmaxa, hsqma, hdvda, hsfa⟩ := sqfree_kernel a ha0
  obtain ⟨hPb, hmaxb, hsqmb, hdvdb, hsfb⟩ := sqfree_kernel b hb0
  set da := sqfreeKernel a with hda
  set db := sqfreeKernel b with hdb
  set sa := sqPart a with hsa
  set sb := sqPart b with hsb
  -- `hsqma : da * sa ^ 2 = a`, `hsqmb : db * sb ^ 2 = b`, with `da`, `db` squarefree.
  have hsa1 : 1 ≤ sa := by
    rcases Nat.eq_zero_or_pos sa with hs | hs
    · rw [hs] at hsqma; simp at hsqma; omega
    · exact hs
  have hsb1 : 1 ≤ sb := by
    rcases Nat.eq_zero_or_pos sb with hs | hs
    · rw [hs] at hsqmb; simp at hsqmb; omega
    · exact hs
  have hdapos : 0 < da := by
    rcases Nat.eq_zero_or_pos da with hd | hd
    · rw [hd] at hsqma; simp at hsqma; omega
    · exact hd
  have hdb1 : 1 ≤ db := by
    rcases Nat.eq_zero_or_pos db with hd | hd
    · rw [hd] at hsqmb; simp at hsqmb; omega
    · exact hd
  -- Key identity: `da * db * (sa * sb) ^ 2 = t ^ 2`.
  have hab : (da*sa^2)*(db*sb^2) = t^2 := by
    rw [hsqma, hsqmb]; exact ht
  have key : da * db * (sa * sb)^2 = t^2 := by
    rw [← hab]; ring
  -- `sa * sb ∣ t`, say `t = sa * sb * u`.
  have hk2 : (sa*sb)^2 ∣ t^2 := ⟨da*db, by rw [← key, mul_comm]⟩
  have hkd : sa*sb ∣ t := (Nat.pow_dvd_pow_iff (by norm_num : (2:ℕ) ≠ 0)).mp hk2
  obtain ⟨u, hu⟩ := hkd
  have hkpos : 0 < (sa*sb)^2 := by
    have h1 : 1 ≤ sa*sb := one_le_mul hsa1 hsb1
    positivity
  -- `da * db = u ^ 2`.
  have hh : da*db = u^2 := by
    have h1 : da*db*(sa*sb)^2 = u^2*(sa*sb)^2 := by rw [key, hu]; ring
    exact Nat.mul_right_cancel hkpos h1
  -- `da` and `db` are squarefree, hence radical: they divide `u ^ 2 = da * db`, so they divide `u`.
  have hda_u2 : da ∣ u^2 := by rw [← hh]; exact dvd_mul_right da db
  have hda_dvd_u : da ∣ u := (Squarefree.isRadical hsfa) 2 u hda_u2
  have hdb_u2 : db ∣ u^2 := by rw [← hh]; exact dvd_mul_left db da
  have hdb_dvd_u : db ∣ u := (Squarefree.isRadical hsfb) 2 u hdb_u2
  -- Write `u = da * v`, then `db = da * v ^ 2`.
  obtain ⟨v, hv⟩ := hda_dvd_u
  have hdb_eq : db = da * v^2 := by
    have h2 : da * db = da * (da * v^2) := by rw [hh, hv]; ring
    exact Nat.mul_left_cancel hdapos h2
  -- `db ∣ u` becomes `da * v ^ 2 ∣ da * v`, so `v ^ 2 ∣ v`, forcing `v = 1`.
  have hvdv : v^2 ∣ v := by
    have h3 : da * v^2 ∣ da * v := by
      rw [← hdb_eq, ← hv]; exact hdb_dvd_u
    exact (Nat.mul_dvd_mul_iff_left hdapos).mp h3
  have hv_eq : v = 1 := by
    rcases Nat.eq_zero_or_pos v with hv0 | hvpos
    · rw [hv0] at hdb_eq; simp at hdb_eq; omega
    · have hle : v^2 ≤ v := Nat.le_of_dvd hvpos hvdv
      nlinarith [hle, hvpos]
  simp [hv_eq] at hdb_eq
  exact hdb_eq.symm

end Work.FIArea4
