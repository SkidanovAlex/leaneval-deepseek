import Mathlib.Data.ZMod.Basic

namespace Commons.Data.ZMod

open Nat

private theorem val_even_sub_iff_of_even {n : ℕ} [NeZero n] (a b : ZMod n) (hn : Even n) :
    Even ((a - b).val) ↔ (Even a.val ↔ Even b.val) := by
  by_cases hba : b.val ≤ a.val
  · rw [ZMod.val_sub hba]
    exact Nat.even_sub hba
  · have hab : a.val < b.val := lt_of_not_ge hba
    have hle : a.val ≤ b.val := le_of_lt hab
    have hsub : (b - a).val = b.val - a.val := ZMod.val_sub hle
    have hvalne : (b - a).val ≠ 0 := by
      rw [hsub]
      omega
    have hbne : b - a ≠ 0 := (ZMod.val_ne_zero (b - a)).mp hvalne
    have hnegval : (a - b).val = n - (b - a).val := by
      have hmn : a - b = -(b - a) := by
        rw [neg_sub]
      rw [hmn, ZMod.neg_val (b - a), if_neg hbne]
    rw [hnegval]
    have hleba : (b - a).val ≤ n := (ZMod.val_lt (b - a)).le
    have hstep1 : Even (n - (b - a).val) ↔ Even (b - a).val := by
      have h := Nat.even_sub hleba
      rw [h]
      constructor
      · intro hif
        exact hif.1 hn
      · intro hk
        exact ⟨fun _ => hk, fun _ => hn⟩
    rw [hstep1, hsub]
    calc
      Even (b.val - a.val) ↔ (Even b.val ↔ Even a.val) := Nat.even_sub hle
      _ ↔ (Even a.val ↔ Even b.val) := Iff.comm

/-- In `ZMod (2^t)` the difference `a - b` has an even canonical representative
iff `a` and `b` have representatives of the same parity. -/
theorem val_even_sub_iff {t : ℕ} (a b : ZMod (2 ^ t)) :
    Even ((a - b).val) ↔ (Even a.val ↔ Even b.val) := by
  by_cases ht : t = 0
  · subst t
    have hva : a.val = 0 := by
      have hlt : a.val < 1 := by simpa using (ZMod.val_lt a)
      omega
    have hvb : b.val = 0 := by
      have hlt : b.val < 1 := by simpa using (ZMod.val_lt b)
      omega
    have hvd : (a - b).val = 0 := by
      have hlt : (a - b).val < 1 := by simpa using (ZMod.val_lt (a - b))
      omega
    simp [hva, hvb, hvd]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have h2 : Even (2 ^ t) := by
      refine even_iff_two_dvd.mpr ?_
      have hpow : 2 ^ 1 ∣ 2 ^ t := pow_dvd_pow 2 htpos
      simpa using hpow
    exact val_even_sub_iff_of_even (n := 2 ^ t) a b h2

end Commons.Data.ZMod