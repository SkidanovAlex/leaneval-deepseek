import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

namespace Work.LinnikBurgess

/-- In the "non-degenerate" case `g < K` of the 2-adic quadratic Gauss sum (`g` the capped
valuation of `2 ^ m * γ`), both `2 ^ m * γ` and `2 ^ (m - 1) * γ` are a power of two times the
same unit of `ZMod (2 ^ K)`: the odd part of `γ.val`. -/
theorem twoPow_g_lt_K_unit {K m : ℕ} (hK : 1 ≤ K) (hm : 1 ≤ m) (hmK : m ≤ K)
    (γ : ZMod (2 ^ K))
    (hg : m + vcap 2 (K - m) γ.val < K) :
    ∃ u : (ZMod (2 ^ K))ˣ,
      (((2 ^ (m + vcap 2 (K - m) γ.val) : ℕ) : ZMod (2 ^ K)) * (u : ZMod (2 ^ K))
          = ((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ)
        ∧ (((2 ^ (m - 1 + vcap 2 (K - m) γ.val) : ℕ) : ZMod (2 ^ K)) * (u : ZMod (2 ^ K))
          = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ) := by
  -- `2 ^ K ≠ 0` so that `ZMod (2 ^ K)` is the ring with `val`-`natCast` round trip.
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num)⟩
  -- Work with `v = vcap 2 (K - m) γ.val` implicitly, keeping the definition folded.
  obtain ⟨v, hv⟩ : ∃ v : ℕ, v = vcap 2 (K - m) γ.val := ⟨_, rfl⟩
  have hg' : m + v < K := by rw [hv]; exact hg
  -- The valuation cap is not saturated, so `v = min (padicValNat 2 γ.val) (K - m)` is exact.
  have hvlt : v < K - m := by omega
  have hval0 : γ.val ≠ 0 := by
    intro h0
    have hv0 : v = K - m := by rw [hv]; unfold vcap; rw [if_pos h0]
    omega
  have hmin : v = min (padicValNat 2 γ.val) (K - m) := by
    rw [hv]; unfold vcap; rw [if_neg hval0]
  have hle : padicValNat 2 γ.val ≤ K - m := by
    by_contra h
    rw [min_eq_right (le_of_lt (not_le.mp h))] at hmin
    omega
  have hpadv : padicValNat 2 γ.val = v := by rw [hmin, min_eq_left hle]
  -- Factor `γ.val = 2 ^ v * w` with `w` the odd part.
  have hdvd : 2 ^ v ∣ γ.val := by
    have h := pow_padicValNat_dvd (p := 2) (n := γ.val)
    rwa [hpadv] at h
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = γ.val / 2 ^ v := ⟨_, rfl⟩
  have hmul : 2 ^ v * w = γ.val := by
    rw [hw]; exact Nat.mul_div_cancel' hdvd
  have hw0 : w ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact hval0 hmul.symm
  have hpadw : padicValNat 2 w = 0 := by
    have h := padicValNat.div_pow (p := 2) (b := γ.val) (a := v) hdvd
    rw [← hw] at h
    rw [hpadv, tsub_self] at h
    exact h
  have hodd : Odd w := by
    have hnd : ¬ 2 ∣ w := by
      rcases (padicValNat.eq_zero_iff (p := 2) (n := w)).mp hpadw with h | h | h
      · norm_num at h
      · exact absurd h hw0
      · exact h
    exact Nat.not_even_iff_odd.mp (fun he => hnd (even_iff_two_dvd.mp he))
  have hcop : Nat.Coprime w (2 ^ K) := Nat.Coprime.pow_right K hodd.coprime_two_right
  -- The unit is the odd part of `γ.val`; both statements are then pure integer arithmetic.
  rw [← hv]
  refine ⟨ZMod.unitOfCoprime w hcop, ?_, ?_⟩
  · have hnat1 : 2 ^ (m + v) * w = 2 ^ m * γ.val := by
      rw [pow_add, ← hmul]; ring
    rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val γ]
    rw [← Nat.cast_mul, ← Nat.cast_mul, hnat1]
  · have hnat2 : 2 ^ (m - 1 + v) * w = 2 ^ (m - 1) * γ.val := by
      rw [pow_add, ← hmul]; ring
    rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val γ]
    rw [← Nat.cast_mul, ← Nat.cast_mul, hnat2]

end Work.LinnikBurgess
