import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

namespace Work.LinnikBurgess

open Classical

/-- `2 ^ (K-1) < 2 ^ K` for `K ≥ 1`. -/
lemma twoPowPred_lt (K : ℕ) (hK : 1 ≤ K) : 2 ^ (K - 1) < 2 ^ K := by
  have h := Nat.pow_lt_pow_succ (a := 2) (n := K - 1) (show 1 < 2 by norm_num)
  rwa [Nat.sub_add_cancel hK] at h

/-- `2 ^ (K-1) * 2 = 2 ^ K` for `K ≥ 1`. -/
lemma twoPowPred_mul_two (K : ℕ) (hK : 1 ≤ K) : 2 ^ (K - 1) * 2 = 2 ^ K := by
  rw [← pow_succ, Nat.sub_add_cancel hK]

/-- `2` divides `2 ^ K`. -/
lemma two_dvd_two_pow (K : ℕ) (hK : 1 ≤ K) : 2 ∣ 2 ^ K := by
  have h : 2 ^ 1 ∣ 2 ^ K := Nat.pow_dvd_pow 2 hK
  simpa using h

/-- For `K ≥ 1` and `v : ℕ`, `2 ^ (K-1) * v` reduces modulo `2 ^ K` to `2 ^ (K-1) * (v % 2)`. -/
lemma twoPowPred_mul_mod (K v : ℕ) (hK : 1 ≤ K) :
    2 ^ (K - 1) * v % 2 ^ K = 2 ^ (K - 1) * (v % 2) := by
  have hpk : 2 ^ (K - 1) * 2 = 2 ^ K := twoPowPred_mul_two K hK
  have hltK : 2 ^ (K - 1) < 2 ^ K := twoPowPred_lt K hK
  have hlt : 2 ^ (K - 1) * (v % 2) < 2 ^ K := by
    have h1 : v % 2 ≤ 1 := by have := Nat.mod_lt v (by norm_num : 0 < 2); omega
    calc 2 ^ (K - 1) * (v % 2) ≤ 2 ^ (K - 1) * 1 := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (K - 1) := mul_one _
      _ < 2 ^ K := hltK
  have hv : v = 2 * (v / 2) + v % 2 := by have := Nat.div_add_mod v 2; omega
  have hkey : 2 ^ (K - 1) * v = 2 ^ K * (v / 2) + 2 ^ (K - 1) * (v % 2) := by
    conv_lhs => rw [hv]
    rw [mul_add, ← mul_assoc, hpk]
  rw [hkey, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- `(2^(K-1) : ZMod (2^K)) * x` depends only on the parity of `x.val`. -/
lemma twoPowPred_mul_val (K : ℕ) (hK : 1 ≤ K) (x : ZMod (2 ^ K)) :
    ((2 ^ (K - 1) : ℕ) : ZMod (2 ^ K)) * x
      = ((2 ^ (K - 1) * (x.val % 2) : ℕ) : ZMod (2 ^ K)) := by
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num : (2 : ℕ) ≠ 0)⟩
  have hltK : 2 ^ (K - 1) < 2 ^ K := twoPowPred_lt K hK
  have hlt : 2 ^ (K - 1) * (x.val % 2) < 2 ^ K := by
    have h1 : x.val % 2 ≤ 1 := by have := Nat.mod_lt x.val (by norm_num : 0 < 2); omega
    calc 2 ^ (K - 1) * (x.val % 2) ≤ 2 ^ (K - 1) * 1 := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (K - 1) := mul_one _
      _ < 2 ^ K := hltK
  apply ZMod.val_injective
  simp only [ZMod.val_mul, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt hltK, twoPowPred_mul_mod K x.val hK, Nat.mod_eq_of_lt hlt]

/-- In `ZMod (2^K)`, `h ^ 2` and `h` have the same parity. -/
lemma val_sq_mod_two (K : ℕ) (hK : 1 ≤ K) (h : ZMod (2 ^ K)) :
    (h ^ 2).val % 2 = h.val % 2 := by
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num : (2 : ℕ) ≠ 0)⟩
  have hdvd : 2 ∣ 2 ^ K := two_dvd_two_pow K hK
  rw [pow_two, ZMod.val_mul, Nat.mod_mod_of_dvd (h.val * h.val) hdvd, Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one h.val with hh | hh <;> rw [hh] <;> norm_num

/-- `2 ^ (K-1) * h ^ 2 = 2 ^ (K-1) * h` in `ZMod (2^K)` for `K ≥ 1`. -/
lemma twoPowPred_mul_sq (K : ℕ) (hK : 1 ≤ K) (h : ZMod (2 ^ K)) :
    ((2 ^ (K - 1) : ℕ) : ZMod (2 ^ K)) * h ^ 2
      = ((2 ^ (K - 1) : ℕ) : ZMod (2 ^ K)) * h := by
  rw [twoPowPred_mul_val K hK (h ^ 2), twoPowPred_mul_val K hK h,
    val_sq_mod_two K hK h]

/-- Any `D` with `2 * D = 0` in `ZMod (2^K)` (`K ≥ 1`) satisfies `D * h ^ 2 = D * h`. -/
lemma mul_sq_eq_mul_of_two_mul_eq_zero (K : ℕ) (hK : 1 ≤ K) (D : ZMod (2 ^ K))
    (hD : 2 * D = 0) : ∀ h : ZMod (2 ^ K), D * h ^ 2 = D * h := by
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num : (2 : ℕ) ≠ 0)⟩
  have hcast : (2 : ZMod (2 ^ K)) * D = ((2 * D.val : ℕ) : ZMod (2 ^ K)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val D]
    push_cast
    ring
  have h0 : ((2 * D.val : ℕ) : ZMod (2 ^ K)) = 0 := by rw [← hcast]; exact hD
  have hmod : (2 * D.val) % 2 ^ K = 0 := by
    have h := (ZMod.val_eq_zero ((2 * D.val : ℕ) : ZMod (2 ^ K))).mpr h0
    rwa [ZMod.val_natCast] at h
  have hdvd : 2 ^ K ∣ 2 * D.val := Nat.dvd_of_mod_eq_zero hmod
  have hpk : 2 ^ K = 2 * 2 ^ (K - 1) := by
    rw [mul_comm, twoPowPred_mul_two K hK]
  have hdvd2 : 2 * 2 ^ (K - 1) ∣ 2 * D.val := by rw [← hpk]; exact hdvd
  have hdvd' : 2 ^ (K - 1) ∣ D.val :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 2) hdvd2
  have hDich : D.val = 0 ∨ D.val = 2 ^ (K - 1) := by
    obtain ⟨c, hc⟩ := hdvd'
    have hltX : 2 ^ (K - 1) * c < 2 ^ K := hc ▸ ZMod.val_lt D
    have hltY : 2 ^ (K - 1) * c < 2 ^ (K - 1) * 2 := by
      rw [twoPowPred_mul_two K hK]; exact hltX
    have hc2 : c < 2 := Nat.lt_of_mul_lt_mul_left hltY
    have hc01 : c = 0 ∨ c = 1 := by omega
    rcases hc01 with rfl | rfl
    · left; simpa using hc
    · right; simpa using hc
  have hDichZ : D = 0 ∨ D = ((2 ^ (K - 1) : ℕ) : ZMod (2 ^ K)) := by
    rcases hDich with h | h
    · left; exact (ZMod.val_eq_zero D).mp h
    · right
      apply ZMod.val_injective
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (twoPowPred_lt K hK)]
      exact h
  intro h
  rcases hDichZ with rfl | rfl
  · simp
  · exact twoPowPred_mul_sq K hK h

/-- In the "degenerate" case `g = K` of the 2-adic quadratic Gauss sum (`g` the capped valuation
of `2 ^ m * γ`), one has `2 ^ m * γ = 0` and therefore `2 ^ (m - 1) * γ` is annihilated by `2`,
which makes the squaring drop out: `(2 ^ (m - 1) * γ) * h ^ 2 = (2 ^ (m - 1) * γ) * h` for every
`h`. -/
theorem twoPow_g_eq_K {K m : ℕ} (hK : 1 ≤ K) (hm : 1 ≤ m) (hmK : m ≤ K)
    (γ : ZMod (2 ^ K)) (hg : m + vcap 2 (K - m) γ.val = K) :
    (((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ = 0)
      ∧ (∀ h : ZMod (2 ^ K),
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ * h ^ 2
            = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ * h) := by
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num : (2 : ℕ) ≠ 0)⟩
  have hdiv : 2 ^ K ∣ 2 ^ m * γ.val := by
    rcases eq_or_ne γ.val 0 with h0 | h0
    · rw [h0, mul_zero]; exact dvd_zero _
    · have hv : vcap 2 (K - m) γ.val = min (padicValNat 2 γ.val) (K - m) := by
        unfold vcap; rw [if_neg h0]
      have h1 : min (padicValNat 2 γ.val) (K - m) = K - m := by
        have h3 : m + min (padicValNat 2 γ.val) (K - m) = m + (K - m) := by
          rw [← hv, hg, Nat.add_sub_cancel' hmK]
        exact Nat.add_left_cancel h3
      have hle : K - m ≤ padicValNat 2 γ.val := by
        have h4 := Nat.min_le_left (padicValNat 2 γ.val) (K - m)
        rwa [h1] at h4
      have hgm : 2 ^ (K - m) ∣ γ.val := (padicValNat_dvd_iff_le h0).mpr hle
      have h5 : 2 ^ m * 2 ^ (K - m) ∣ 2 ^ m * γ.val := mul_dvd_mul_left _ hgm
      rwa [← pow_add, Nat.add_sub_cancel' hmK] at h5
  have hmain : ((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ = 0 := by
    have h4 : ((2 ^ m * γ.val : ℕ) : ZMod (2 ^ K)) = 0 := by
      rw [← ZMod.val_eq_zero, ZMod.val_natCast]
      exact Nat.mod_eq_zero_of_dvd hdiv
    calc ((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ
        = ((2 ^ m : ℕ) : ZMod (2 ^ K)) * ((γ.val : ℕ) : ZMod (2 ^ K)) := by
            rw [ZMod.natCast_zmod_val γ]
      _ = ((2 ^ m * γ.val : ℕ) : ZMod (2 ^ K)) := by push_cast; ring
      _ = 0 := h4
  refine ⟨hmain, ?_⟩
  intro h
  have hD : (2 : ZMod (2 ^ K)) * (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ) = 0 := by
    have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hm]
    calc (2 : ZMod (2 ^ K)) * (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ)
        = ((2 * 2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ := by push_cast; ring
      _ = ((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ := by rw [hpow]
      _ = 0 := hmain
  exact mul_sq_eq_mul_of_two_mul_eq_zero K hK _ hD h

end Work.LinnikBurgess
