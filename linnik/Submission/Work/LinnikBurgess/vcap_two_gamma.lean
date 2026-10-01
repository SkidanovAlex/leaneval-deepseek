import Mathlib
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikBurgess.padicValNat_pow_sub_mod

namespace Work.LinnikBurgess

/-- Arithmetic identification of the two capping parameters.  With `δ ∈ [0, p^e)`, `K = e - m`,
`δ' = δ mod p^K` and `γ = -(1/2) p^m δ' ∈ ZMod (p^K)`, one has
`vcap p K (2γ).val = m + vcap p (e - 2m) δ`.  Both sides equal `min(m + v_p(δ), e - m)`
(or `e - m` when `p^(e-m) ∣ δ`). -/
theorem vcap_two_gamma {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h2m : 2 * m ≤ e) (δ : ℕ) (hδ : δ < p ^ e) :
    vcap p (e - m) (2 * (-(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
        * ((δ : ℕ) : ZMod (p ^ (e - m))))).val = m + vcap p (e - 2 * m) δ := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hK : e - m = m + (e - 2 * m) := by omega
  haveI hNe : NeZero (p ^ (e - m)) := ⟨pow_ne_zero _ hp0⟩
  -- `2` is invertible modulo the odd number `p^(e-m)`
  have h2inv : (2 : ZMod (p ^ (e - m))) * (2 : ZMod (p ^ (e - m)))⁻¹ = 1 := by
    have hodd : Odd (p ^ (e - m)) := (hp.odd_of_ne_two hp2).pow
    have hcop : Nat.Coprime 2 (p ^ (e - m)) := Nat.coprime_two_left.mpr hodd
    simpa using ZMod.coe_mul_inv_eq_one 2 hcop
  -- identify the argument of `.val` with `-(p^m δ)`
  have hx : 2 * (-(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
        * ((δ : ℕ) : ZMod (p ^ (e - m))))
      = -(((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m))) := by
    have hcast : ((p ^ m * δ : ℕ) : ZMod (p ^ (e - m)))
        = ((p ^ m : ℕ) : ZMod (p ^ (e - m))) * ((δ : ℕ) : ZMod (p ^ (e - m))) := by
      rw [Nat.cast_mul]
    rw [hcast]
    calc 2 * (-(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
            * ((δ : ℕ) : ZMod (p ^ (e - m))))
        = -((2 : ZMod (p ^ (e - m))) * (2 : ZMod (p ^ (e - m)))⁻¹
            * ((p ^ m : ℕ) : ZMod (p ^ (e - m))) * ((δ : ℕ) : ZMod (p ^ (e - m)))) := by ring
      _ = -(1 * ((p ^ m : ℕ) : ZMod (p ^ (e - m))) * ((δ : ℕ) : ZMod (p ^ (e - m)))) := by
            rw [h2inv]
      _ = -(((p ^ m : ℕ) : ZMod (p ^ (e - m))) * ((δ : ℕ) : ZMod (p ^ (e - m)))) := by ring
  rw [hx]
  by_cases hTdvd : p ^ (e - 2 * m) ∣ δ
  · -- Case A: `p^(e-2m) | δ`, so the argument is `0` and both sides are `e - m`
    have hKdvd : p ^ (e - m) ∣ p ^ m * δ := by
      rw [hK, pow_add]
      exact mul_dvd_mul_left (p ^ m) hTdvd
    have hzero : (((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m))) = 0 :=
      (ZMod.natCast_eq_zero_iff (p ^ m * δ) (p ^ (e - m))).mpr hKdvd
    have hxv : (-(((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m)))).val = 0 := by
      rw [hzero]; simp
    have hL : vcap p (e - m) ((-(((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m)))).val) = e - m := by
      rw [hxv]; unfold vcap; rw [if_pos rfl]
    have hR : vcap p (e - 2 * m) δ = e - 2 * m := by
      rcases eq_or_ne δ 0 with h | h
      · subst h; unfold vcap; rw [if_pos rfl]
      · unfold vcap; rw [if_neg h]
        exact Nat.min_eq_right ((padicValNat_dvd_iff_le h).mp hTdvd)
    rw [hL, hR]
    omega
  · -- Case B: `p^(e-2m) ∤ δ`
    have hδ0 : δ ≠ 0 := by
      intro h; exact hTdvd (by rw [h]; exact dvd_zero _)
    have hvδ : padicValNat p δ < e - 2 * m := by
      by_contra hc
      have hc' : e - 2 * m ≤ padicValNat p δ := by omega
      exact hTdvd ((padicValNat_dvd_iff_le hδ0).mpr hc')
    have ha_ne : p ^ m * δ ≠ 0 := mul_ne_zero (pow_ne_zero m hp0) hδ0
    have hvpa : padicValNat p (p ^ m * δ) = m + padicValNat p δ := by
      rw [padicValNat.mul (pow_ne_zero m hp0) hδ0, padicValNat.prime_pow]
    have hvltK : padicValNat p (p ^ m * δ) < e - m := by
      rw [hvpa]; omega
    have hmv : m + padicValNat p δ < e - m := by rw [← hvpa]; exact hvltK
    have hAne : (((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m))) ≠ 0 := by
      intro hc
      have hdvd : p ^ (e - m) ∣ p ^ m * δ :=
        (ZMod.natCast_eq_zero_iff (p ^ m * δ) (p ^ (e - m))).mp hc
      have := (padicValNat_dvd_iff_le ha_ne).mp hdvd
      omega
    have hxv : (-(((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m)))).val
        = p ^ (e - m) - p ^ m * δ % p ^ (e - m) := by
      haveI : NeZero (((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m))) := ⟨hAne⟩
      rw [ZMod.val_neg_of_ne_zero, ZMod.val_natCast]
    have hvsub : padicValNat p (p ^ (e - m) - p ^ m * δ % p ^ (e - m))
        = m + padicValNat p δ := by
      rw [padicValNat_pow_sub_mod ha_ne hvltK, hvpa]
    have hpos : 0 < p ^ (e - m) - p ^ m * δ % p ^ (e - m) := by
      have := Nat.mod_lt (p ^ m * δ) (pow_pos hp.pos (e - m))
      omega
    have hL : vcap p (e - m) ((-(((p ^ m * δ : ℕ)) : ZMod (p ^ (e - m)))).val)
        = m + padicValNat p δ := by
      rw [hxv]; unfold vcap; rw [if_neg (ne_of_gt hpos), hvsub]
      exact Nat.min_eq_left (le_of_lt hmv)
    have hR : vcap p (e - 2 * m) δ = padicValNat p δ := by
      unfold vcap; rw [if_neg hδ0]
      exact Nat.min_eq_left (le_of_lt hvδ)
    rw [hL, hR]

end Work.LinnikBurgess
