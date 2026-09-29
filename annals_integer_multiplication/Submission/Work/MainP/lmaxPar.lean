import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-- `lmax ts = rpar n` for `ParamOK n ts ss`: the maximum of `ts` is `rpar n`.
Every `tᵢ` is `rpar n` or `rpar n/2`, hence `≤ rpar n`; and not all `tᵢ` are `rpar n/2`, because
then `∏tᵢ = (r/2)^d = 2^(d(kr-1))` while `∏tᵢ = Tpar n = 2^kTpar` would force
`kTpar = d(kr-1)`, contradicting `d(kr-1) < kTpar` (ceil-division, needs `1 ≤ kTpar`).
Use `List.max_le_of_forall_le` and `List.le_max_of_le`. -/
theorem lmaxPar (n : ℕ) (ts ss : List ℕ) (hOK : HvdH.ParamOK n ts ss)
    (hkT : 1 ≤ HvdH.kTpar n) : HvdH.lmax ts = HvdH.rpar n := by
  obtain ⟨hlen, -, -, hprod, hmem, -⟩ := hOK
  -- Every entry is `≤ rpar n`.
  have hub : ∀ t ∈ ts, t ≤ HvdH.rpar n := by
    intro t ht
    rcases hmem t ht with h | h
    · rw [h]
    · omega
  have hle : HvdH.lmax ts ≤ HvdH.rpar n := by
    simpa [HvdH.lmax] using List.max_le_of_forall_le ts (HvdH.rpar n) hub
  -- Some entry equals `rpar n`: not all can be `rpar n / 2`, else the product would be too small.
  have hex : ∃ t ∈ ts, t = HvdH.rpar n := by
    by_contra hc
    have hc' : ∀ t ∈ ts, t ≠ HvdH.rpar n := fun t ht h => hc ⟨t, ht, h⟩
    have hall : ∀ t ∈ ts, 2 * t = HvdH.rpar n := by
      intro t ht
      rcases hmem t ht with h | h
      · exact absurd h (hc' t ht)
      · exact h
    set e := (HvdH.kTpar n + HvdH.D - 1) / HvdH.D with he
    have hD : 0 < HvdH.D := by decide
    have he1 : 1 ≤ e := by
      rw [he, Nat.le_div_iff_mul_le hD]
      omega
    -- each entry is then `2^(e-1)`
    have hhalf : ∀ t ∈ ts, t = 2 ^ (e - 1) := by
      intro t ht
      have h2t := hall t ht
      rw [show HvdH.rpar n = 2 ^ e from rfl] at h2t
      have hone : 2 ^ e = 2 * 2 ^ (e - 1) := by
        conv_lhs => rw [show e = (e - 1) + 1 by omega]
        rw [Nat.pow_succ']
      rw [hone] at h2t
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2t
    have hprodeq : ts.prod = 2 ^ ((e - 1) * HvdH.D) := by
      rw [List.prod_eq_pow_length ts (2 ^ (e - 1)) hhalf, hlen, pow_mul]
    have hexp : (e - 1) * HvdH.D = HvdH.kTpar n := by
      have h1 : 2 ^ ((e - 1) * HvdH.D) = 2 ^ HvdH.kTpar n := by
        rw [← hprodeq, hprod]
        rfl
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1
    -- but `d · (e-1) = d·e - d ≤ (kT + d - 1) - d = kT - 1 < kT`
    have hle1 : HvdH.D * e ≤ HvdH.kTpar n + HvdH.D - 1 := by
      rw [Nat.mul_comm, he]
      exact Nat.div_mul_le_self _ _
    have hsub : HvdH.D * (e - 1) ≤ HvdH.kTpar n - 1 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have h := Nat.sub_le_sub_right hle1 HvdH.D
      have h2 : HvdH.kTpar n + HvdH.D - 1 - HvdH.D = HvdH.kTpar n - 1 := by omega
      omega
    have hlt : HvdH.D * (e - 1) < HvdH.kTpar n := by omega
    rw [Nat.mul_comm] at hlt
    omega
  obtain ⟨t, ht, ht_eq⟩ := hex
  have hge : HvdH.rpar n ≤ HvdH.lmax ts := by
    simpa [HvdH.lmax] using List.le_max_of_le ht (le_of_eq ht_eq.symm)
  exact le_antisymm hle hge

end Work.MainP
