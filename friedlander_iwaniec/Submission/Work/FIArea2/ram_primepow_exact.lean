import Mathlib
import Submission.Work.FIArea2.TsumDefs2

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `p^(k+1)/p = p^k`. -/
private lemma ram_pp_pow_div (p k : ℕ) (hp : Nat.Prime p) : p ^ (k + 1) / p = p ^ k := by
  rw [pow_succ]
  exact Nat.mul_div_cancel _ hp.pos

/-- **Splitting the Ramanujan sum at a prime power.** The terms coprime to `p^(k+1)` are `ram`,
the others are the multiples of `p` and reindex to `T (p^k) h`, so
`ram (p^(k+1)) h = T (p^(k+1)) h - T (p^k) h`. -/
private lemma ram_pp_decomp (p k : ℕ) (hp : Nat.Prime p) (h : ℤ) :
    ram (p ^ (k + 1)) h = T (p ^ (k + 1)) h - T (p ^ k) h := by
  have hsplit := sum_filter_add_sum_filter_not (s := Icc 1 (p^(k+1)))
      (p := fun η => Nat.Coprime η (p^(k+1)))
      (f := fun η => E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)))
  have hfull : (∑ η ∈ Icc 1 (p^(k+1)),
      E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ))) = T (p^(k+1)) h := by
    unfold T; rfl
  have hnotcop : (∑ η ∈ (Icc 1 (p^(k+1))).filter (fun η => ¬ Nat.Coprime η (p^(k+1))),
        E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ))) = T (p^k) h := by
    rw [show (Icc 1 (p^(k+1))).filter (fun η => ¬ Nat.Coprime η (p^(k+1)))
        = (Icc 1 (p^(k+1))).filter (fun η => p ∣ η) from by
      apply filter_congr; intro η _
      rw [Nat.coprime_pow_right_iff (n := k+1) (Nat.succ_pos k), Nat.coprime_comm,
          hp.coprime_iff_not_dvd]
      tauto]
    rw [sum_Icc_filter_dvd (p^(k+1)) p ⟨p^k, by rw [pow_succ']⟩
          (fun η => E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)))]
    rw [ram_pp_pow_div p k hp]
    unfold T
    apply sum_congr rfl
    intro j hj
    congr 1
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast
    rw [pow_succ]
    field_simp
  calc ram (p^(k+1)) h
      = ∑ η ∈ (Icc 1 (p^(k+1))).filter (fun η => Nat.Coprime η (p^(k+1))),
          E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)) := rfl
    _ = (∑ η ∈ Icc 1 (p^(k+1)), E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)))
          - (∑ η ∈ (Icc 1 (p^(k+1))).filter (fun η => ¬ Nat.Coprime η (p^(k+1))),
              E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ))) := by
          rw [← hsplit]; ring
    _ = T (p^(k+1)) h - T (p^k) h := by rw [hfull, hnotcop]

theorem ram_primepow_exact (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (h : ℤ) :
    ram (p ^ k) h
      = (if ((p ^ k : ℕ) : ℤ) ∣ h then ((p ^ k : ℕ) : ℂ) else 0)
        - (if ((p ^ (k - 1) : ℕ) : ℤ) ∣ h then ((p ^ (k - 1) : ℕ) : ℂ) else 0) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [show k' + 1 - 1 = k' from Nat.add_sub_cancel k' 1]
  rw [ram_pp_decomp p k' hp h, T_eq (p^(k'+1)) (Nat.one_le_pow _ p hp.pos) h,
      T_eq (p^k') (Nat.one_le_pow _ p hp.pos) h]

end

end Work.FIArea2
