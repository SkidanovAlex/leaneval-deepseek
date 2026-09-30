import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.Delta_pow_expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial Finset

/-! ### Expanding `Δ(z;j) · z^i` and `Δ(z;j) · (a z + c)^k` in the `Δ(z;e)`

The functions `Delta · e` for `e = 0, …, N` span the polynomials of degree `≤ N`
(`Delta_pow_expansion` treats the pure powers `z^k`).  Here we first show that the products
`Δ(z;j) · z^i` also lie in this span, with `e` ranging up to `i + j`, by the recurrence
`z · Δ(z;e) = (e+1)(Δ(z;e+1) - Δ(z;e))` (`Delta_mul_self`) together with Abel summation
(`Delta_sum_shift`).  Then `(a z + c)^k` is expanded by the binomial theorem. -/

/-- For all `i`, `j`, the product `Δ(z;j) · z^i` is a finite ℂ-linear combination of the
`Δ(z;e)` with `e ≤ i + j`. -/
lemma Delta_mul_pow_expansion (i j : ℕ) :
    ∃ β : ℕ → ℂ, (∀ e, i + j < e → β e = 0) ∧
      ∀ z : ℂ, Delta z j * z ^ i = ∑ e ∈ Finset.range (i + j + 1), β e * Delta z e := by
  revert j
  induction i with
  | zero =>
    intro j
    refine ⟨fun e => if e = j then 1 else 0, ?_, ?_⟩
    · intro e he
      have hne : e ≠ j := by omega
      simp [hne]
    · intro z
      rw [pow_zero, mul_one]
      symm
      rw [Finset.sum_eq_single j (fun b _ hbj => by simp [hbj])
            (fun hj => absurd (by simp : j ∈ Finset.range (0 + j + 1)) hj)]
      simp
  | succ i ih =>
    intro j
    obtain ⟨β, hβsupp, hβval⟩ := ih j
    refine ⟨fun m => (m : ℂ) * β (m - 1) - ((m + 1 : ℕ) : ℂ) * β m, ?_, ?_⟩
    · intro m hm
      have hm1 : i + j < m := by omega
      have hm2 : i + j < m - 1 := by omega
      change (m : ℂ) * β (m - 1) - ((m + 1 : ℕ) : ℂ) * β m = 0
      rw [hβsupp m hm1, hβsupp (m - 1) hm2]
      ring
    · intro z
      have hstep : Delta z j * z ^ (i + 1) = z * (Delta z j * z ^ i) := by ring
      rw [hstep, hβval z, Finset.mul_sum]
      rw [show (∑ e ∈ Finset.range (i + j + 1), z * (β e * Delta z e))
            = ∑ e ∈ Finset.range (i + j + 1),
                β e * (((e + 1 : ℕ) : ℂ) * (Delta z (e + 1) - Delta z e)) from by
            apply Finset.sum_congr rfl
            intro e _
            rw [show z * (β e * Delta z e) = β e * (z * Delta z e) from by ring, Delta_mul_self]]
      rw [show i + 1 + j + 1 = (i + j) + 2 from by omega]
      exact Delta_sum_shift β (i + j) (hβsupp (i + j + 1) (by omega)) (fun m => Delta z m)

/-- The main expansion: `Δ(z;j) · (a z + c)^k` is a finite ℂ-linear combination of the
`Δ(z;e)` with `e ≤ k + j`. -/
theorem Delta_mul_affine_pow_expansion (k j : ℕ) (a c : ℂ) :
    ∃ β : ℕ → ℂ, (∀ e, k + j < e → β e = 0) ∧
      ∀ z : ℂ, Work.BW.Delta z j * (a * z + c) ^ k
        = ∑ e ∈ Finset.range (k + j + 1), β e * Work.BW.Delta z e := by
  choose β hβsupp hβval using fun i => Delta_mul_pow_expansion i j
  refine ⟨fun e => ∑ i ∈ Finset.range (k + 1),
      (((k.choose i : ℂ)) * a ^ i * c ^ (k - i)) * β i e, ?_, ?_⟩
  · intro e he
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hβsupp i e (by omega), mul_zero]
  · intro z
    have hpow : (a * z + c) ^ k
        = ∑ i ∈ Finset.range (k + 1), (a * z) ^ i * c ^ (k - i) * (k.choose i : ℂ) :=
      add_pow (a * z) c k
    rw [hpow, Finset.mul_sum]
    rw [show (∑ i ∈ Finset.range (k + 1),
              Delta z j * ((a * z) ^ i * c ^ (k - i) * (k.choose i : ℂ)))
          = ∑ i ∈ Finset.range (k + 1),
              ((k.choose i : ℂ) * a ^ i * c ^ (k - i)) * (Delta z j * z ^ i) from by
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_pow]
            ring]
    rw [show (∑ i ∈ Finset.range (k + 1),
              ((k.choose i : ℂ) * a ^ i * c ^ (k - i)) * (Delta z j * z ^ i))
          = ∑ i ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.range (i + j + 1),
                ((k.choose i : ℂ) * a ^ i * c ^ (k - i)) * (β i e * Delta z e) from by
            apply Finset.sum_congr rfl
            intro i _
            rw [hβval i z, Finset.mul_sum]]
    rw [show (∑ e ∈ Finset.range (k + j + 1),
              (∑ i ∈ Finset.range (k + 1),
                ((k.choose i : ℂ) * a ^ i * c ^ (k - i)) * β i e) * Delta z e)
          = ∑ e ∈ Finset.range (k + j + 1),
              ∑ i ∈ Finset.range (k + 1),
                (((k.choose i : ℂ) * a ^ i * c ^ (k - i)) * β i e) * Delta z e from by
            apply Finset.sum_congr rfl
            intro e _
            rw [Finset.sum_mul]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    trans ∑ e ∈ Finset.range (i + j + 1),
            (((k.choose i : ℂ) * a ^ i * c ^ (k - i)) * β i e) * Delta z e
    · apply Finset.sum_congr rfl
      intro e _
      ring
    · apply Finset.sum_subset
      · intro e he
        rw [Finset.mem_range] at he ⊢
        omega
      · intro e he hne
        rw [Finset.mem_range] at he hne
        rw [hβsupp i e (by omega)]
        ring

end Work.BW
