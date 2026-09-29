import Mathlib
import Submission.Work.Haupt.defs

namespace Work.Haupt

open scoped BigOperators

/-- The Hauptmodul–theta identity
`h(x²)·θ₄(x²)^8 = θ₂(x)^8 / x²` in product form: writing `ξ = x²`,
`B = ∏'ₙ (1+ξⁿ⁺¹)`, `A = ∏'ₙ (1-ξⁿ⁺¹)`, `A₂ = ∏'ₙ (1-ξ²⁽ⁿ⁺¹⁾)`,
`D = ∏'ₙ (1-ξ²ⁿ⁺¹)`, the two classical product identities are `A₂ = A B`
(from `(1-y)(1+y) = 1-y²`) and `B D = 1` (from `∏(1+qⁿ)·∏(1-q²ⁿ⁻¹) = 1`),
and then `B²⁴ A₂⁸ D¹⁶ = A⁸ B¹⁶`. -/
theorem tprod_identity (x : ℂ) (hx : ‖x‖ < 1) :
    (-256 * x ^ 2 * ∏' n : ℕ, (1 + (x ^ 2) ^ (n + 1)) ^ 24) * T4prod (x ^ 2) ^ 8
      = -x ^ 2 * T2prod x ^ 8 := by
  have hnorm : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℂ, ξ = x ^ 2 := ⟨x ^ 2, rfl⟩
  rw [← hξ]
  have hξn : ‖ξ‖ < 1 := by rw [hξ]; exact hnorm
  have hξ2n : ‖ξ ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg ξ) hξn (by norm_num)
  -- summability of the exponent families
  have hs1 : Summable (fun n : ℕ => ξ ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hξn)
  have hs2 : Summable (fun n : ℕ => ξ ^ (2 * (n + 1))) := by
    have h : Summable (fun n : ℕ => (ξ ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hξ2n)
    exact h.congr (fun n => by rw [pow_mul])
  have hs3 : Summable (fun n : ℕ => ξ ^ (2 * n + 1)) := by
    have h : Summable (fun n : ℕ => ξ * (ξ ^ 2) ^ n) :=
      (summable_geometric_of_norm_lt_one hξ2n).mul_left ξ
    exact h.congr (fun n => by rw [← pow_mul, ← pow_succ'])
  have mB : Multipliable (fun n : ℕ => 1 + ξ ^ (n + 1)) :=
    Complex.multipliable_one_add_of_summable hs1
  have mA : Multipliable (fun n : ℕ => 1 - ξ ^ (n + 1)) :=
    (Complex.multipliable_one_add_of_summable hs1.neg).congr (fun n => by simp [sub_eq_add_neg])
  have mA2 : Multipliable (fun n : ℕ => 1 - ξ ^ (2 * (n + 1))) :=
    (Complex.multipliable_one_add_of_summable hs2.neg).congr (fun n => by simp [sub_eq_add_neg])
  have mD : Multipliable (fun n : ℕ => 1 - ξ ^ (2 * n + 1)) :=
    (Complex.multipliable_one_add_of_summable hs3.neg).congr (fun n => by simp [sub_eq_add_neg])
  -- expand the two product definitions
  have hP1 : (∏' n : ℕ, (1 + ξ ^ (n + 1)) ^ 24) = (∏' n : ℕ, (1 + ξ ^ (n + 1))) ^ 24 :=
    mB.tprod_pow 24
  have hT4 : T4prod ξ
      = (∏' n : ℕ, (1 - ξ ^ (2 * (n + 1)))) * (∏' n : ℕ, (1 - ξ ^ (2 * n + 1))) ^ 2 := by
    rw [T4prod]
    rw [Multipliable.tprod_mul mA2 (mD.pow 2), mD.tprod_pow 2]
  have hT2 : T2prod x
      = 2 * ((∏' n : ℕ, (1 - ξ ^ (n + 1))) * (∏' n : ℕ, (1 + ξ ^ (n + 1))) ^ 2) := by
    rw [T2prod]
    have e : (∏' n : ℕ, (1 - x ^ (2 * (n + 1))) * (1 + x ^ (2 * (n + 1))) ^ 2)
        = ∏' n : ℕ, (1 - ξ ^ (n + 1)) * (1 + ξ ^ (n + 1)) ^ 2 :=
      tprod_congr (fun n => by rw [hξ, pow_mul])
    rw [e, Multipliable.tprod_mul mA (mB.pow 2), mB.tprod_pow 2]
  rw [hP1, hT4, hT2]
  -- name the four products
  set A : ℂ := ∏' n : ℕ, (1 - ξ ^ (n + 1)) with hA
  set B : ℂ := ∏' n : ℕ, (1 + ξ ^ (n + 1)) with hB
  set A2 : ℂ := ∏' n : ℕ, (1 - ξ ^ (2 * (n + 1))) with hA2
  set D : ℂ := ∏' n : ℕ, (1 - ξ ^ (2 * n + 1)) with hD
  -- splitting the product over `n ≥ 1` into even and odd `n`
  have hsplit : D * A2 = A := by
    rw [hD, hA2, hA]
    have hpw : ∀ k : ℕ, (1 - ξ ^ (2 * k + 1 + 1)) = (1 - ξ ^ (2 * (k + 1))) := fun k => by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega]
    have mA2' : Multipliable (fun k : ℕ => 1 - ξ ^ (2 * k + 1 + 1)) :=
      mA2.congr (fun k => (hpw k).symm)
    simpa only [hpw] using tprod_even_mul_odd (f := fun k : ℕ => 1 - ξ ^ (k + 1)) mD mA2'
  -- `A₂ = A·B`
  have hA2eq : A2 = A * B := by
    rw [hA2, hA, hB]
    have hpw2 : ∀ n : ℕ, (1 - ξ ^ (2 * (n + 1))) = (1 - ξ ^ (n + 1)) * (1 + ξ ^ (n + 1)) := by
      intro n
      have h2 : ξ ^ (2 * (n + 1)) = (ξ ^ (n + 1)) ^ 2 :=
        (congrArg (fun m => ξ ^ m) (by ring : 2 * (n + 1) = (n + 1) * 2)).trans
          (pow_mul ξ (n + 1) 2)
      rw [h2]
      ring
    rw [tprod_congr hpw2, Multipliable.tprod_mul mA mB]
  -- `A ≠ 0`
  have hAne : A ≠ 0 := by
    rw [hA]
    rw [show (∏' n : ℕ, (1 - ξ ^ (n + 1))) = ∏' n : ℕ, (1 + (-(ξ ^ (n + 1)))) from
      tprod_congr (fun n => by ring)]
    refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(ξ ^ (n + 1)))
      (fun n h0 => ?_) hs1.neg.norm
    have hy : ξ ^ (n + 1) = 1 := by
      have h1 : (1 : ℂ) = ξ ^ (n + 1) := by
        simpa using (add_eq_zero_iff_eq_neg.mp h0)
      exact h1.symm
    have h3 : ‖ξ ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg ξ) hξn (Nat.succ_ne_zero n)
    rw [hy, norm_one] at h3
    exact lt_irrefl 1 h3
  -- `B·D = 1`
  have hBD : B * D = 1 := by
    have hAA : A = (B * D) * A := by
      calc A = D * A2 := hsplit.symm
        _ = D * (A * B) := by rw [hA2eq]
        _ = (B * D) * A := by ring
    have hfin : (B * D) * A = 1 * A := by
      rw [one_mul]
      exact hAA.symm
    exact mul_right_cancel₀ hAne hfin
  have hBD16 : B ^ 16 * D ^ 16 = 1 := by
    rw [← mul_pow, hBD]
    norm_num
  have hmain : (-256 * ξ * B ^ 24) * (A2 * D ^ 2) ^ 8 = -ξ * (2 * (A * B ^ 2)) ^ 8 := by
    rw [hA2eq]
    calc (-256 * ξ * B ^ 24) * ((A * B) * D ^ 2) ^ 8
        = (-256 * ξ * A ^ 8 * B ^ 16) * (B ^ 16 * D ^ 16) := by ring
      _ = (-256 * ξ * A ^ 8 * B ^ 16) * 1 := by rw [hBD16]
      _ = -ξ * (2 * (A * B ^ 2)) ^ 8 := by ring
  exact hmain

end Work.Haupt
