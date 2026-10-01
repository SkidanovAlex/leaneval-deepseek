import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex

open Finset

namespace Work.LinnikAreas.Density4

/-- Harmonic bound: `∑_{m ≤ Y} 1/m ≤ 1 + log Y` (Mathlib's `harmonic_le_one_add_log`). -/
lemma sum_Icc_inv_le_one_add_log (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, ((m : ℝ)⁻¹) ≤ 1 + Real.log (Y : ℝ) := by
  have h := harmonic_le_one_add_log Y
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- The partial `σ`-sum bound, valid for every `σ ≤ 1`: writing
`m^{-σ} = m^{1-σ} · m^{-1}` and using `m^{1-σ} ≤ Y^{1-σ}` (as `1 - σ ≥ 0`), the sum is at most
`Y^{1-σ} ∑_{m ≤ Y} 1/m ≤ Y^{1-σ} (1 + log Y)`. -/
lemma sum_Icc_rpow_neg_le_of_le_one {Y : ℕ} (hY : 1 ≤ Y) {σ : ℝ} (hσ : σ ≤ 1) :
    ∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (1 - σ) * (1 + Real.log (Y : ℝ)) := by
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hexp : 0 ≤ 1 - σ := by linarith
  have hYexp : 0 ≤ (Y : ℝ) ^ (1 - σ) := Real.rpow_nonneg hYpos.le _
  calc ∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-σ)
      = ∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : (0 : ℝ) < (m : ℝ) := by
          have h1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          exact_mod_cast (by omega : 0 < m)
        rw [← Real.rpow_neg_one (m : ℝ), ← Real.rpow_add hm0 (1 - σ) (-1)]
        congr 1
        ring
    _ ≤ ∑ m ∈ Finset.Icc 1 Y, (Y : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
        have hmle : (m : ℝ) ≤ (Y : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hm).2
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm0 hmle hexp) (by positivity)
    _ = (Y : ℝ) ^ (1 - σ) * ∑ m ∈ Finset.Icc 1 Y, (m : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (Y : ℝ) ^ (1 - σ) * (1 + Real.log (Y : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hYexp
        exact sum_Icc_inv_le_one_add_log Y

/-- `∑_{d ≤ A} d^{-σ} τ(d) ≤ A^{1-σ} (1 + log A)^2` for `A ≥ 1` and `σ ≤ 1`.

Writing `τ(d) = Σ_{ab = d} 1`, the sum becomes `Σ_{a b ≤ A} (ab)^{-σ}`, which is grouped as
`Σ_{a ≤ A} a^{-σ} Σ_{b ≤ A/a} b^{-σ}`; the inner sum is bounded by
`(A/a)^{1-σ}(1 + log(A/a))`, the product with `a^{-σ}` collapses to `A^{1-σ}/a`, and the harmonic
sum `Σ_{a ≤ A} 1/a` is at most `1 + log A`. -/
lemma sum_tau_mul_rpow_neg_le {A : ℕ} (hA : 1 ≤ A) {σ : ℝ} (hσ1 : σ ≤ 1) :
    ∑ d ∈ Finset.Icc 1 A, (d : ℝ) ^ (-σ) * (d.divisors.card : ℝ)
      ≤ (A : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2 := by
  have hApos : 0 < A := by omega
  have hAr : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hexp : 0 ≤ 1 - σ := by linarith
  -- Step 1: the divisor-sum identity `Σ_{ab ≤ A} (ab)^{-σ} = Σ_{d ≤ A} d^{-σ} τ(d)`.
  have key' : ∑ a ∈ Finset.Icc 1 A, ∑ b ∈ Finset.Icc 1 (A / a), ((a * b : ℕ) : ℝ) ^ (-σ)
      = ∑ d ∈ Finset.Icc 1 A, (d : ℝ) ^ (-σ) * (d.divisors.card : ℝ) := by
    have key := sum_Icc_div_reindex A (fun _ => True) (fun a b => ((a * b : ℕ) : ℝ) ^ (-σ))
    simp only [Finset.filter_true] at key
    rw [key]
    apply Finset.sum_congr rfl
    intro n hn
    have hterm : ∀ d ∈ n.divisors, ((d * (n / d) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := by
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [← key']
  -- Step 2: distribute the `a^{-σ}` factor over the inner sum.
  have hrewrite : ∑ a ∈ Finset.Icc 1 A, ∑ b ∈ Finset.Icc 1 (A / a), ((a * b : ℕ) : ℝ) ^ (-σ)
      = ∑ a ∈ Finset.Icc 1 A, (a : ℝ) ^ (-σ) * (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Real.mul_rpow (by positivity) (by positivity), Nat.cast_mul]
  rw [hrewrite]
  -- Step 3: termwise bound.
  have hterm : ∀ a ∈ Finset.Icc 1 A,
      (a : ℝ) ^ (-σ) * (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ))
        ≤ (A : ℝ) ^ (1 - σ) * (a : ℝ)⁻¹ * (1 + Real.log (A : ℝ)) := by
    intro a ha
    obtain ⟨ha1, haA⟩ := Finset.mem_Icc.mp ha
    have hapos : 0 < a := by omega
    have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
    have hN1 : 1 ≤ A / a := (Nat.one_le_div_iff hapos).mpr haA
    have hNpos : (0 : ℝ) < ((A / a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < A / a)
    have hNle : ((A / a : ℕ) : ℝ) ≤ (A : ℝ) / (a : ℝ) := Nat.cast_div_le
    have hS : (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ))
        ≤ ((A / a : ℕ) : ℝ) ^ (1 - σ) * (1 + Real.log ((A / a : ℕ) : ℝ)) :=
      sum_Icc_rpow_neg_le_of_le_one (Y := A / a) (σ := σ) hN1 hσ1
    have hrpow : ((A / a : ℕ) : ℝ) ^ (1 - σ) ≤ ((A : ℝ) / (a : ℝ)) ^ (1 - σ) :=
      Real.rpow_le_rpow hNpos.le hNle hexp
    have hlog : (1 + Real.log ((A / a : ℕ) : ℝ)) ≤ (1 + Real.log ((A : ℝ) / (a : ℝ))) := by
      have h := Real.log_le_log hNpos hNle
      linarith
    have hfactor : 0 ≤ (1 + Real.log ((A / a : ℕ) : ℝ)) := by
      have h1 : (1 : ℝ) ≤ ((A / a : ℕ) : ℝ) := by exact_mod_cast hN1
      linarith [Real.log_nonneg h1]
    have hbound1 : (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ))
        ≤ ((A : ℝ) / (a : ℝ)) ^ (1 - σ) * (1 + Real.log ((A : ℝ) / (a : ℝ))) := by
      calc _ ≤ ((A / a : ℕ) : ℝ) ^ (1 - σ) * (1 + Real.log ((A / a : ℕ) : ℝ)) := hS
        _ ≤ ((A : ℝ) / (a : ℝ)) ^ (1 - σ) * (1 + Real.log ((A / a : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hrpow hfactor
        _ ≤ ((A : ℝ) / (a : ℝ)) ^ (1 - σ) * (1 + Real.log ((A : ℝ) / (a : ℝ))) :=
            mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by positivity) _)
    have step1 : (a : ℝ) ^ (-σ) * (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ))
        ≤ (a : ℝ) ^ (-σ)
          * (((A : ℝ) / (a : ℝ)) ^ (1 - σ) * (1 + Real.log ((A : ℝ) / (a : ℝ)))) :=
      mul_le_mul_of_nonneg_left hbound1 (Real.rpow_nonneg har.le _)
    have hprod : (a : ℝ) ^ (-σ)
          * (((A : ℝ) / (a : ℝ)) ^ (1 - σ) * (1 + Real.log ((A : ℝ) / (a : ℝ))))
        = (A : ℝ) ^ (1 - σ) * (a : ℝ)⁻¹ * (1 + Real.log ((A : ℝ) / (a : ℝ))) := by
      have h1 : ((A : ℝ) / (a : ℝ)) ^ (1 - σ) = (A : ℝ) ^ (1 - σ) * (a : ℝ) ^ (σ - 1) := by
        rw [div_eq_mul_inv, Real.mul_rpow hAr.le (by positivity), Real.inv_rpow har.le,
          ← Real.rpow_neg har.le (1 - σ), show -(1 - σ) = σ - 1 by ring]
      rw [h1]
      rw [show (a : ℝ) ^ (-σ) * ((A : ℝ) ^ (1 - σ) * (a : ℝ) ^ (σ - 1)
              * (1 + Real.log ((A : ℝ) / (a : ℝ))))
            = (A : ℝ) ^ (1 - σ) * ((a : ℝ) ^ (-σ) * (a : ℝ) ^ (σ - 1))
              * (1 + Real.log ((A : ℝ) / (a : ℝ))) by ring,
        ← Real.rpow_add har, show -σ + (σ - 1) = -1 by ring, Real.rpow_neg_one]
    have hlog2 : (1 + Real.log ((A : ℝ) / (a : ℝ))) ≤ (1 + Real.log (A : ℝ)) := by
      have hdivle : (A : ℝ) / (a : ℝ) ≤ (A : ℝ) := by
        rw [div_le_iff₀ har]
        nlinarith [hAr, har, (show (1 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha1)]
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (A : ℝ) / (a : ℝ)) hdivle
      linarith
    calc (a : ℝ) ^ (-σ) * (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ))
        ≤ (a : ℝ) ^ (-σ)
          * (((A : ℝ) / (a : ℝ)) ^ (1 - σ) * (1 + Real.log ((A : ℝ) / (a : ℝ)))) := step1
      _ = (A : ℝ) ^ (1 - σ) * (a : ℝ)⁻¹ * (1 + Real.log ((A : ℝ) / (a : ℝ))) := hprod
      _ ≤ (A : ℝ) ^ (1 - σ) * (a : ℝ)⁻¹ * (1 + Real.log (A : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog2 (mul_nonneg (Real.rpow_nonneg hAr.le _) (by positivity))
  -- Step 4: sum the termwise bound and use the harmonic estimate.
  calc ∑ a ∈ Finset.Icc 1 A, (a : ℝ) ^ (-σ) * (∑ b ∈ Finset.Icc 1 (A / a), (b : ℝ) ^ (-σ))
      ≤ ∑ a ∈ Finset.Icc 1 A, (A : ℝ) ^ (1 - σ) * (a : ℝ)⁻¹ * (1 + Real.log (A : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((A : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)))
          * ∑ a ∈ Finset.Icc 1 A, (a : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
    _ ≤ ((A : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ))) * (1 + Real.log (A : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_Icc_inv_le_one_add_log A)
        exact mul_nonneg (Real.rpow_nonneg hAr.le _) (by
          have h1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
          linarith [Real.log_nonneg h1])
    _ = (A : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2 := by ring

end Work.LinnikAreas.Density4
