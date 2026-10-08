import Mathlib
import Submission.Work.PSL2.Card

namespace Work.CORE4.L2PAux

/-- **Cardinality of `PSL(2, GF(ρ,k))` in factored form.**

For an odd prime `ρ` and `k ≠ 0`, the order of `PSL(2, GF(ρ,k))` is
`(ρ^k + 1) · ρ^k · (ρ^k - 1)/2`.

This is `Work.PSL2.card_PSL2_galoisField` (which gives `2 · |PSL| = ρ^k (ρ^(2k) - 1)`)
combined with `ρ^(2k) - 1 = (ρ^k + 1)(ρ^k - 1)` and the observation that `2 ∣ ρ^k - 1`
because `ρ` is odd. -/
theorem card_psl2_galoisField_factored (ρ k : ℕ) [Fact ρ.Prime] (hρ : Odd ρ) (hk : k ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)) =
      (ρ ^ k + 1) * ρ ^ k * ((ρ ^ k - 1) / 2) := by
  have h := Work.PSL2.card_PSL2_galoisField ρ k hρ hk
  -- `ρ ^ (2 * k) = (ρ ^ k) ^ 2`
  have h2k : ρ ^ (2 * k) = (ρ ^ k) ^ 2 := by rw [Nat.mul_comm 2 k, pow_mul]
  rw [h2k] at h
  -- `(ρ ^ k) ^ 2 - 1 = (ρ ^ k + 1) * (ρ ^ k - 1)`
  have hfac : (ρ ^ k) ^ 2 - 1 = (ρ ^ k + 1) * (ρ ^ k - 1) := by
    simpa using Nat.sq_sub_sq (ρ ^ k) 1
  rw [hfac] at h
  -- `2 ∣ ρ ^ k - 1` because `ρ ^ k` is odd
  obtain ⟨m, hm⟩ := hρ.pow (n := k)
  have hdvd : 2 ∣ ρ ^ k - 1 := ⟨m, by omega⟩
  have hpk1 : ρ ^ k - 1 = 2 * ((ρ ^ k - 1) / 2) := (Nat.mul_div_cancel' hdvd).symm
  -- cancel the common factor `2`
  refine Nat.mul_left_cancel (n := 2) (by norm_num) ?_
  rw [h]
  conv_lhs => rw [hpk1]
  ring

theorem factorization_card_psl2 (ρ k : ℕ) [Fact ρ.Prime] (hρ : Odd ρ) (hk : 5 ≤ ρ ^ k) :
    (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k))).factorization ρ = k ∧
    ρ ^ k ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)) ∧
    ¬ ρ ^ (k + 1) ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact absurd hk (by norm_num)
  have hcard := card_psl2_galoisField_factored ρ k hρ hk0
  have hA_ne : ρ ^ k + 1 ≠ 0 := by positivity
  have hB_ne : ρ ^ k ≠ 0 := by positivity
  have hC_ne : (ρ ^ k - 1) / 2 ≠ 0 := by
    have : 0 < (ρ ^ k - 1) / 2 := Nat.div_pos (by omega) (by norm_num)
    omega
  -- `ρ ∤ ρ ^ k + 1`
  have hAdvd : ¬ ρ ∣ ρ ^ k + 1 := by
    intro h
    have hb : ρ ∣ ρ ^ k := dvd_pow_self ρ hk0
    exact (Fact.out : ρ.Prime).not_dvd_one ((Nat.dvd_add_iff_right hb).mpr h)
  -- `ρ ∤ (ρ ^ k - 1) / 2`
  have hCdvd : ¬ ρ ∣ (ρ ^ k - 1) / 2 := by
    intro h
    have hb : ρ ∣ ρ ^ k := dvd_pow_self ρ hk0
    obtain ⟨m, hm⟩ := hρ.pow (n := k)
    have hdvd : 2 ∣ ρ ^ k - 1 := ⟨m, by omega⟩
    have h2C : 2 * ((ρ ^ k - 1) / 2) = ρ ^ k - 1 := Nat.mul_div_cancel' hdvd
    have h' : ρ ∣ ρ ^ k - 1 := by rw [← h2C]; exact dvd_mul_of_dvd_right h 2
    have hsub := Nat.dvd_sub hb h'
    have h1 : ρ ∣ 1 := by
      rwa [show ρ ^ k - (ρ ^ k - 1) = 1 from by omega] at hsub
    exact (Fact.out : ρ.Prime).not_dvd_one h1
  -- the `ρ`-adic valuation of the product is `k`
  have hfac : ((ρ ^ k + 1) * ρ ^ k * ((ρ ^ k - 1) / 2)).factorization ρ = k := by
    rw [Nat.factorization_mul (mul_ne_zero hA_ne hB_ne) hC_ne,
        Nat.factorization_mul hA_ne hB_ne]
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd hAdvd,
        Nat.factorization_pow_self (Fact.out : ρ.Prime),
        Nat.factorization_eq_zero_of_not_dvd hCdvd]
    simp
  have hNfac :
      (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k))).factorization ρ
        = k := by
    rw [hcard]; exact hfac
  have hNne : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)) ≠ 0 := by
    rw [hcard]; exact mul_ne_zero (mul_ne_zero hA_ne hB_ne) hC_ne
  refine ⟨hNfac, ?_, ?_⟩
  · exact (Fact.out : ρ.Prime).pow_dvd_iff_le_factorization hNne |>.mpr (le_of_eq hNfac.symm)
  · intro h
    have hle := ((Fact.out : ρ.Prime).pow_dvd_iff_le_factorization hNne).mp h
    omega

end Work.CORE4.L2PAux
