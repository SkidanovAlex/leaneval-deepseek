import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory in
theorem irrEqTrivialOfInvFixed {K : Type} [Group K] [Finite K] [Fintype K]
    (hodd : Odd (Nat.card K)) [IsMulCommutative K] (μ : ClassFunction K ℂ)
    (hμ : IsIrreducibleCharacter μ) (hinv : ∀ k : K, μ k⁻¹ = μ k) :
    μ = trivialClassFunction K := by
  -- Every irreducible character of a commutative group is a linear character.
  obtain ⟨χ, hχ⟩ := hμ.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  -- `hinv` forces `χ k = (χ k)⁻¹`, i.e. `(χ k)^2 = 1`, for every `k`.
  have hval : ∀ k : K, (χ k : ℂ) = 1 := by
    intro k
    have hk : (χ k)⁻¹ = χ k := by
      apply Units.ext
      have h := hinv k
      rw [← hχ] at h
      simpa [linearIrreducibleCharacter_apply] using h
    have hsq : (χ k) ^ 2 = 1 := by
      have h2 := mul_inv_cancel (χ k)
      rw [hk] at h2
      simpa [sq] using h2
    -- `orderOf (χ k)` divides both `2` and `orderOf k`; the latter is odd.
    have hm : orderOf (χ k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    have hmk : orderOf (χ k) ∣ orderOf k := orderOf_map_dvd χ k
    have hoddk : Odd (orderOf k) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard k)
    have hone : orderOf (χ k) = 1 := by
      have hcop : Nat.Coprime 2 (orderOf k) := hoddk.coprime_two_left
      have hdvd : orderOf (χ k) ∣ Nat.gcd 2 (orderOf k) := Nat.dvd_gcd hm hmk
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hdvd
      exact Nat.dvd_one.mp hdvd
    have hχk : χ k = 1 := orderOf_eq_one_iff.mp hone
    rw [hχk]
    simp
  apply ClassFunction.ext
  intro k
  rw [← hχ]
  simp [hval k]

end Work.BG
