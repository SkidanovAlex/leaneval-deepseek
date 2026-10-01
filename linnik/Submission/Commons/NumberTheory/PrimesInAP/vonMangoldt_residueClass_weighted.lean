import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.PrimesInAP

theorem vonMangoldt_residueClass_weighted {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (X : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 X,
        ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ) * w n)
      = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ∑ n ∈ Finset.Ioc 0 X,
            (χ (n : ZMod q)) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * w n := by
  have h : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ)
        = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ a⁻¹ * (χ (n : ZMod q)) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) :=
    fun n => ArithmeticFunction.vonMangoldt.residueClass_apply (q := q) (a := a) ha n
  calc (∑ n ∈ Finset.Ioc 0 X,
          ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ) * w n)
      = ∑ n ∈ Finset.Ioc 0 X,
          (((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ a⁻¹ * (χ (n : ZMod q)) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) * w n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [h n]
    _ = ((q.totient : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc 0 X,
          (∑ χ : DirichletCharacter ℂ q,
            χ a⁻¹ * (χ (n : ZMod q)) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) * w n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ∑ n ∈ Finset.Ioc 0 X,
            (χ (n : ZMod q)) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * w n := by
        congr 1
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro χ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring

end Commons.NumberTheory.PrimesInAP