import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Submission.Commons.NumberTheory.BombieriVinogradov.indicator_char
import Submission.Commons.NumberTheory.BombieriVinogradov.mean_value_small_modulus_bound

open scoped BigOperators

namespace Commons.NumberTheory.BombieriVinogradov

lemma residue_vonMangoldt_char_sum (q : ℕ) [NeZero q] (x a : ℕ) (ha : a.Coprime q) :
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        (ArithmeticFunction.vonMangoldt n : ℂ)) =
      ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))) := by
  classical
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have h :
      (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q), Λ n) =
      ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
          Λ n * χ (n : ZMod q))) := by
    calc
      (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q), Λ n)
          = ∑ n ∈ Finset.range (x + 1), if n % q = a % q then Λ n else 0 := by
              rw [Finset.sum_filter]
      _ = ∑ n ∈ Finset.range (x + 1),
              Λ n * (((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
                χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hp : n % q = a % q
              · rw [if_pos hp]
                have hc : ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
                    χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) = (1 : ℂ) := by
                  rw [← indicator_char q a ha n, if_pos hp]
                rw [hc, mul_one]
              · rw [if_neg hp]
                have hc : ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
                    χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) = (0 : ℂ) := by
                  rw [← indicator_char q a ha n, if_neg hp]
                rw [hc, mul_zero]
      _ = ((q.totient : ℂ)⁻¹) * (∑ n ∈ Finset.range (x + 1),
              Λ n * (∑ χ : DirichletCharacter ℂ q,
                χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
      _ = ((q.totient : ℂ)⁻¹) * (∑ n ∈ Finset.range (x + 1),
              ∑ χ : DirichletCharacter ℂ q,
                Λ n * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [Finset.mul_sum]
      _ = ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
              ∑ n ∈ Finset.range (x + 1),
                Λ n * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
              congr 1
              rw [Finset.sum_comm]
      _ = ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
              ∑ n ∈ Finset.range (x + 1),
                χ ((a : ZMod q)⁻¹) * (Λ n * χ (n : ZMod q))) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro χ hχ
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
      _ = ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
              χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
                Λ n * χ (n : ZMod q))) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro χ hχ
              rw [Finset.mul_sum]
  simpa [Λ] using h

end Commons.NumberTheory.BombieriVinogradov