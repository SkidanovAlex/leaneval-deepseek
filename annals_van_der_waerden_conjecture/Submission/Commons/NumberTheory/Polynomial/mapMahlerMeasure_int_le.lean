import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace Commons.NumberTheory.Polynomial

open Finset

theorem mapMahlerMeasure_int_le (f : Polynomial ℤ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i, |((f.coeff i : ℤ) : ℝ)| ≤ B) :
    Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ ((f.natDegree : ℝ) + 1) * B := by
  rw [Polynomial.mapMahlerMeasure_eq]
  have hmain : (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      ((f.map (Int.castRingHom ℂ)).support.card : ℝ) * B := by
    calc (f.map (Int.castRingHom ℂ)).mahlerMeasure
        ≤ (f.map (Int.castRingHom ℂ)).sum (fun _ a ↦ ‖a‖) :=
          Polynomial.mahlerMeasure_le_sum_norm_coeff _
      _ = ∑ i ∈ (f.map (Int.castRingHom ℂ)).support,
            ‖(f.map (Int.castRingHom ℂ)).coeff i‖ := by rw [Polynomial.sum_def]
      _ ≤ ∑ _i ∈ (f.map (Int.castRingHom ℂ)).support, B := by
          apply Finset.sum_le_sum
          intro i _
          rw [Polynomial.coeff_map]
          simpa using h i
      _ = ((f.map (Int.castRingHom ℂ)).support.card : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine hmain.trans ?_
  gcongr
  have hsub : (f.map (Int.castRingHom ℂ)).support ⊆ f.support :=
    Polynomial.support_map_subset _ f
  calc ((f.map (Int.castRingHom ℂ)).support.card : ℝ)
      ≤ (f.support.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (f.natDegree : ℝ) + 1 := by
        have := f.card_supp_le_succ_natDegree
        exact_mod_cast this

end Commons.NumberTheory.Polynomial