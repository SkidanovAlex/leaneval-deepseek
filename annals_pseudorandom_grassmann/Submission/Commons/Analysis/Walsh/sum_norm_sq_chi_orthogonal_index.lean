import Mathlib
import Submission.Commons.Analysis.Walsh.sum_norm_sq_chi_orthogonal

namespace Commons.Analysis.Walsh

open Finset BigOperators

noncomputable section

/-- Orthogonality form of Parseval for the Walsh characters with an arbitrary injective
re-indexing `R` of the character index sets. -/
theorem sum_norm_sq_chi_orthogonal_index {n : ℕ} (s : Finset (Finset (Fin n))) (a : Finset (Fin n) → ℂ)
    (R : Finset (Fin n) → Finset (Fin n)) (hinj : ∀ T ∈ s, ∀ U ∈ s, R T = R U → T = U) :
    (∑ x : Fin n → ZMod 2, ‖∑ T ∈ s, a T * ∏ i ∈ R T, ZMod.stdAddChar (x i)‖ ^ 2)
      = (2 : ℝ) ^ n * ∑ T ∈ s, ‖a T‖ ^ 2 := by
  classical
  have key : (∑ x : Fin n → ZMod 2, ‖∑ S ∈ s, a S * chi (R S) x‖ ^ 2)
      = (2 : ℝ) ^ n * ∑ S ∈ s, ‖a S‖ ^ 2 := by
    have hsq : ∀ z : ℂ, (Complex.normSq z : ℂ) = z * (starRingEnd ℂ) z :=
      fun z => (Complex.mul_conj z).symm
    have hcomplex :
        (∑ x : Fin n → ZMod 2, (Complex.normSq (∑ S ∈ s, a S * chi (R S) x) : ℂ))
          = (2 : ℂ) ^ n * ∑ S ∈ s, (Complex.normSq (a S) : ℂ) := by
      have hstar : ∀ x : Fin n → ZMod 2,
          (starRingEnd ℂ) (∑ S ∈ s, a S * chi (R S) x)
            = ∑ T ∈ s, (starRingEnd ℂ) (a T) * chi (R T) x := by
        intro x
        rw [map_sum]
        exact Finset.sum_congr rfl fun T _ => by rw [map_mul, star_chi]
      have hexpand : ∀ x : Fin n → ZMod 2,
          (∑ S ∈ s, a S * chi (R S) x) * (starRingEnd ℂ) (∑ S ∈ s, a S * chi (R S) x)
            = ∑ S ∈ s, ∑ T ∈ s,
                a S * (starRingEnd ℂ) (a T) * chi ((R S \ R T) ∪ (R T \ R S)) x := by
        intro x
        rw [hstar x, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => by
          rw [show a S * chi (R S) x * ((starRingEnd ℂ) (a T) * chi (R T) x)
              = a S * (starRingEnd ℂ) (a T) * (chi (R S) x * chi (R T) x) by ring, chi_mul]
      rw [Finset.sum_congr rfl (fun x _ => hsq _),
          Finset.sum_congr rfl (fun S _ => hsq _)]
      rw [Finset.sum_congr rfl (fun x _ => hexpand x)]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun S _ => Finset.sum_comm)]
      simp_rw [← Finset.mul_sum]
      simp only [sum_chi_apply, sdiff_union_eq_empty_iff]
      have hinner : ∀ S ∈ s,
          (∑ T ∈ s, a S * (starRingEnd ℂ) (a T) * (if R S = R T then (2 : ℂ) ^ n else 0))
            = a S * (starRingEnd ℂ) (a S) * (2 : ℂ) ^ n := by
        intro S hS
        rw [Finset.sum_eq_single S]
        · rw [if_pos rfl]
        · intro T hT hTS
          rw [if_neg (fun h => hTS (hinj S hS T hT h).symm), mul_zero]
        · intro hS'; exact absurd hS hS'
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, mul_comm]
    have hreal : (∑ x : Fin n → ZMod 2, Complex.normSq (∑ S ∈ s, a S * chi (R S) x))
        = (2 : ℝ) ^ n * ∑ S ∈ s, Complex.normSq (a S) := by
      apply Complex.ofReal_inj.mp
      rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum,
        Complex.ofReal_ofNat]
      simpa using hcomplex
    calc (∑ x : Fin n → ZMod 2, ‖∑ S ∈ s, a S * chi (R S) x‖ ^ 2)
        = ∑ x : Fin n → ZMod 2, Complex.normSq (∑ S ∈ s, a S * chi (R S) x) :=
          Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_norm_sq _).symm
      _ = (2 : ℝ) ^ n * ∑ S ∈ s, Complex.normSq (a S) := hreal
      _ = (2 : ℝ) ^ n * ∑ S ∈ s, ‖a S‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun S _ => Complex.normSq_eq_norm_sq (a S)
  simpa only [chi] using key

end

end Commons.Analysis.Walsh
