import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Analysis.Walsh.chi_symmDiff
import Submission.Commons.Analysis.Walsh.sum_coord_chi
import Submission.Commons.Analysis.Walsh.sum_chi_index

namespace Commons.Analysis.Walsh

open Finset BigOperators

noncomputable section

/-- The Walsh character of the cube associated with a set of coordinates `S`:
`chi S x = ∏ i ∈ S, stdAddChar (x i)`. (For `𝔽₂` this is `(-1)^{∑_{i ∈ S} x i}`.) -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ℂ :=
  ∏ i ∈ S, ZMod.stdAddChar (x i)

/-- `stdAddChar` on `𝔽₂` is real (`±1`), hence fixed by complex conjugation. -/
lemma starRingEnd_stdAddChar_two (a : ZMod 2) :
    (starRingEnd ℂ) (ZMod.stdAddChar a) = ZMod.stdAddChar a := by
  have h : ZMod.stdAddChar a ^ 2 = 1 := by
    rw [pow_two, ← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero, AddChar.map_zero_eq_one]
  rcases sq_eq_one_iff.mp h with h | h <;> rw [h] <;> simp

/-- The Walsh characters are real-valued. -/
lemma star_chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (starRingEnd ℂ) (chi S x) = chi S x := by
  rw [chi, map_prod]
  exact Finset.prod_congr rfl fun i _ => starRingEnd_stdAddChar_two (x i)

/-- Product rule for the Walsh characters (symmetric difference of index sets). -/
lemma chi_mul {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chi S x * chi T x = chi ((S \ T) ∪ (T \ S)) x :=
  chi_symmDiff n S T x

/-- Sum of a single Walsh character over the whole cube. -/
lemma sum_chi_apply {n : ℕ} (A : Finset (Fin n)) :
    (∑ x : Fin n → ZMod 2, chi A x) = if A = ∅ then (2 : ℂ) ^ n else 0 := by
  have h : (∑ x : Fin n → ZMod 2, chi A x)
      = ∑ x : Fin n → ZMod 2, ∏ i : Fin n, (if i ∈ A then ZMod.stdAddChar (x i) else 1) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [chi, (Finset.prod_ite_mem_eq A (fun i => ZMod.stdAddChar (x i))).symm]
  rw [h, sum_coord_chi]
  simp

/-- Two Finsets are equal iff the union of their set differences is empty. -/
lemma sdiff_union_eq_empty_iff {α : Type*} [DecidableEq α] (S T : Finset α) :
    (S \ T) ∪ (T \ S) = ∅ ↔ S = T := by
  constructor
  · intro h
    ext i
    constructor
    · intro hi
      by_contra hni
      have hm : i ∈ (S \ T) ∪ (T \ S) := by simp [hi, hni]
      rw [h] at hm; simp at hm
    · intro hi
      by_contra hni
      have hm : i ∈ (S \ T) ∪ (T \ S) := by simp [hi, hni]
      rw [h] at hm; simp at hm
  · intro h; subst h; simp

/-- Orthogonality of the Walsh characters. -/
lemma chi_orthogonal {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Fin n → ZMod 2, chi S x * chi T x)
      = if S = T then (2 : ℂ) ^ n else 0 := by
  rw [Finset.sum_congr rfl (fun x _ => chi_mul S T x), sum_chi_apply]
  by_cases h : S = T
  · subst h; simp
  · have hne : (S \ T) ∪ (T \ S) ≠ ∅ := fun hh => h ((sdiff_union_eq_empty_iff S T).mp hh)
    rw [if_neg hne, if_neg h]

theorem sum_norm_sq_chi_orthogonal {n : ℕ} (s : Finset (Finset (Fin n))) (a : Finset (Fin n) → ℂ) :
    (∑ x : Fin n → ZMod 2, ‖∑ S ∈ s, a S * ∏ i ∈ S, ZMod.stdAddChar (x i)‖ ^ 2)
      = (2 : ℝ) ^ n * ∑ S ∈ s, ‖a S‖ ^ 2 := by
  classical
  have key : (∑ x : Fin n → ZMod 2, ‖∑ S ∈ s, a S * chi S x‖ ^ 2)
      = (2 : ℝ) ^ n * ∑ S ∈ s, ‖a S‖ ^ 2 := by
    have hsq : ∀ z : ℂ, (Complex.normSq z : ℂ) = z * (starRingEnd ℂ) z :=
      fun z => (Complex.mul_conj z).symm
    have hcomplex :
        (∑ x : Fin n → ZMod 2, (Complex.normSq (∑ S ∈ s, a S * chi S x) : ℂ))
          = (2 : ℂ) ^ n * ∑ S ∈ s, (Complex.normSq (a S) : ℂ) := by
      have hstar : ∀ x : Fin n → ZMod 2,
          (starRingEnd ℂ) (∑ S ∈ s, a S * chi S x) = ∑ T ∈ s, (starRingEnd ℂ) (a T) * chi T x := by
        intro x
        rw [map_sum]
        exact Finset.sum_congr rfl fun T _ => by rw [map_mul, star_chi]
      have hexpand : ∀ x : Fin n → ZMod 2,
          (∑ S ∈ s, a S * chi S x) * (starRingEnd ℂ) (∑ S ∈ s, a S * chi S x)
            = ∑ S ∈ s, ∑ T ∈ s, a S * (starRingEnd ℂ) (a T) * chi ((S \ T) ∪ (T \ S)) x := by
        intro x
        rw [hstar x, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => by
          rw [show a S * chi S x * ((starRingEnd ℂ) (a T) * chi T x)
              = a S * (starRingEnd ℂ) (a T) * (chi S x * chi T x) by ring, chi_mul]
      rw [Finset.sum_congr rfl (fun x _ => hsq _),
          Finset.sum_congr rfl (fun S _ => hsq _)]
      rw [Finset.sum_congr rfl (fun x _ => hexpand x)]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun S _ => Finset.sum_comm)]
      simp_rw [← Finset.mul_sum]
      simp only [sum_chi_apply, sdiff_union_eq_empty_iff]
      have hinner : ∀ S ∈ s,
          (∑ T ∈ s, a S * (starRingEnd ℂ) (a T) * (if S = T then (2 : ℂ) ^ n else 0))
            = a S * (starRingEnd ℂ) (a S) * (2 : ℂ) ^ n := by
        intro S hS
        rw [Finset.sum_eq_single S]
        · rw [if_pos rfl]
        · intro T _ hTS
          rw [if_neg (Ne.symm hTS), mul_zero]
        · intro hS'; exact absurd hS hS'
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, mul_comm]
    have hreal : (∑ x : Fin n → ZMod 2, Complex.normSq (∑ S ∈ s, a S * chi S x))
        = (2 : ℝ) ^ n * ∑ S ∈ s, Complex.normSq (a S) := by
      apply Complex.ofReal_inj.mp
      rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum,
        Complex.ofReal_ofNat]
      simpa using hcomplex
    calc (∑ x : Fin n → ZMod 2, ‖∑ S ∈ s, a S * chi S x‖ ^ 2)
        = ∑ x : Fin n → ZMod 2, Complex.normSq (∑ S ∈ s, a S * chi S x) :=
          Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_norm_sq _).symm
      _ = (2 : ℝ) ^ n * ∑ S ∈ s, Complex.normSq (a S) := hreal
      _ = (2 : ℝ) ^ n * ∑ S ∈ s, ‖a S‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun S _ => Complex.normSq_eq_norm_sq (a S)
  simpa only [chi] using key

end

end Commons.Analysis.Walsh