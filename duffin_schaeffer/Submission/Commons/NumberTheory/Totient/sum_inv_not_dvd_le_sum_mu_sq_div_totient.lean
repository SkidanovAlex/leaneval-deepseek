import Mathlib
import Submission.Commons.NumberTheory.Nat.radical_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Totient.smooth_inv_sum_le_totient_ratio

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Totient

open Commons.NumberTheory.Nat

/-- Reciprocal mass of a set all of whose elements have radical `r` is bounded by
`1/φ(r)`: writing each `n = r · m`, the `m` are `r`-smooth numbers, and the
reciprocal sum over the `r`-smooth numbers up to `Y` is at most `r/φ(r)` by the
Euler product. -/
private lemma fiber_bound (r Y : ℕ) (F : Finset ℕ) (hr : 1 ≤ r)
    (hF1 : ∀ n ∈ F, 1 ≤ n) (hrad : ∀ n ∈ F, radical n = r) (hY : ∀ n ∈ F, n ≤ Y) :
    (∑ n ∈ F, (1 : ℝ) / n) ≤ 1 / (Nat.totient r : ℝ) := by
  classical
  set W : Finset ℕ := F.image (fun n => n / r) with hW
  -- `1/n = (1/r) · 1/(n/r)` for every `n ∈ F`.
  have hterm : ∀ n ∈ F, (1 : ℝ) / n = (1 / (r : ℝ)) * (1 / (((n / r : ℕ)) : ℝ)) := by
    intro n hn
    have hdvd : r ∣ n := by rw [← hrad n hn]; exact radical_dvd n
    have hnd : r * (n / r) = n := Nat.mul_div_cancel' hdvd
    have hcast : (n : ℝ) = (r : ℝ) * (((n / r : ℕ)) : ℝ) := by
      rw [← Nat.cast_mul, hnd]
    rw [hcast, one_div, mul_inv]
    simp only [one_div]
  -- `n ↦ n/r` is injective on `F`.
  have hinj : Set.InjOn (fun n => n / r) (↑F : Set ℕ) := by
    intro a ha b hb hab
    have hda : r * (a / r) = a := Nat.mul_div_cancel' (by rw [← hrad a ha]; exact radical_dvd a)
    have hdb : r * (b / r) = b := Nat.mul_div_cancel' (by rw [← hrad b hb]; exact radical_dvd b)
    have h : a / r = b / r := hab
    rw [← hda, ← hdb, h]
  have hWsum : (∑ m ∈ W, (1 / (m : ℝ))) = ∑ n ∈ F, (1 / (((n / r : ℕ)) : ℝ)) := by
    rw [hW]; exact Finset.sum_image hinj
  have hdecomp : (∑ n ∈ F, (1 : ℝ) / n) = (1 / (r : ℝ)) * ∑ m ∈ W, (1 / (m : ℝ)) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hWsum]
  -- The `m = n/r` form an `r`-smooth set inside the box `Icc 1 Y`.
  have hsub : W ⊆ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors) := by
    intro m hm
    rw [hW, Finset.mem_image] at hm
    obtain ⟨n, hnF, rfl⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hdvd : r ∣ n := by rw [← hrad n hnF]; exact radical_dvd n
    have hn1 : 1 ≤ n := hF1 n hnF
    have hn0 : n ≠ 0 := by omega
    have hrle : r ≤ n := by rw [← hrad n hnF]; exact radical_le_self hn0
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_pos hrle (by omega)
    · exact le_trans (Nat.div_le_self n r) (hY n hnF)
    · have hpr : r.primeFactors = n.primeFactors := by
        rw [← hrad n hnF]; exact primeFactors_radical n
      rw [hpr]
      exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdvd) hn0
  have hle : (∑ m ∈ W, (1 / (m : ℝ)))
      ≤ ∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors), (1 / (m : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
  calc (∑ n ∈ F, (1 : ℝ) / n)
      = (1 / (r : ℝ)) * ∑ m ∈ W, (1 / (m : ℝ)) := hdecomp
    _ ≤ (1 / (r : ℝ)) * ∑ m ∈ (Finset.Icc 1 Y).filter
            (fun m => m.primeFactors ⊆ r.primeFactors), (1 / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ (1 / (r : ℝ)) * ((r : ℝ) / (Nat.totient r : ℝ)) :=
          mul_le_mul_of_nonneg_left (smooth_inv_sum_le_totient_ratio r Y hr) (by positivity)
    _ = 1 / (Nat.totient r : ℝ) := by
          have hrne : (r : ℝ) ≠ 0 := by positivity
          field_simp

theorem sum_inv_not_dvd_le_sum_mu_sq_div_totient (Y : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ∀ p ∈ S, ¬ p ∣ n), (1 : ℝ) / n)
      ≤ ∑ r ∈ (Finset.Icc 1 Y).filter (fun r => ∀ p ∈ S, ¬ p ∣ r),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
  classical
  set A : Finset ℕ := (Finset.Icc 1 Y).filter (fun n => ∀ p ∈ S, ¬ p ∣ n) with hA
  have hmemA : ∀ n ∈ A, 1 ≤ n ∧ n ≤ Y ∧ (∀ p ∈ S, ¬ p ∣ n) := by
    intro n hn
    rw [hA] at hn
    obtain ⟨hnIcc, hnS⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp hnIcc
    exact ⟨hn1, hnY, hnS⟩
  -- Bound every `radical`-fibre of `A` by `μ(r)²/φ(r)`.
  have key : ∀ r ∈ A.image radical,
      (∑ n ∈ A.filter (fun n => radical n = r), (1 : ℝ) / n)
        ≤ ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
    intro r hr
    obtain ⟨n0, hn0A, hn0r⟩ := Finset.mem_image.mp hr
    have hn0_0 : n0 ≠ 0 := by have := (hmemA n0 hn0A).1; omega
    have hr1 : 1 ≤ r := by rw [← hn0r]; exact Nat.one_le_iff_ne_zero.mpr (radical_ne_zero n0)
    have hsq : Squarefree r := by rw [← hn0r]; exact radical_squarefree n0
    have hfib : (∑ n ∈ A.filter (fun n => radical n = r), (1 : ℝ) / n)
        ≤ 1 / (Nat.totient r : ℝ) := by
      refine fiber_bound r Y (A.filter (fun n => radical n = r)) hr1 ?_ ?_ ?_
      · intro n hn; exact (hmemA n (Finset.mem_filter.mp hn).1).1
      · intro n hn; exact (Finset.mem_filter.mp hn).2
      · intro n hn; exact (hmemA n (Finset.mem_filter.mp hn).1).2.1
    have hmu : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
      norm_num
    rw [hmu]
    exact hfib
  calc (∑ n ∈ A, (1 : ℝ) / n)
      = ∑ r ∈ A.image radical, ∑ n ∈ A.filter (fun n => radical n = r), (1 : ℝ) / n :=
        (Finset.sum_fiberwise_of_maps_to
          (fun n hn => Finset.mem_image_of_mem radical hn) (fun n => (1 : ℝ) / n)).symm
    _ ≤ ∑ r ∈ A.image radical,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) :=
        Finset.sum_le_sum key
    _ ≤ ∑ r ∈ A,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          obtain ⟨n, hnA, hnr⟩ := Finset.mem_image.mp hr
          obtain ⟨hn1, hnY, hnS⟩ := hmemA n hnA
          have hn0 : n ≠ 0 := by omega
          rw [hA, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [← hnr]; exact Nat.one_le_iff_ne_zero.mpr (radical_ne_zero n)
          · rw [← hnr]; exact le_trans (radical_le_self hn0) hnY
          · rw [← hnr]
            intro p hpS hpr
            exact hnS p hpS (dvd_trans hpr (radical_dvd n))
        · intro r _ _
          apply div_nonneg
          · positivity
          · positivity

end Commons.NumberTheory.Totient
