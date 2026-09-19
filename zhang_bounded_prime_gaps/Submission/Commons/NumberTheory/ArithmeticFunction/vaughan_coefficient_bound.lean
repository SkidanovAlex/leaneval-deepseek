import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le

namespace Commons.NumberTheory.ArithmeticFunction

open scoped BigOperators

/-- Pointwise bound: the norm of a single Vaughan summand is at most `Λ k`. -/
private lemma vaughan_norm_term_le (kl : ℕ × ℕ) :
    ‖((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
        * ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)‖
      ≤ ArithmeticFunction.vonMangoldt kl.1 := by
  rw [norm_mul, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hmu : |((ArithmeticFunction.moebius kl.2 : ℤ) : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := kl.2)
    exact_mod_cast h
  calc ArithmeticFunction.vonMangoldt kl.1
        * |((ArithmeticFunction.moebius kl.2 : ℤ) : ℝ)|
      ≤ ArithmeticFunction.vonMangoldt kl.1 * 1 :=
        mul_le_mul_of_nonneg_left hmu ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt kl.1 := mul_one _

/-- The Vaughan coefficient `c m = Σ_{k l = m, k ≤ u, l ≤ v} Λ(k) μ(l)` is bounded by
`log m`, because `|Σ_{k | m} Λ(k)| = log m`. -/
theorem vaughan_coefficient_bound (u v m : ℕ) :
    ‖∑ kl ∈ (Finset.Icc 1 u ×ˢ Finset.Icc 1 v).filter (fun kl => kl.1 * kl.2 = m),
        ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
          * ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)‖
      ≤ max 0 (Real.log (m : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hempty :
        (Finset.Icc 1 u ×ˢ Finset.Icc 1 v).filter (fun kl => kl.1 * kl.2 = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro kl hkl hcon
      simp only [Finset.mem_product, Finset.mem_Icc] at hkl
      obtain ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ := hkl
      have hpos : 0 < kl.1 * kl.2 := Nat.mul_pos (by omega) (by omega)
      omega
    rw [hempty]
    simp
  · set S : Finset (ℕ × ℕ) :=
      (Finset.Icc 1 u ×ˢ Finset.Icc 1 v).filter (fun kl => kl.1 * kl.2 = m) with hS
    set f : ℕ × ℕ → ℂ := fun kl =>
      ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
        * ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) with hf
    have hInj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, hS] at ha hb
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha hb
      obtain ⟨⟨⟨ha1, _⟩, _⟩, ha2⟩ := ha
      obtain ⟨⟨⟨_, _⟩, _⟩, hb2⟩ := hb
      have h1 : a.1 * a.2 = a.1 * b.2 := by rw [ha2, ← hb2, hab]
      have h2 : a.2 = b.2 := Nat.mul_left_cancel (by omega) h1
      exact Prod.ext hab h2
    have hSub : S.image Prod.fst ⊆ m.divisors := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨kl, hkl, hkfst⟩ := hk
      subst hkfst
      rw [Nat.mem_divisors]
      rw [hS] at hkl
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hkl
      obtain ⟨⟨⟨_, _⟩, _⟩, hklm⟩ := hkl
      exact ⟨⟨kl.2, hklm.symm⟩, hm.ne'⟩
    calc ‖∑ kl ∈ S, f kl‖
        ≤ ∑ kl ∈ S, ‖f kl‖ := norm_sum_le S f
      _ ≤ ∑ kl ∈ S, ArithmeticFunction.vonMangoldt kl.1 :=
          Finset.sum_le_sum (fun kl _ => vaughan_norm_term_le kl)
      _ = ∑ k ∈ S.image Prod.fst, ArithmeticFunction.vonMangoldt k :=
          (Finset.sum_image hInj).symm
      _ ≤ ∑ k ∈ m.divisors, ArithmeticFunction.vonMangoldt k :=
          Finset.sum_le_sum_of_subset_of_nonneg hSub
            (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Real.log (m : ℝ) := ArithmeticFunction.vonMangoldt_sum
      _ ≤ max 0 (Real.log (m : ℝ)) := le_max_right _ _

end Commons.NumberTheory.ArithmeticFunction