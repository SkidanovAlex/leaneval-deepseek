import Mathlib
import Submission.Work.FIArea7.hyperbolaBlockAux

namespace Work.FIArea7.smallCInner2EpsAux

open Finset MeasureTheory
open scoped BigOperators

lemma hypBlock_le_eps (psi : GaussianInt → ℂ) (c0 a M N u : ℕ) (hM : 1 ≤ M) (hu : 1 ≤ u)
    (α β : ℕ → ℂ)
    (hα : ∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1)
    (hβ : ∀ n ∈ Finset.Icc 1 N, ‖β n‖ ≤ 1)
    (C1 eps : ℝ) (hC1 : 0 < C1) (heps : 0 < eps)
    (hbound : ∀ (Ma Ca : ℕ) (γ δ : ℕ → ℂ), 1 ≤ Ma → 1 ≤ Ca →
      (∀ m ∈ Finset.Icc 1 Ma, ‖γ m‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 Ca, ‖δ n‖ ≤ 1) →
      ‖LBilin Ma Ca c0 psi γ δ‖
        ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * ((Ma : ℝ) + Ca) ^ ((1 : ℝ) / 12)
            * ((Ma : ℝ) * Ca) ^ ((11 : ℝ) / 12)
            * (((Ma : ℝ) * Ca + (c0 : ℝ) + 2) ^ eps))
    (h : ℝ → ℝ)
    (hspec : ∀ k : ℕ, 1 ≤ k →
      (∫ t : ℝ, (h t : ℂ) * (k : ℂ) ^ (t * Complex.I)) = if (k : ℝ) ≤ (u : ℝ) then 1 else 0) :
    ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then α m * β n * quadEigen psi (c0 * m * n) else 0)‖
      ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
          * (((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps)) * ∫ t : ℝ, |h t| := by
  have hτnn : (0 : ℝ) ≤ ((c0.divisors.card : ℕ) : ℝ) := by positivity
  -- the product side of the cut rectangle is at most `2u`
  have hMaCa : (min (2 ^ (a + 1) - 1) M) * (min N (u / 2 ^ a)) ≤ 2 * u := by
    have hMa2 : min (2 ^ (a + 1) - 1) M ≤ 2 ^ (a + 1) :=
      le_trans (min_le_left _ _) (Nat.sub_le _ _)
    have hCa2 : min N (u / 2 ^ a) * 2 ^ a ≤ u :=
      le_trans (Nat.mul_le_mul_right _ (min_le_right _ _)) (Nat.div_mul_le_self u (2 ^ a))
    calc (min (2 ^ (a + 1) - 1) M) * (min N (u / 2 ^ a))
        ≤ 2 ^ (a + 1) * (min N (u / 2 ^ a)) := Nat.mul_le_mul_right _ hMa2
      _ = 2 * (min N (u / 2 ^ a) * 2 ^ a) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 * u := Nat.mul_le_mul_left _ hCa2
  have hMaCaR : (((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) * ((min N (u / 2 ^ a) : ℕ) : ℝ))
      ≤ 2 * (u : ℝ) := by exact_mod_cast hMaCa
  have hSum : (((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) + ((min N (u / 2 ^ a) : ℕ) : ℝ))
      ≤ (M : ℝ) + N := by
    have h1 : ((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast min_le_right (2 ^ (a + 1) - 1) M
    have h2 : ((min N (u / 2 ^ a) : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast min_le_left N (u / 2 ^ a)
    linarith
  -- the rectangular bound for the cut rectangle
  set B : ℝ := C1 * ((c0.divisors.card : ℕ) : ℝ)
      * (((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) + ((min N (u / 2 ^ a) : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
      * ((((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) * ((min N (u / 2 ^ a) : ℕ) : ℝ)) ^ ((11 : ℝ) / 12))
      * (((((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) * ((min N (u / 2 ^ a) : ℕ) : ℝ)) + (c0 : ℝ) + 2) ^ eps)
      with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) hτnn)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)
  have hkey : ∀ t : ℝ, ‖LBilin (min (2 ^ (a + 1) - 1) M) (min N (u / 2 ^ a)) c0 psi
      (fun m => (if 2 ^ a ≤ m then α m else 0) * (m : ℂ) ^ (t * Complex.I))
      (fun n => β n * (n : ℂ) ^ (t * Complex.I))‖ ≤ B := by
    intro t
    rw [hBdef]
    by_cases hC : 1 ≤ min N (u / 2 ^ a)
    · have hMa1 : 1 ≤ min (2 ^ (a + 1) - 1) M := by
        have hp : 2 ≤ 2 ^ (a + 1) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ a + 1)
          simpa using this
        exact le_min (by omega) hM
      have hγ : ∀ m ∈ Finset.Icc 1 (min (2 ^ (a + 1) - 1) M),
          ‖(if 2 ^ a ≤ m then α m else 0) * (m : ℂ) ^ (t * Complex.I)‖ ≤ 1 := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        rw [norm_mul, norm_natCast_cpow_I m hm.1 t, mul_one]
        by_cases h2a : 2 ^ a ≤ m
        · rw [if_pos h2a]
          exact hα m (Finset.mem_Icc.mpr ⟨hm.1, le_trans hm.2 (min_le_right _ _)⟩)
        · rw [if_neg h2a, norm_zero]; norm_num
      have hδ : ∀ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
          ‖β n * (n : ℂ) ^ (t * Complex.I)‖ ≤ 1 := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [norm_mul, norm_natCast_cpow_I n hn.1 t, mul_one]
        exact hβ n (Finset.mem_Icc.mpr ⟨hn.1, le_trans hn.2 (min_le_left _ _)⟩)
      exact hbound (min (2 ^ (a + 1) - 1) M) (min N (u / 2 ^ a))
        (fun m => (if 2 ^ a ≤ m then α m else 0) * (m : ℂ) ^ (t * Complex.I))
        (fun n => β n * (n : ℂ) ^ (t * Complex.I)) hMa1 hC hγ hδ
    · have hC0 : min N (u / 2 ^ a) = 0 := by
        by_contra hcon
        exact hC (Nat.one_le_iff_ne_zero.mpr hcon)
      have hz : LBilin (min (2 ^ (a + 1) - 1) M) (min N (u / 2 ^ a)) c0 psi
          (fun m => (if 2 ^ a ≤ m then α m else 0) * (m : ℂ) ^ (t * Complex.I))
          (fun n => β n * (n : ℂ) ^ (t * Complex.I)) = 0 := by
        rw [hC0]; simp [LBilin]
      rw [hz, norm_zero, ← hBdef]; exact hBnn
  -- the rectangle is dominated by the target bound
  have hBleT : B ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
      * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
      * (((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps)) := by
    rw [hBdef]
    have h1 : (((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) + ((min N (u / 2 ^ a) : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
        ≤ ((M : ℝ) + N) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by positivity) hSum (by norm_num)
    have h2 : (((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) * ((min N (u / 2 ^ a) : ℕ) : ℝ)) ^ ((11 : ℝ) / 12)
        ≤ (2 * (u : ℝ)) ^ ((11 : ℝ) / 12) :=
      Real.rpow_le_rpow (by positivity) hMaCaR (by norm_num)
    have h3 : ((((min (2 ^ (a + 1) - 1) M : ℕ) : ℝ) * ((min N (u / 2 ^ a) : ℕ) : ℝ)) + (c0 : ℝ) + 2) ^ eps
        ≤ (2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps :=
      Real.rpow_le_rpow (by positivity) (by linarith [hMaCaR]) (le_of_lt heps)
    apply mul_le_mul
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt hC1) hτnn)
      · exact h2
      · exact Real.rpow_nonneg (by positivity) _
      · exact mul_nonneg (mul_nonneg (le_of_lt hC1) hτnn) (Real.rpow_nonneg (by positivity) _)
    · exact h3
    · exact Real.rpow_nonneg (by positivity) _
    · exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) hτnn)
        (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hIntnn : 0 ≤ ∫ t : ℝ, |h t| := MeasureTheory.integral_nonneg (f := fun t => |h t|) (fun t => abs_nonneg (h t))
  rw [show (∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then α m * β n * quadEigen psi (c0 * m * n) else 0))
      = (∑ m ∈ Finset.Icc 1 (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
        (if m * n ≤ u then (if 2 ^ a ≤ m then α m else 0) * β n
          * quadEigen psi (c0 * m * n) else 0)) from
    hyperbola_block_rewrite a M N u α β (fun m n => quadEigen psi (c0 * m * n))]
  exact le_trans (hyperbola_block_le h u hu hspec (min (2 ^ (a + 1) - 1) M)
    (min N (u / 2 ^ a)) c0 psi (fun m => if 2 ^ a ≤ m then α m else 0) β B hBnn hkey)
    (mul_le_mul_of_nonneg_right hBleT hIntnn)

end Work.FIArea7.smallCInner2EpsAux
