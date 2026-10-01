import Mathlib

namespace Work.ZeroDensity.Zeta.balAux

open Finset

/-- The reciprocal sum over `Icc 1 N` is invariant under the reflection `n ↦ N + 1 - n`. -/
lemma sum_Icc_recip_reflect (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/((N+1-n : ℕ):ℝ) = ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ) := by
  refine Finset.sum_nbij' (fun n => N+1-n) (fun n => N+1-n) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; rfl

/-- The real reciprocal sum over `Icc 1 N` is the `N`-th harmonic number. -/
lemma sum_one_div_eq_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Rat.cast_inv, one_div]

theorem harmMain (y : ℝ) (hy : 3 ≤ y) :
    ∑ n ∈ Finset.Icc 1 (⌊y⌋₊ - 1), (1 : ℝ) / ((n : ℝ) * (y - (n : ℝ))) ≤
      4 * (Real.log y + 1) / y := by
  set N : ℕ := ⌊y⌋₊ - 1 with hN
  have hy0 : (0:ℝ) < y := by linarith
  have hfloor3 : 3 ≤ ⌊y⌋₊ := Nat.le_floor (show (3:ℝ) ≤ y from hy)
  have hN1 : N + 1 = ⌊y⌋₊ := by omega
  have hNy : (N:ℝ) + 1 ≤ y := by
    have hthis : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    rw [← hN1] at hthis; push_cast at hthis; linarith
  -- partial fractions: `1/(n(y-n)) = (1/y) * (1/n + 1/(y-n))`
  have hdecomp : ∀ n ∈ Finset.Icc 1 N,
      (1:ℝ)/((n:ℝ)*(y-(n:ℝ))) = (1/y)*((1:ℝ)/(n:ℝ) + (1:ℝ)/(y-(n:ℝ))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnN⟩ := hn
    have hnne : (n:ℝ) ≠ 0 := by positivity
    have hnle : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
    have hynne : y - (n:ℝ) ≠ 0 := by linarith
    have hyne : y ≠ 0 := by linarith
    field_simp
    ring
  have hsum_decomp :
      ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/((n:ℝ)*(y-(n:ℝ)))
        = (1/y) * ∑ n ∈ Finset.Icc 1 N, ((1:ℝ)/(n:ℝ) + (1:ℝ)/(y-(n:ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hdecomp
  have hsum_split :
      ∑ n ∈ Finset.Icc 1 N, ((1:ℝ)/(n:ℝ) + (1:ℝ)/(y-(n:ℝ)))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) + ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(y-(n:ℝ)) :=
    Finset.sum_add_distrib
  -- the second sum is dominated by the harmonic sum, by reflection `n ↦ N+1-n`
  have hT_le : ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(y-(n:ℝ)) ≤ ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ) := by
    calc ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(y-(n:ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/((N+1-n:ℕ):ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          obtain ⟨hn1, hnN⟩ := hn
          have hnN1 : n ≤ N + 1 := by omega
          have hcast : ((N+1-n:ℕ):ℝ) = (N:ℝ) + 1 - (n:ℝ) := by
            rw [Nat.cast_sub hnN1, Nat.cast_add, Nat.cast_one]
          have hpos : (0:ℝ) < ((N+1-n:ℕ):ℝ) := by
            have : (0:ℕ) < N+1-n := by omega
            exact_mod_cast this
          have hle : ((N+1-n:ℕ):ℝ) ≤ y - (n:ℝ) := by rw [hcast]; linarith
          exact one_div_le_one_div_of_le hpos hle
      _ = ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ) := sum_Icc_recip_reflect N
  have hSval : ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ) = (harmonic N : ℝ) := sum_one_div_eq_harmonic N
  have hHle : (harmonic N : ℝ) ≤ 1 + Real.log y := by
    refine (harmonic_le_one_add_log N).trans ?_
    have hx : (0:ℝ) < (N:ℝ) := by
      have : (0:ℕ) < N := by omega
      exact_mod_cast this
    have hxy : (N:ℝ) ≤ y := by linarith
    have := Real.log_le_log hx hxy
    linarith
  have hTle : ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(y-(n:ℝ)) ≤ (harmonic N:ℝ) := hT_le.trans hSval.le
  calc ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/((n:ℝ)*(y-(n:ℝ)))
      = (1/y) * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) + ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(y-(n:ℝ))) := by
          rw [hsum_decomp, hsum_split]
    _ ≤ (1/y) * ((harmonic N : ℝ) + (harmonic N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (le_of_lt hy0))
          linarith [hSval.le, hTle]
    _ = 2 * (harmonic N : ℝ) / y := by ring
    _ ≤ 2 * (1 + Real.log y) / y := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hy0)
          linarith
    _ ≤ 4 * (Real.log y + 1) / y := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hy0)
          nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ y)]

end Work.ZeroDensity.Zeta.balAux
