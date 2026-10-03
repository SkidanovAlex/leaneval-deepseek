import Mathlib
import Submission.Work.FIArea4.A4c.Defs

namespace Work.FIArea4.A4c

/-- **The `N`-multiple of the §15 bracket is absorbed by `X^{-1/3}N²`.**

With `S15Br6 Pa X = X^{-1/2}N + N^{1/3}X^{-1/3}N^{2/3} + N^{23/24+1/1000}` and `1 ≤ X ≤ N^{1/9}`,

  `Pa.N * S15Br6 Pa X ≤ 3·X^{-1/3}·N²`.

Each of the three summands of `N·S15Br6` is at most `X^{-1/3}N²`:
* `N·(X^{-1/2}N) = X^{-1/2}N² ≤ X^{-1/3}N²`, because `X^{-1/2} ≤ X^{-1/3}` for `X ≥ 1`;
* `N·(N^{1/3}X^{-1/3}N^{2/3}) = X^{-1/3}N²` exactly (`1/3 + 2/3 = 1`);
* `N·N^{23/24+1/1000} = N^{2939/1500} ≤ X^{-1/3}N²`: indeed
  `X^{1/3} ≤ (N^{1/9})^{1/3} = N^{1/27} ≤ N^{61/1500}` (as `1/27 < 61/1500 = 2 − 2939/1500`),
  and inverting (both bases are positive) gives `N^{-61/1500} ≤ X^{-1/3}`, so that
  `N^{2939/1500} = N²·N^{-61/1500} ≤ X^{-1/3}N²`. -/
theorem N_mul_S15Br6_le (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X)
    (hX9 : (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9)) :
    Pa.N * Work.FIArea4.S15Br6 Pa X ≤ 3 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  -- ### `X^{1/3} ≤ N^{61/1500}`, hence (inverting) `N^{-61/1500} ≤ X^{-1/3}`
  have hX13 : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ Pa.N ^ ((61 : ℝ) / 1500) := by
    calc (X : ℝ) ^ ((1 : ℝ) / 3)
        ≤ (Pa.N ^ ((1 : ℝ) / 9)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hX0 hX9 (by norm_num)
      _ = Pa.N ^ ((1 : ℝ) / 27) := by
          rw [← Real.rpow_mul hNpos.le,
            show (1 : ℝ) / 9 * ((1 : ℝ) / 3) = (1 : ℝ) / 27 by norm_num]
      _ ≤ Pa.N ^ ((61 : ℝ) / 1500) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hNinv_le : (Pa.N ^ ((61 : ℝ) / 1500))⁻¹ ≤ ((X : ℝ) ^ ((1 : ℝ) / 3))⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hXpos _)).mpr hX13
  have hAinv : Pa.N ^ (-(61 : ℝ) / 1500) ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) := by
    have e1 : Pa.N ^ (-(61 : ℝ) / 1500) = (Pa.N ^ ((61 : ℝ) / 1500))⁻¹ := by
      rw [show (-(61 : ℝ) / 1500) = -((61 : ℝ) / 1500) by ring, Real.rpow_neg hNpos.le]
    have e2 : (X : ℝ) ^ (-(1 : ℝ) / 3) = ((X : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
      rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg hX0]
    rw [e1, e2]
    exact hNinv_le
  -- ### The three summands of `N * S15Br6`, each at most `X^{-1/3}N²`
  have key1 : (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N * Pa.N
      ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    have h1 : (X : ℝ) ^ (-(1 : ℝ) / 2) ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    calc (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N * Pa.N
        = ((X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N) * Pa.N := by ring
      _ ≤ ((X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N) * Pa.N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hNpos.le) hNpos.le
      _ ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := le_of_eq (by ring)
  have key2 : Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * Pa.N
      = (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    have h1 : Pa.N ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) = Pa.N := by
      rw [← Real.rpow_add hNpos, show (1 : ℝ) / 3 + (2 : ℝ) / 3 = 1 by norm_num, Real.rpow_one]
    calc Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * Pa.N
        = (X : ℝ) ^ (-(1 : ℝ) / 3)
            * ((Pa.N ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3)) * Pa.N) := by ring
      _ = (X : ℝ) ^ (-(1 : ℝ) / 3) * (Pa.N * Pa.N) := by rw [h1]
      _ = (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by ring
  have key3 : Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) * Pa.N
      ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    have hA : Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) * Pa.N
        = Pa.N ^ ((2939 : ℝ) / 1500) := by
      have h := Real.rpow_add hNpos ((23 : ℝ) / 24 + (1 : ℝ) / 1000) (1 : ℝ)
      rw [Real.rpow_one] at h
      rw [show (23 : ℝ) / 24 + (1 : ℝ) / 1000 + (1 : ℝ) = (2939 : ℝ) / 1500
        by norm_num] at h
      exact h.symm
    rw [hA]
    calc Pa.N ^ ((2939 : ℝ) / 1500)
        = Pa.N ^ (2 : ℝ) * Pa.N ^ (-(61 : ℝ) / 1500) := by
          have h := Real.rpow_add hNpos (2 : ℝ) (-(61 : ℝ) / 1500)
          rw [show (2 : ℝ) + (-(61 : ℝ) / 1500) = (2939 : ℝ) / 1500 by norm_num] at h
          exact h
      _ ≤ Pa.N ^ (2 : ℝ) * (X : ℝ) ^ (-(1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hAinv (by positivity)
      _ ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
          rw [mul_comm (Pa.N ^ (2 : ℝ)) ((X : ℝ) ^ (-(1 : ℝ) / 3))]
          exact mul_le_mul_of_nonneg_left (le_of_eq (Real.rpow_natCast Pa.N 2))
            (by positivity)
  -- ### Assembly
  calc Pa.N * Work.FIArea4.S15Br6 Pa X
      = (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N * Pa.N
        + Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * Pa.N
        + Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) * Pa.N := by
        unfold Work.FIArea4.S15Br6
        ring
    _ ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2
        + (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2
        + (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
        linarith [key1, key2, key3]
    _ ≤ 3 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := le_of_eq (by ring)

end Work.FIArea4.A4c
