import Mathlib

namespace Work.FIArea6Hecke.R

open Matrix

/-- For `x : Fin 2 → ℤ`, the square of the sup-norm (which is the norm of `Fin 2 → ℤ`)
is bounded by the sum of the squares of the two coordinates. -/
private lemma norm_sq_le_sum_sq (x : Fin 2 → ℤ) :
    (‖x‖ : ℝ) ^ 2 ≤ (x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2 := by
  rw [EisensteinSeries.norm_eq_max_natAbs, Nat.cast_max]
  have h0 : ((x 0).natAbs : ℝ) = |(x 0 : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h1 : ((x 1).natAbs : ℝ) = |(x 1 : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h0, h1]
  rcases max_choice |(x 0 : ℝ)| |(x 1 : ℝ)| with h | h
  · rw [h, sq_abs]; nlinarith [sq_nonneg (x 1 : ℝ)]
  · rw [h, sq_abs]; nlinarith [sq_nonneg (x 0 : ℝ)]

theorem latticeCubic_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ℤ × ℤ => (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-σ))) := by
  -- The Eisenstein-series summability lemma gives summability of `‖x‖^(-k)` on `ℤ²` for `k > 2`.
  have hnorm : Summable (fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ))) :=
    EisensteinSeries.summable_one_div_norm_rpow (k := 2 * σ) (by linarith)
  -- Compare `(x₀² + x₁²)^(-σ)` with the summable sup-norm function.
  have hmain : Summable (fun x : Fin 2 → ℤ => ((x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (f := fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)))
      (fun x => Real.rpow_nonneg (by positivity) _) (fun x => ?_) hnorm
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      simp only [Pi.zero_apply, Int.cast_zero, norm_zero]
      norm_num
      rw [Real.zero_rpow (by linarith : (-σ : ℝ) ≠ 0),
          Real.zero_rpow (by linarith : (-(2 * σ) : ℝ) ≠ 0)]
    · -- `x ≠ 0` gives `‖x‖ > 0`; the sup-norm squared is at most the Euclidean square.
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hle := Real.rpow_le_rpow_of_nonpos (pow_pos hn 2) (norm_sq_le_sum_sq x)
        (by linarith : (-σ : ℝ) ≤ 0)
      have h2 : ((‖x‖ : ℝ) ^ 2) ^ (-σ) = ‖x‖ ^ (-(2 * σ)) := by
        rw [← Real.rpow_natCast (‖x‖) 2, ← Real.rpow_mul (norm_nonneg x)]
        congr 1; ring
      rwa [h2] at hle
  -- Transport the summability from `Fin 2 → ℤ` to `ℤ × ℤ`.
  have htransfer : Summable ((fun x : Fin 2 → ℤ => ((x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2) ^ (-σ))
      ∘ (finTwoArrowEquiv ℤ).symm) :=
    (Equiv.summable_iff (f := fun x : Fin 2 → ℤ => ((x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2) ^ (-σ))
      (finTwoArrowEquiv ℤ).symm).mpr hmain
  simpa [Function.comp_def, finTwoArrowEquiv] using htransfer

end Work.FIArea6Hecke.R
