/-
# Summability of the integer translates of a Schwartz function

For a Schwartz function `φ : ℝ → ℂ` and a shift `x : ℝ`, the series
`∑_{k : ℤ} ‖φ (x + k)‖` converges.  The two ingredients are

* the Schwartz decay bound `‖φ y‖ ≤ C / |y| ^ 2` for `|y| ≥ 1` (a single Schwartz seminorm
  controls it), and
* the summability of the shifted `p`-series `∑_{k : ℤ} 1 / |x + k| ^ 2`, which is Mathlib's
  `Real.summable_one_div_int_add_rpow`.

The only bookkeeping needed is that the decay bound is available only away from `0`, i.e. for
all but finitely many `k`; summability is insensitive to finitely many terms
(`Summable.of_norm_bounded_eventually`, along the cofinite filter).
-/
import Mathlib

namespace Work.KMTAreas

/-- The set of integers `k` with `|x + k| < 1` is finite: it is contained in the integer
interval `[⌊-x-1⌋, ⌈1-x⌉]`. -/
lemma finite_int_near_shift (x : ℝ) : {k : ℤ | ¬ (1 ≤ |x + (k : ℝ)|)}.Finite := by
  refine (Set.finite_Icc ⌊-x-1⌋ ⌈1-x⌉).subset (fun k hk => ?_)
  have hlt : |x + (k : ℝ)| < 1 := lt_of_not_ge hk
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
  refine ⟨?_, ?_⟩
  · have h : ((⌊-x-1⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by
      have h1 := Int.floor_le (-x-1)
      linarith
    exact_mod_cast h
  · have h : (k : ℝ) ≤ ((⌈1-x⌉ : ℤ) : ℝ) := by
      have h1 := Int.le_ceil (1-x)
      linarith
    exact_mod_cast h

/-- Schwartz decay, in the form needed for the shifted series: there is `C` with
`‖φ y‖ ≤ C / |y| ^ 2` for every `y` with `|y| ≥ 1`. -/
lemma schwartz_norm_le_inv_rpow_sq (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ |y| → ‖(φ : ℝ → ℂ) y‖ ≤ C * (1 / |y| ^ (2 : ℝ)) := by
  refine ⟨SchwartzMap.seminorm ℝ 2 0 φ, fun y hy => ?_⟩
  have h1 : |y| ^ (2 : ℝ) * ‖(φ : ℝ → ℂ) y‖ ≤ SchwartzMap.seminorm ℝ 2 0 φ := by
    have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ φ 2 y
    rw [Real.norm_eq_abs] at h
    have hpow : |y| ^ (2 : ℝ) = |y| ^ 2 := Real.rpow_natCast |y| 2
    rw [hpow]
    exact h
  have hy2 : (0 : ℝ) < |y| ^ (2 : ℝ) := Real.rpow_pos_of_pos (by linarith) 2
  have h2 : ‖(φ : ℝ → ℂ) y‖ ≤ SchwartzMap.seminorm ℝ 2 0 φ / |y| ^ (2 : ℝ) := by
    rw [le_div_iff₀ hy2]
    calc ‖(φ : ℝ → ℂ) y‖ * |y| ^ (2 : ℝ)
        = |y| ^ (2 : ℝ) * ‖(φ : ℝ → ℂ) y‖ := mul_comm _ _
      _ ≤ SchwartzMap.seminorm ℝ 2 0 φ := h1
  simpa [div_eq_mul_inv] using h2

/-- The integer translates of a Schwartz function have summable norms: for every `x : ℝ`,
`∑_{k : ℤ} ‖φ (x + k)‖ < ∞`. -/
theorem schwartz_shift_summable (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun k : ℤ => ‖(φ : ℝ → ℂ) (x + (k : ℝ))‖) := by
  obtain ⟨C, hC⟩ := schwartz_norm_le_inv_rpow_sq φ
  -- the decay bound holds for all but finitely many `k`
  have hev : ∀ᶠ k : ℤ in Filter.cofinite, 1 ≤ |x + (k : ℝ)| :=
    Filter.eventually_cofinite.mpr (finite_int_near_shift x)
  -- the comparison series is summable
  have hcomp : Summable (fun k : ℤ => C * (1 / |x + (k : ℝ)| ^ (2 : ℝ))) := by
    have h := ((Real.summable_one_div_int_add_rpow x 2).mpr one_lt_two).mul_left C
    exact h.congr (fun k => by rw [add_comm])
  refine Summable.of_norm_bounded_eventually hcomp ?_
  filter_upwards [hev] with k hk
  simpa [norm_norm] using hC (x + (k : ℝ)) hk

end Work.KMTAreas
