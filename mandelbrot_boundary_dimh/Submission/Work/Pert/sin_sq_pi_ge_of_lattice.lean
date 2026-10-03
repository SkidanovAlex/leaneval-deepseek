import Mathlib

/-!
# PERT · `Work.Pert.sin_sq_pi_ge_of_lattice`

If a real number `P` stays at squared `T`-distance at least `δ ^ 2` from every point of the
lattice `ℤ`, that is

  `δ ^ 2 ≤ (P - k) ^ 2 + T ^ 2`  for every `k : ℤ`,

then `4 * max 0 (δ ^ 2 - T ^ 2) ≤ sin (π * P) ^ 2`.

This is the elementary "lattice separation" estimate used in the Shishikura perturbation
gates: the horizontal distance to the lattice controls the squared sine through

* *nearest-integer rounding* (`k = ⌊P + 1/2⌋`, so `|P - k| ≤ 1/2`), together with the fact that
  `sin (π ·) ^ 2` is unchanged when `P` is shifted by an integer, and
* *Jordan's inequality* `sin t ≥ (2 / π) * t` on `[0, π / 2]`, which in squared form reads
  `4 * x ^ 2 ≤ sin (π * x) ^ 2` for `|x| ≤ 1/2` (equality at `x = ±1/2`).

The two ingredients are proved below as (private) helper lemmas; the main theorem is a short
assembly.
-/

namespace Work.Pert

set_option autoImplicit false

/-- **Jordan's inequality, squared form.**  For `x` in the fundamental interval
`[-1/2, 1/2]` one has `4 * x ^ 2 ≤ sin (π * x) ^ 2`.  The constant is optimal: equality holds
at `x = ±1/2`.

Proof: with `t = |π * x| ≤ π / 2`, Jordan's inequality `2 / π * t ≤ |sin t|` (Mathlib's
`Real.mul_abs_le_abs_sin`) gives `2 * |x| ≤ |sin (π * x)|`; squaring yields the claim. -/
private theorem sin_sq_pi_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) :
    4 * x ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
  have hpx : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hx]
  have h1 := Real.mul_abs_le_abs_sin hpx
  have h2 : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    have h3 : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    linarith [h1, h3]
  have h3 : (2 * |x|) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
    have hp : (2 * |x|) ^ 2 ≤ |Real.sin (Real.pi * x)| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rwa [sq_abs] at hp
  nlinarith [h3, sq_abs x]

/-- **Nearest-integer rounding.**  For every `P : ℝ` there is an integer `k` with
`|P - k| ≤ 1 / 2` and, moreover, `sin (π * P) ^ 2 = sin (π * (P - k)) ^ 2`; the first conjunct
is `k = ⌊P + 1/2⌋` and the second holds for *every* integer `k` because
`sin (π * (P - k)) = (-1) ^ k * sin (π * P)`. -/
private theorem exists_int_abs_sub_le_half_sin_sq (P : ℝ) :
    ∃ k : ℤ, |P - (k : ℝ)| ≤ 1 / 2 ∧
      Real.sin (Real.pi * P) ^ 2 = Real.sin (Real.pi * (P - (k : ℝ))) ^ 2 := by
  have hsin : ∀ k : ℤ,
      Real.sin (Real.pi * (P - (k : ℝ))) ^ 2 = Real.sin (Real.pi * P) ^ 2 := by
    intro k
    have h1 : Real.sin (Real.pi * (P - (k : ℝ))) =
        (-1 : ℝ) ^ k * Real.sin (Real.pi * P) := by
      have h2 := Real.sin_sub_int_mul_pi (Real.pi * P) k
      have harg : Real.pi * P - (k : ℝ) * Real.pi = Real.pi * (P - (k : ℝ)) := by ring
      rw [← harg]; exact h2
    rw [h1]
    rcases Int.even_or_odd k with he | ho
    · rw [he.neg_one_zpow]; ring
    · rw [ho.neg_one_zpow]; ring
  set k : ℤ := ⌊P + 1 / 2⌋ with hk
  have hk_le : (k : ℝ) ≤ P + 1 / 2 := by rw [hk]; exact Int.floor_le _
  have hk_lt : P + 1 / 2 < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
  refine ⟨k, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · exact (hsin k).symm

/-- **Lattice separation bounds the sine.**  If `δ ^ 2 ≤ (P - k) ^ 2 + T ^ 2` for every integer
`k`, then `4 * max 0 (δ ^ 2 - T ^ 2) ≤ sin (π * P) ^ 2`. -/
theorem sin_sq_pi_ge_of_lattice {P T δ : ℝ}
    (h : ∀ k : ℤ, δ ^ 2 ≤ (P - (k : ℝ)) ^ 2 + T ^ 2) :
    4 * max 0 (δ ^ 2 - T ^ 2) ≤ Real.sin (Real.pi * P) ^ 2 := by
  obtain ⟨k, hk, hsin⟩ := exists_int_abs_sub_le_half_sin_sq P
  -- the lattice hypothesis turns into a bound on the excess over `T ^ 2`
  have hd : δ ^ 2 - T ^ 2 ≤ (P - (k : ℝ)) ^ 2 := by
    have := h k; linarith
  have hmax : max 0 (δ ^ 2 - T ^ 2) ≤ (P - (k : ℝ)) ^ 2 :=
    max_le (by positivity) hd
  calc 4 * max 0 (δ ^ 2 - T ^ 2) ≤ 4 * (P - (k : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
    _ ≤ Real.sin (Real.pi * (P - (k : ℝ))) ^ 2 := sin_sq_pi_of_abs_le_half hk
    _ = Real.sin (Real.pi * P) ^ 2 := hsin.symm

end Work.Pert
