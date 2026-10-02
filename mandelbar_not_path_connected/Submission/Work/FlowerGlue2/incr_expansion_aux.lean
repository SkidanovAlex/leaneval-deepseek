import Mathlib
import Submission.Work.FlowerGlue2.L0
import Submission.Work.FlowerGlue2.incr_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- **The increment expansion at the parabolic parameter.**

At `c₀` the germ constant is `τ = P.h c₀ 0 = 1` (`Work.FlowerGlue2.tau_c₀`), so that the germ
reads `h = 1 + h₁ζ + O(ζ²)` and the correction constant of the approximate Écalle coordinate is
`κ₀ = 1 - h₁` (`Work.FlowerGlue2.kappa_eq_one_sub_h1`).  The exact algebraic identity

`h/(1 + ζh) - 1 + κ₀ζ = ((h - 1 - h₁ζ)(1 - ζ) - h₁ζ² + κ₀ζ²h) / (1 + ζh)`

then exhibits the increment `w ↦ w + h(ζ)/(1 + ζh(ζ))`, `ζ = -1/w`, as `1 - κ₀ζ` up to an error
that is `O(‖ζ‖²)`: the term `h - 1 - h₁ζ` is `O(‖ζ‖²)` by the uniform bounds, and the linear parts
in `ζ` cancel exactly because `κ₀ = 1 - h₁`.

The two remaining conjuncts are the `L¹`-consequences of the first: on `‖ζ‖ ≤ rsmall P` a
straight estimate on `rsmall` gives `‖h/(1 + ζh) - 1‖ ≤ 5/64`, whence the real part of the
increment is `≥ 59/64 > 1/2` (so the lower bound involving the *linear* term `(κ₀ζ).re` holds)
and the increment is `≤ 69/64 < 3/2` in modulus.

*Provenance of the vocabulary.*  `rsmall` and `Cin` are defined in
`Submission/Work/FlowerGlue2/incr_defs.lean` — copied verbatim from
`Submission/Work/FlowerGlue2/box_lands_attr.lean`, which **no longer compiles** because it imports
the deleted module `Submission.Work.FlowerGlue2.box_deep_attr` (judged unprovable as written,
`NOTES_FALSE_box_deep_attr2.md`).  Nothing from that broken chain is used here: the proof needs
only `ParNormal.bounds`, `tau_c₀` and `kappa_eq_one_sub_h1`.
-/
theorem incr_expansion_aux {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ Work.FlowerGlue2.rsmall P) :
    ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 + P.κ c₀ * ζ‖ ≤ Work.FlowerGlue2.Cin P * ‖ζ‖ ^ 2 ∧
    (P.κ c₀ * ζ).re - Work.FlowerGlue2.Cin P * ‖ζ‖ ^ 2 ≤ (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re ∧
    ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)‖ ≤ 3 / 2 := by
  have hτ : P.h c₀ 0 = 1 := tau_c₀ P
  have hκ : P.κ c₀ = 1 - P.h1 c₀ := kappa_eq_one_sub_h1 P hτ
  have hr : ‖ζ‖ < P.r := lt_of_le_of_lt hζ (rsmall_le_r P)
  have h64 : ‖ζ‖ ≤ 1 / 64 := le_trans hζ (rsmall_le_one P)
  have hB : 1 + ζ * P.h c₀ ζ ≠ 0 := one_add_ne P hζ
  have hB2 : 1 + P.h c₀ ζ * ζ ≠ 0 := by
    have h : (1 : ℂ) + P.h c₀ ζ * ζ = 1 + ζ * P.h c₀ ζ := by ring
    rw [h]; exact hB
  have hh2 : ‖P.h c₀ ζ‖ ≤ 2 := (h_norm_bounds' P hr).1
  have he : ‖P.h c₀ ζ - 1 - P.h1 c₀ * ζ‖ ≤ P.A * ‖ζ‖ ^ 2 := by
    have h := (P.bounds c₀ (Metric.mem_ball_self P.hρ₀)).2.2.1 ζ hr
    rw [hτ] at h; exact h
  have hzh : ‖ζ * P.h c₀ ζ‖ ≤ 1 / 2 := zeta_h_small P hζ
  have hden : (1 : ℝ) / 2 ≤ ‖1 + ζ * P.h c₀ ζ‖ := by
    have h := norm_sub_le (1 + ζ * P.h c₀ ζ) (ζ * P.h c₀ ζ)
    have h' : ‖(1 : ℂ)‖ ≤ ‖1 + ζ * P.h c₀ ζ‖ + ‖ζ * P.h c₀ ζ‖ := by simpa using h
    rw [norm_one] at h'; linarith
  have hCin0 : 0 ≤ Cin P := by
    have h1 := norm_nonneg (P.h1 c₀)
    have h2 := norm_nonneg (P.κ c₀)
    rw [Cin]; linarith [P.hA]
  have hkey : P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 + P.κ c₀ * ζ
      = ((P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ) - P.h1 c₀ * ζ ^ 2 + P.κ c₀ * ζ ^ 2 * P.h c₀ ζ)
        / (1 + ζ * P.h c₀ ζ) := by
    rw [hκ, eq_div_iff hB]
    field_simp [hB2]
    ring
  have hnum : ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ) - P.h1 c₀ * ζ ^ 2
        + P.κ c₀ * ζ ^ 2 * P.h c₀ ζ‖
      ≤ (P.A * (65 / 64) + ‖P.h1 c₀‖ + 2 * ‖P.κ c₀‖) * ‖ζ‖ ^ 2 := by
    have hsplit : ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ) - P.h1 c₀ * ζ ^ 2
          + P.κ c₀ * ζ ^ 2 * P.h c₀ ζ‖
        ≤ ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ)‖ + ‖P.h1 c₀ * ζ ^ 2‖
          + ‖P.κ c₀ * ζ ^ 2 * P.h c₀ ζ‖ := by
      have h1 := norm_add_le ((P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ) - P.h1 c₀ * ζ ^ 2)
        (P.κ c₀ * ζ ^ 2 * P.h c₀ ζ)
      have h2 := norm_sub_le ((P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ)) (P.h1 c₀ * ζ ^ 2)
      linarith
    have h1z : ‖(1 : ℂ) - ζ‖ ≤ 65 / 64 := by
      have h := norm_sub_le (1 : ℂ) ζ
      rw [norm_one] at h; linarith
    have hterm1 : ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ)‖
        ≤ (P.A * (65 / 64)) * ‖ζ‖ ^ 2 := by
      rw [norm_mul]
      calc ‖P.h c₀ ζ - 1 - P.h1 c₀ * ζ‖ * ‖(1 : ℂ) - ζ‖
          ≤ (P.A * ‖ζ‖ ^ 2) * (65 / 64) :=
            mul_le_mul he h1z (norm_nonneg _) (mul_nonneg P.hA (by positivity))
        _ = (P.A * (65 / 64)) * ‖ζ‖ ^ 2 := by ring
    have hterm2 : ‖P.h1 c₀ * ζ ^ 2‖ ≤ ‖P.h1 c₀‖ * ‖ζ‖ ^ 2 := by
      rw [norm_mul, norm_pow]
    have hterm3 : ‖P.κ c₀ * ζ ^ 2 * P.h c₀ ζ‖ ≤ (2 * ‖P.κ c₀‖) * ‖ζ‖ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow]
      have h3 : ‖P.κ c₀‖ * (‖ζ‖ ^ 2 * ‖P.h c₀ ζ‖) ≤ ‖P.κ c₀‖ * (‖ζ‖ ^ 2 * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh2 (by positivity))
          (norm_nonneg _)
      calc ‖P.κ c₀‖ * ‖ζ‖ ^ 2 * ‖P.h c₀ ζ‖
          = ‖P.κ c₀‖ * (‖ζ‖ ^ 2 * ‖P.h c₀ ζ‖) := by ring
        _ ≤ ‖P.κ c₀‖ * (‖ζ‖ ^ 2 * 2) := h3
        _ = (2 * ‖P.κ c₀‖) * ‖ζ‖ ^ 2 := by ring
    linarith
  have hE : ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 + P.κ c₀ * ζ‖ ≤ Cin P * ‖ζ‖ ^ 2 := by
    rw [hkey, norm_div]
    have hdenpos : 0 < ‖1 + ζ * P.h c₀ ζ‖ := lt_of_lt_of_le (by norm_num) hden
    rw [div_le_iff₀ hdenpos]
    have hM : P.A * (65 / 64) + ‖P.h1 c₀‖ + 2 * ‖P.κ c₀‖ ≤ Cin P / 2 := by
      rw [Cin]; linarith [P.hA]
    have h1 : ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) * (1 - ζ) - P.h1 c₀ * ζ ^ 2
          + P.κ c₀ * ζ ^ 2 * P.h c₀ ζ‖ ≤ (Cin P / 2) * ‖ζ‖ ^ 2 :=
      le_trans hnum (mul_le_mul_of_nonneg_right hM (by positivity))
    have h2 : (Cin P / 2) * ‖ζ‖ ^ 2 ≤ Cin P * ‖ζ‖ ^ 2 * ‖1 + ζ * P.h c₀ ζ‖ := by
      have h3 : (Cin P / 2) * ‖ζ‖ ^ 2 = (Cin P * ‖ζ‖ ^ 2) * (1 / 2) := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hden (mul_nonneg hCin0 (by positivity))
    linarith
  have hSpos : 0 < 1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖ := by
    have h1 := norm_nonneg (P.h1 c₀); have h2 := norm_nonneg (P.κ c₀); linarith [P.hA]
  have hrs : rsmall P ≤ 1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hCin_rsmall : Cin P * rsmall P ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left hrs hCin0
    have h2 : Cin P * (1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖))) ≤ 1 / 16 := by
      rw [mul_one_div,
        div_le_iff₀ (by linarith : (0:ℝ) < 64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖))]
      rw [Cin]
      nlinarith [norm_nonneg (P.h1 c₀), norm_nonneg (P.κ c₀), P.hA]
    linarith
  have hκ_rsmall : ‖P.κ c₀‖ * rsmall P ≤ 1 / 64 := by
    have h := mul_le_mul_of_nonneg_left hrs (norm_nonneg (P.κ c₀))
    have h2 : ‖P.κ c₀‖ * (1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖))) ≤ 1 / 64 := by
      rw [mul_one_div,
        div_le_iff₀ (by linarith : (0:ℝ) < 64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖))]
      nlinarith [norm_nonneg (P.h1 c₀), norm_nonneg (P.κ c₀), P.hA]
    linarith
  have hCinζ : Cin P * ‖ζ‖ ^ 2 ≤ 1 / 4 := by
    have h1 : ‖ζ‖ ^ 2 ≤ ‖ζ‖ * rsmall P := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_left hζ (norm_nonneg ζ)
    have h2 : Cin P * ‖ζ‖ ^ 2 ≤ Cin P * (‖ζ‖ * rsmall P) := mul_le_mul_of_nonneg_left h1 hCin0
    have h3 : Cin P * rsmall P * ‖ζ‖ ≤ (1 / 16) * (1 / 64) :=
      mul_le_mul hCin_rsmall h64 (norm_nonneg ζ) (by norm_num)
    linarith
  have hκζ : ‖P.κ c₀‖ * ‖ζ‖ ≤ 1 / 64 :=
    le_trans (mul_le_mul_of_nonneg_left hζ (norm_nonneg _)) hκ_rsmall
  have hsmall : ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1‖ ≤ 1 / 2 := by
    have h1 : ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1‖
        ≤ ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 + P.κ c₀ * ζ‖ + ‖P.κ c₀ * ζ‖ := by
      have h := norm_sub_le (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 + P.κ c₀ * ζ) (P.κ c₀ * ζ)
      have heq : P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 + P.κ c₀ * ζ - P.κ c₀ * ζ
          = P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1 := by ring
      rwa [heq] at h
    have h2 : ‖P.κ c₀ * ζ‖ ≤ 1 / 64 := by rw [norm_mul]; exact hκζ
    linarith
  refine ⟨hE, ?_, ?_⟩
  · have hrew : (1 : ℝ) / 2 ≤ (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re := by
      have h := (abs_le.mp (Complex.abs_re_le_norm (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1))).1
      have heq : (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1).re
          = (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re - 1 := by
        rw [Complex.sub_re, Complex.one_re]
      linarith
    have hL : (P.κ c₀ * ζ).re - Cin P * ‖ζ‖ ^ 2 ≤ 1 / 64 := by
      have h4 : (P.κ c₀ * ζ).re ≤ 1 / 64 := by
        have h5 := Complex.re_le_norm (P.κ c₀ * ζ)
        rw [norm_mul] at h5
        linarith
      have h6 : 0 ≤ Cin P * ‖ζ‖ ^ 2 := mul_nonneg hCin0 (by positivity)
      linarith
    linarith
  · have h : ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)‖
        ≤ ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1‖ + 1 := by
      have h := norm_add_le (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1) (1 : ℂ)
      simpa using h
    linarith

end Work.FlowerGlue2
