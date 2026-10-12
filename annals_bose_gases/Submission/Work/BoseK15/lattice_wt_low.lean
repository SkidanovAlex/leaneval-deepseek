import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseK15.LevelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.lattice_wt_low` — the `‖vec n‖^{-2}`-weighted lattice sum inside the ball

FS §10 needs the lattice sum `∑_{n} (1+‖vec n‖/ℓ)^{-4}(‖vec n‖/ℓ)^{-2}` over the
*low* modes `‖vec n‖ < ℓ` to be `O(ℓ³)`.  This is the borderline row of the lattice
estimates: the weight `(‖vec n‖/ℓ)^{-2}` alone would diverge at the origin
(`∑_{n} ‖vec n‖^{-2}` over a ball of radius `R` is `≍ R`, see
`Work.BoseK15.inv2_low`), but the sum is restricted to `‖vec n‖ < ℓ`, and the
`ℓ²` from the scaling combines with the linear growth of `∑‖vec n‖^{-2} ≲ ℓ` to
give exactly `ℓ³`.

Proof (the `ℓ^∞`-level decomposition of `LevelDefs`):

* for `n ≠ 0`, write `r = ‖vec n‖`.  Since `1 + r/ℓ ≥ 1` the first factor is at
  most `1`, and `(r/ℓ)^{-2} = ℓ²/r²`, so the summand is at most `ℓ²/r²`;
* `2π·lev n ≤ r` (`two_pi_mul_lev_le_norm_vec`), so the summand is at most
  `G (lev n)` with `G m = ℓ²/(2πm)²`;
* the levels of the modes in `T` lie in `[1, ⌊ℓ/2π⌋]`
  (`one_le_lev_of_ne_zero`, `lev_le_of_norm_le`), so `sum_le_level_range` gives
  `∑_{n∈T} ≤ ∑_{m=1}^{M} 26 m² · ℓ²/(2πm)² = M · 26ℓ²/(4π²)`;
* finally `M ≤ ℓ/2π` and `26/(8π³) ≤ 1`, whence `M · 26ℓ²/(4π²) ≤ ℓ³`.

All constants are explicit (`26/(8π³) < 1` because `π > 3`); nothing here depends
on the finer structure of `T`, only on `n ≠ 0` and `‖vec n‖ < ℓ`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

/-- The scalar core of the estimate: for `ℓ > 0` and `r > 0`,

    `(1 + r/ℓ)^{-4} (r/ℓ)^{-2} ≤ ℓ²/r²`.

Indeed `1 + r/ℓ ≥ 1` makes the first factor `≤ 1` (negative exponent) and
`(r/ℓ)^{-2} = r^{-2}/ℓ^{-2} = ℓ²/r²`. -/
private lemma rpow_core (ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) :
    (1 + r / ℓ) ^ (-(4 : ℝ)) * (r / ℓ) ^ (-(2 : ℝ)) ≤ ℓ ^ 2 / r ^ 2 := by
  have hA : (1 + r / ℓ) ^ (-(4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [div_nonneg hr.le hℓ.le]) (by norm_num)
  have hBnn : 0 ≤ (r / ℓ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (div_nonneg hr.le hℓ.le) _
  have hB : (r / ℓ) ^ (-(2 : ℝ)) = ℓ ^ 2 / r ^ 2 := by
    have hr2 : (r : ℝ) ^ (2 : ℝ) = r ^ 2 := Real.rpow_natCast r 2
    have hℓ2 : (ℓ : ℝ) ^ (2 : ℝ) = ℓ ^ 2 := Real.rpow_natCast ℓ 2
    rw [Real.div_rpow hr.le hℓ.le, Real.rpow_neg hr.le, Real.rpow_neg hℓ.le,
      hr2, hℓ2, div_inv_eq_mul, inv_mul_eq_div]
  calc (1 + r / ℓ) ^ (-(4 : ℝ)) * (r / ℓ) ^ (-(2 : ℝ))
      ≤ 1 * (r / ℓ) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right hA hBnn
    _ = ℓ ^ 2 / r ^ 2 := by rw [one_mul, hB]

/-- **The weighted lattice sum over the low modes is `O(ℓ³)`.**  For `ℓ ≥ 1` and
any finite set `T` of non-zero lattice indices all of whose momenta satisfy
`‖vec n‖ < ℓ` (FS's *low* mode region, the `‖q‖ ≲ ℓ` part of the mode set),

    `∑_{n ∈ T} (1 + ‖vec n‖/ℓ)^{-4} (‖vec n‖/ℓ)^{-2} ≤ ℓ³`.

The proof is the level decomposition of `LevelDefs` together with the pointwise
domination `(1+r/ℓ)^{-4}(r/ℓ)^{-2} ≤ ℓ²/r² ≤ ℓ²/(2π·lev n)²`. -/
theorem lattice_wt_low (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (T : Finset (Fin 3 → ℤ))
    (hT : ∀ n ∈ T, n ≠ 0) (hlo : ∀ n ∈ T, ‖Work.BoseB4.vec n‖ < ℓ) :
    ∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
      (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ)) ≤ ℓ ^ 3 := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  set M : ℕ := Nat.floor (ℓ / (2 * Real.pi)) with hM
  set G : ℕ → ℝ := fun m => ℓ ^ 2 / (2 * Real.pi * (m : ℝ)) ^ 2 with hG
  have hGnn : ∀ m : ℕ, 0 ≤ G m := by intro m; rw [hG]; positivity
  -- pointwise domination by the level profile
  have hpt : ∀ n ∈ T,
      (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
          (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ)) ≤ G (lev n) := by
    intro n hn
    have hlev1 : 1 ≤ lev n := one_le_lev_of_ne_zero n (hT n hn)
    have hrle : 2 * Real.pi * (lev n : ℝ) ≤ ‖Work.BoseB4.vec n‖ :=
      two_pi_mul_lev_le_norm_vec n
    have hlevr : (0 : ℝ) < (lev n : ℝ) := by exact_mod_cast hlev1
    have hp : (0 : ℝ) < 2 * Real.pi * (lev n : ℝ) := mul_pos (by positivity) hlevr
    have hrpos : 0 < ‖Work.BoseB4.vec n‖ := lt_of_lt_of_le hp hrle
    have h0pos : 0 < (2 * Real.pi * (lev n : ℝ)) ^ 2 := pow_pos hp 2
    have hkey : (2 * Real.pi * (lev n : ℝ)) ^ 2 ≤ ‖Work.BoseB4.vec n‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hrle 2
    calc (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
            (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ))
        ≤ ℓ ^ 2 / ‖Work.BoseB4.vec n‖ ^ 2 := rpow_core ℓ ‖Work.BoseB4.vec n‖ hℓpos hrpos
      _ ≤ ℓ ^ 2 / (2 * Real.pi * (lev n : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) h0pos hkey
      _ = G (lev n) := by rw [hG]
  -- the level range `[1, ⌊ℓ/2π⌋]`
  have hhi : ∀ n ∈ T, lev n ≤ M := by
    intro n hn
    rw [hM]
    exact Nat.le_floor (lev_le_of_norm_le (le_of_lt (hlo n hn)))
  have hmain := sum_le_level_range _ G T 1 M (le_refl 1) hpt
    (fun n hn => one_le_lev_of_ne_zero n (hT n hn)) hhi hGnn
  -- each level term is the constant `26ℓ²/(4π²)`
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      (26 * (m : ℝ) ^ 2) * G m = 26 * ℓ ^ 2 / (4 * Real.pi ^ 2) := by
    intro m hm
    have hm1 : (1 : ℕ) ≤ m := (Finset.mem_Icc.mp hm).1
    have hmne : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    rw [hG]
    field_simp
    ring
  have hsum_eq : ∑ m ∈ Finset.Icc 1 M, (26 * (m : ℝ) ^ 2) * G m
      = (M : ℝ) * (26 * ℓ ^ 2 / (4 * Real.pi ^ 2)) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc]
    rw [Nat.add_sub_cancel, nsmul_eq_mul]
  -- the arithmetic `M · 26ℓ²/(4π²) ≤ ℓ³`
  have hfinal : (M : ℝ) * (26 * ℓ ^ 2 / (4 * Real.pi ^ 2)) ≤ ℓ ^ 3 := by
    have hMr : (M : ℝ) ≤ ℓ / (2 * Real.pi) := by
      rw [hM]; exact Nat.floor_le (by positivity)
    have hc : (0 : ℝ) ≤ 26 * ℓ ^ 2 / (4 * Real.pi ^ 2) := by positivity
    calc (M : ℝ) * (26 * ℓ ^ 2 / (4 * Real.pi ^ 2))
        ≤ (ℓ / (2 * Real.pi)) * (26 * ℓ ^ 2 / (4 * Real.pi ^ 2)) :=
          mul_le_mul_of_nonneg_right hMr hc
      _ = ℓ ^ 3 * (26 / (8 * Real.pi ^ 3)) := by field_simp; ring
      _ ≤ ℓ ^ 3 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]
          have hpi3 : (27 : ℝ) ≤ Real.pi ^ 3 := by
            have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
            have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 3
            norm_num at this ⊢
            linarith
          linarith
      _ = ℓ ^ 3 := by ring
  calc ∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
        (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 M, (26 * (m : ℝ) ^ 2) * G m := hmain
    _ = (M : ℝ) * (26 * ℓ ^ 2 / (4 * Real.pi ^ 2)) := hsum_eq
    _ ≤ ℓ ^ 3 := hfinal

end Work.BoseK15
