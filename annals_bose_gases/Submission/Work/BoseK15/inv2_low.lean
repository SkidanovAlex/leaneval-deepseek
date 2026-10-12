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
# `Work.BoseK15.inv2_low` — the shell-sum bound `∑ ‖vec n‖^{-2} ≲ R`

The lattice summand `1/‖vec n‖²` is *not* summable in the naive sense over a ball:
there are `~R³` lattice points with `‖vec n‖ ≤ R` and the summand has a non-integrable
singularity at the origin.  But on a ball of radius `R` the sum is still only
`O(R)`, not `O(R³)`: the divergence is cured by the `‖n‖^{-2}` weight and the `ℝ³`
volume measure `∫_{‖k‖≤R} ‖k‖^{-2}dk = 4πR` is finite.  This is the elementary
count that FS §10 consumes when it replaces `∑_{q} ‖q‖^{-2}` over a truncated mode
set by a bound linear in the truncation radius (and it is what licenses the
`∑ ‖vec n‖^{-p}` rows of `lem:EstimateIntegral` for `p = 2`, the borderline case).

The proof uses the `ℓ^∞` level of `LevelDefs` (`lev n = maxᵢ |nᵢ|`) rather than the
crude ball count `card_le_of_vec_norm_le` (which would give `(R/π+1)³ = O(R³)`):

* by `two_pi_mul_lev_le_norm_vec`, `‖vec n‖ ≥ 2π·lev n`, so the summand is at most
  `(2π lev n)^{-2}`;
* the level shells `{lev = m}` carry at most `26 m²` points (`card_filter_lev_le`),
  exactly the `ℝ³`-surface growth `4πm²`;
* the level decomposition `sum_le_level_range` then turns the sum into
  `∑_{m=1}^{⌊R/2π⌋} 26 m² · (2πm)^{-2} = ⌊R/2π⌋ · 26/(4π²) ≤ R`,
  because `26/(8π³) < 1` (`π > 3`).

Hence `C = 1` works, and the constant is absolute (no dependence on the finite set
`S` or on the cutoff `R`).  The hypothesis `n ≠ 0` on `S` is exactly what makes
`lev n ≥ 1` (`one_le_lev_of_ne_zero`), i.e. what keeps the summand off the pole.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

/-- **The `‖vec n‖^{-2}` lattice sum over a ball is `O(R)`.**  There is an absolute
constant `C ≥ 0` such that every finite set `S` of *nonzero* lattice indices whose
momenta `vec n = 2πn` are bounded by `R` contributes at most `C·R`:

    `∑_{n ∈ S} ‖vec n‖^{-2} ≤ C·R`   (`‖vec n‖ ≤ R` for `n ∈ S`).

The proof is the level decomposition of `LevelDefs`: `‖vec n‖ ≥ 2π·lev n`, the shell
`{lev = m}` has at most `26 m²` points, and `∑_{m≤⌊R/2π⌋} 26 m²(2πm)^{-2} ≤ R`
since `26/(8π³) < 1`; take `C = 1`. -/
theorem inv2_low :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset (Fin 3 → ℤ)) (R : ℝ), 0 ≤ R →
      (∀ n ∈ S, n ≠ 0) → (∀ n ∈ S, ‖Work.BoseB4.vec n‖ ≤ R) →
      (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 2) ≤ C * R := by
  refine ⟨1, zero_le_one, ?_⟩
  intro S R hR hne hbd
  -- the level of every `n ∈ S` lies in `[1, ⌊R/(2π)⌋]`
  set M : ℕ := Nat.floor (R / (2 * Real.pi)) with hM
  have hhi : ∀ n ∈ S, lev n ≤ M := by
    intro n hn
    rw [hM]
    exact Nat.le_floor (lev_le_of_norm_le (hbd n hn))
  have hlo : ∀ n ∈ S, 1 ≤ lev n := fun n hn => one_le_lev_of_ne_zero n (hne n hn)
  -- pointwise domination by the level profile `G m = (2πm)^{-2}`
  have hpt : ∀ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 2 ≤
      (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 2) (lev n) := by
    intro n hn
    have hb : 0 < 2 * Real.pi * (lev n : ℝ) := by
      have h1 : 1 ≤ lev n := hlo n hn
      positivity
    have hle : 2 * Real.pi * (lev n : ℝ) ≤ ‖Work.BoseB4.vec n‖ :=
      two_pi_mul_lev_le_norm_vec n
    exact one_div_le_one_div_of_le (pow_pos hb 2) (pow_le_pow_left₀ hb.le hle 2)
  have hGnn : ∀ m : ℕ, 0 ≤ 1 / (2 * Real.pi * (m : ℝ)) ^ 2 := fun m => by positivity
  -- the level decomposition
  have hmain := sum_le_level_range (fun n => 1 / ‖Work.BoseB4.vec n‖ ^ 2)
      (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 2) S 1 M (le_refl 1) hpt hlo hhi hGnn
  -- each term of the level sum is the constant `26/(4π²)`
  have hterm : ∀ m ∈ Finset.Icc 1 M, (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 2)
      = 26 / (4 * Real.pi ^ 2) := by
    intro m hm
    have hm1 : (1 : ℕ) ≤ m := (Finset.mem_Icc.mp hm).1
    have hmne : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    field_simp
    ring
  have hsum_eq : ∑ m ∈ Finset.Icc 1 M, (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 2)
      = (M : ℝ) * (26 / (4 * Real.pi ^ 2)) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc]
    rw [Nat.add_sub_cancel, nsmul_eq_mul]
  -- the level count `M ≤ R/(2π)` converts to the linear bound
  have hfinal : (M : ℝ) * (26 / (4 * Real.pi ^ 2)) ≤ R := by
    have hMr : (M : ℝ) ≤ R / (2 * Real.pi) := by
      rw [hM]; exact Nat.floor_le (by positivity)
    have hc : (0 : ℝ) ≤ 26 / (4 * Real.pi ^ 2) := by positivity
    have hp3 : (27 : ℝ) ≤ Real.pi ^ 3 := by
      have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 3
      norm_num at this ⊢
      linarith
    calc (M : ℝ) * (26 / (4 * Real.pi ^ 2))
        ≤ (R / (2 * Real.pi)) * (26 / (4 * Real.pi ^ 2)) :=
          mul_le_mul_of_nonneg_right hMr hc
      _ = R * (26 / (8 * Real.pi ^ 3)) := by field_simp; ring
      _ ≤ R * 1 := by
          apply mul_le_mul_of_nonneg_left _ hR
          rw [div_le_one (by positivity)]
          linarith
      _ = R := by ring
  have h1 : ∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 2 ≤ R :=
    hmain.trans (hsum_eq.trans_le hfinal)
  linarith

end Work.BoseK15
