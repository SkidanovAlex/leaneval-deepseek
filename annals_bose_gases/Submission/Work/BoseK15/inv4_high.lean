import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseK15.LevelDefs
import Submission.Work.BoseK15.SumInvPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.inv4_high` — the `‖vec n‖^{-4}` tail sum

The lattice sum `∑_{n ∈ S} ‖vec n‖^{-4}` over a set of momenta *outside* the ball of
radius `R` is `O(1/R)`: in three dimensions `∑_{‖vec n‖ ≥ R} ‖vec n‖^{-4}` is the
convergent `p`-series-like sum with `p = 4 > 3`, and truncating it at `R` costs
exactly one power of `R`.  This is the `p = 4` row of FS §10's
`lem:EstimateIntegral` (the source of `K15Input.sum_inv4`).

The estimate is done through the `ℓ^∞` level of `LevelDefs`
(`lev n = maxᵢ |nᵢ|`, shells of size `26 m²`):

* `R ≤ ‖vec n‖` implies `R/(2π√3) ≤ lev n` (`le_lev_of_norm_le`), so the levels
  run from `M₀ = max 1 ⌈R/(2π√3)⌉₊` up to `M₁ = sup_S lev`;
* the level decomposition `sum_le_level_range` turns the lattice sum into
  `∑_{m = M₀}^{M₁} 26 m² (2πm)^{-4} = (26/16π⁴) ∑_{m = M₀}^{M₁} m^{-2}`, and
  `sum_Icc_inv_sq_le` gives `∑ m^{-2} ≤ 2/M₀`;
* finally `1/M₀ ≤ (2π√3+1)/(R+1)`, because `R ≤ M₀·2π√3` and `1 ≤ M₀`.

The constant is absolute (`C = 1000`, deliberately crude — only existence is ever
consumed downstream) and the `R = 0` case is covered by the `R + 1` denominator
(where `S` is forced to contain no nonzero lattice index at all).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

theorem inv4_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset (Fin 3 → ℤ)) (R : ℝ), 0 ≤ R →
      (∀ n ∈ S, n ≠ 0) → (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 4) ≤ C / (R + 1) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro S R hR hne hlow
  set M₀ : ℕ := max 1 ⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊ with hM₀
  set M₁ : ℕ := S.sup lev with hM₁
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀]; exact le_max_left 1 _
  have hlo : ∀ n ∈ S, M₀ ≤ lev n := by
    intro n hn
    have h1 : 1 ≤ lev n := one_le_lev_of_ne_zero n (hne n hn)
    have h2 : ⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊ ≤ lev n :=
      Nat.ceil_le.mpr (le_lev_of_norm_le (hlow n hn))
    rw [hM₀]
    exact Nat.max_le.mpr ⟨h1, h2⟩
  have hhi : ∀ n ∈ S, lev n ≤ M₁ := by
    intro n hn
    rw [hM₁]
    exact Finset.le_sup hn
  have hpt : ∀ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 4 ≤
      (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 4) (lev n) := by
    intro n hn
    have h1 : 1 ≤ lev n := one_le_lev_of_ne_zero n (hne n hn)
    have hb : 0 < 2 * Real.pi * (lev n : ℝ) := by positivity
    have hle : 2 * Real.pi * (lev n : ℝ) ≤ ‖Work.BoseB4.vec n‖ :=
      two_pi_mul_lev_le_norm_vec n
    exact one_div_le_one_div_of_le (pow_pos hb 4) (pow_le_pow_left₀ hb.le hle 4)
  have hGnn : ∀ m : ℕ, 0 ≤ 1 / (2 * Real.pi * (m : ℝ)) ^ 4 := fun m => by positivity
  have hmain := sum_le_level_range (fun n => 1 / ‖Work.BoseB4.vec n‖ ^ 4)
      (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 4) S M₀ M₁ hM₀1 hpt hlo hhi hGnn
  have hterm : ∀ m ∈ Finset.Icc M₀ M₁,
      (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 4)
        = (26 / (16 * Real.pi ^ 4)) * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans hM₀1 (Finset.mem_Icc.mp hm).1
    have hmne : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    field_simp
    ring
  have hsum : (∑ m ∈ Finset.Icc M₀ M₁,
        (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 4))
      = (26 / (16 * Real.pi ^ 4)) * ∑ m ∈ Finset.Icc M₀ M₁, 1 / (m : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hbnd := sum_Icc_inv_sq_le M₀ M₁ hM₀1
  have hkey : (1 : ℝ) / (M₀ : ℝ) ≤ (2 * Real.pi * Real.sqrt 3 + 1) / (R + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : (⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊ : ℝ) ≤ (M₀ : ℝ) := by
      rw [hM₀]
      exact_mod_cast le_max_right 1 ⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊
    have hceil : R / (2 * Real.pi * Real.sqrt 3) ≤
        (⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊ : ℝ) := Nat.le_ceil _
    have hd : 0 < 2 * Real.pi * Real.sqrt 3 := by positivity
    have h1 : R ≤ (M₀ : ℝ) * (2 * Real.pi * Real.sqrt 3) := by
      have h2 := mul_le_mul_of_nonneg_right (le_trans hceil hc) hd.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hd)] at h2
    nlinarith [h1, (by exact_mod_cast hM₀1 : (1 : ℝ) ≤ (M₀ : ℝ))]
  have hnum : (52 / (16 * Real.pi ^ 4)) * (2 * Real.pi * Real.sqrt 3 + 1) ≤ 1000 := by
    have hs3 : Real.sqrt 3 ≤ 2 := by
      have h : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      rwa [show Real.sqrt 4 = (2 : ℝ) from by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have hpi4 : (81 : ℝ) ≤ Real.pi ^ 4 := by
      have h : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have h3 : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
      norm_num at h3 ⊢
      linarith
    have hp1 : Real.pi * Real.sqrt 3 ≤ 8 := by
      nlinarith [Real.pi_lt_four, hs3, Real.pi_pos, Real.sqrt_nonneg 3]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hp1, hpi4, Real.pi_pos]
  calc (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 4)
      ≤ ∑ m ∈ Finset.Icc M₀ M₁,
          (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 4) := hmain
    _ = (26 / (16 * Real.pi ^ 4)) * (∑ m ∈ Finset.Icc M₀ M₁, 1 / (m : ℝ) ^ 2) := hsum
    _ ≤ (26 / (16 * Real.pi ^ 4)) * (2 / (M₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = (52 / (16 * Real.pi ^ 4)) * (1 / (M₀ : ℝ)) := by ring
    _ ≤ (52 / (16 * Real.pi ^ 4)) * ((2 * Real.pi * Real.sqrt 3 + 1) / (R + 1)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((52 / (16 * Real.pi ^ 4)) * (2 * Real.pi * Real.sqrt 3 + 1)) * (1 / (R + 1)) := by
        ring
    _ ≤ 1000 * (1 / (R + 1)) := by
        refine mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 1000 / (R + 1) := by ring

end Work.BoseK15
