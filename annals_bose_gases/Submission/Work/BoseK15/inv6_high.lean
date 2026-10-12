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
# `Work.BoseK15.inv6_high` — the `‖vec n‖^{-6}` tail sum

The sibling `Work.BoseK15.inv4_high`.  Here `∑_{n ∈ S} ‖vec n‖^{-6}` over momenta
outside the ball of radius `R` is `O(R^{-3})`, the `p = 6` row of FS §10's
`lem:EstimateIntegral` (the source of `K15Input.sum_inv6`).

Same level machinery as `inv4_high`: the levels run from
`M₀ = max 1 ⌈R/(2π√3)⌉₊` to `M₁ = sup_S lev`, the level decomposition gives
`∑_{m = M₀}^{M₁} 26 m² (2πm)^{-6} = (26/64π⁶) ∑_{m = M₀}^{M₁} m^{-4}`, and the
`m^{-4}` bound `sum_Icc_inv_pow4_le` gives `≤ (52/64π⁶)/M₀³`.  With
`1/M₀ ≤ (2π√3+1)/(R+1)` this is `O(R^{-3})`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

theorem inv6_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset (Fin 3 → ℤ)) (R : ℝ), 0 ≤ R →
      (∀ n ∈ S, n ≠ 0) → (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 6) ≤ C / (R + 1) ^ 3 := by
  refine ⟨1000000, by norm_num, ?_⟩
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
  have hpt : ∀ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 6 ≤
      (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 6) (lev n) := by
    intro n hn
    have h1 : 1 ≤ lev n := one_le_lev_of_ne_zero n (hne n hn)
    have hb : 0 < 2 * Real.pi * (lev n : ℝ) := by positivity
    have hle : 2 * Real.pi * (lev n : ℝ) ≤ ‖Work.BoseB4.vec n‖ :=
      two_pi_mul_lev_le_norm_vec n
    exact one_div_le_one_div_of_le (pow_pos hb 6) (pow_le_pow_left₀ hb.le hle 6)
  have hGnn : ∀ m : ℕ, 0 ≤ 1 / (2 * Real.pi * (m : ℝ)) ^ 6 := fun m => by positivity
  have hmain := sum_le_level_range (fun n => 1 / ‖Work.BoseB4.vec n‖ ^ 6)
      (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 6) S M₀ M₁ hM₀1 hpt hlo hhi hGnn
  have hterm : ∀ m ∈ Finset.Icc M₀ M₁,
      (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 6)
        = (26 / (64 * Real.pi ^ 6)) * (1 / (m : ℝ) ^ 4) := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans hM₀1 (Finset.mem_Icc.mp hm).1
    have hmne : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    field_simp
    ring
  have hsum : (∑ m ∈ Finset.Icc M₀ M₁,
        (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 6))
      = (26 / (64 * Real.pi ^ 6)) * ∑ m ∈ Finset.Icc M₀ M₁, 1 / (m : ℝ) ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hbnd := sum_Icc_inv_pow4_le M₀ M₁ hM₀1
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
  have hnum : (52 / (64 * Real.pi ^ 6)) * (2 * Real.pi * Real.sqrt 3 + 1) ^ 3
      ≤ 1000000 := by
    have hs3 : Real.sqrt 3 ≤ 2 := by
      have h : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      rwa [show Real.sqrt 4 = (2 : ℝ) from by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have hpi6 : (729 : ℝ) ≤ Real.pi ^ 6 := by
      have h : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have h3 : (3 : ℝ) ^ 6 ≤ Real.pi ^ 6 := pow_le_pow_left₀ (by norm_num) h 6
      norm_num at h3 ⊢
      linarith
    have hp1 : Real.pi * Real.sqrt 3 ≤ 8 := by
      nlinarith [Real.pi_lt_four, hs3, Real.pi_pos, Real.sqrt_nonneg 3]
    have hp3 : (2 * Real.pi * Real.sqrt 3 + 1) ^ 3 ≤ 4913 := by
      have h : 2 * Real.pi * Real.sqrt 3 + 1 ≤ 17 := by linarith [hp1]
      have h0 : (0 : ℝ) ≤ 2 * Real.pi * Real.sqrt 3 + 1 := by positivity
      have hc := pow_le_pow_left₀ h0 h 3
      norm_num at hc ⊢
      exact hc
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hp3, hpi6, Real.pi_pos]
  calc (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 6)
      ≤ ∑ m ∈ Finset.Icc M₀ M₁,
          (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 6) := hmain
    _ = (26 / (64 * Real.pi ^ 6)) * (∑ m ∈ Finset.Icc M₀ M₁, 1 / (m : ℝ) ^ 4) := hsum
    _ ≤ (26 / (64 * Real.pi ^ 6)) * (2 / (M₀ : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = (52 / (64 * Real.pi ^ 6)) * (1 / (M₀ : ℝ)) ^ 3 := by ring
    _ ≤ (52 / (64 * Real.pi ^ 6)) * ((2 * Real.pi * Real.sqrt 3 + 1) / (R + 1)) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hkey 3
    _ = ((52 / (64 * Real.pi ^ 6)) * (2 * Real.pi * Real.sqrt 3 + 1) ^ 3) *
          (1 / (R + 1)) ^ 3 := by ring
    _ ≤ 1000000 * (1 / (R + 1)) ^ 3 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 1000000 / (R + 1) ^ 3 := by rw [one_div_pow]; ring

end Work.BoseK15
