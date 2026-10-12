import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB7AK.K15R.LevelDefs
import Submission.Work.BoseB7AK.K15R.SumInvPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.inv3_annulus` — the `‖vec n‖^{-3}` annulus sum

The `p = 3` row of FS §10's `lem:EstimateIntegral` (the source of
`K15Input.sum_inv3`): over the *annulus* `R ≤ ‖vec n‖ ≤ R'` with `R' ≤ 2·K_H·R`,

    `∑_{n ∈ S} ‖vec n‖^{-3} ≤ C·(1 + log K_H)`,

the logarithm coming from `∫_R^{2K_H R} r^{-1} dr = log(2K_H)` — the annulus
squarely sits on the borderline `p = 3` where the lattice sum is only
logarithmically bounded.

Via the `ℓ^∞` level machinery (`LevelDefs`): the levels run from
`M₀ = max 1 ⌈R/(2π√3)⌉₊` to `M₁ = sup_S lev`, and

    `∑_{n ∈ S} ‖vec n‖^{-3} ≤ ∑_{m = M₀}^{M₁} 26 m² (2πm)^{-3}
      = (26/8π³) ∑_{m = M₀}^{M₁} m^{-1} ≤ (26/8π³)(1 + log M₁ - log M₀)`.

The two norms compare by `2π√3·M₀ ≥ R` and `M₁ ≤ R'/(2π) ≤ 2√3·K_H·M₀`, so
`log M₁ - log M₀ ≤ log(2√3 K_H) ≤ 3 + log K_H`, and `26/8π³ ≤ 1` finishes with the
crude absolute constant `C = 100`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

theorem inv3_annulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset (Fin 3 → ℤ)) (R R' KH : ℝ), 1 ≤ KH →
      (∀ n ∈ S, n ≠ 0) → (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∀ n ∈ S, ‖Work.BoseB4.vec n‖ ≤ R') → R' ≤ 2 * KH * R →
      (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 3) ≤ C * (1 + Real.log KH) := by
  refine ⟨100, by norm_num, ?_⟩
  intro S R R' KH hKH hne hlow hhigh hR'
  have hs3 : Real.sqrt 3 ≤ 2 := by
    have h : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show Real.sqrt 4 = (2 : ℝ) from by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hlogKH : 0 ≤ Real.log KH := Real.log_nonneg hKH
  by_cases hS : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hS
    have hRpos : 0 < R := by
      by_contra hRc
      push_neg at hRc
      have h1 : (2 : ℝ) * Real.pi ≤ ‖Work.BoseB4.vec n₀‖ := by
        have hlev : (1 : ℝ) ≤ (lev n₀ : ℝ) := by
          exact_mod_cast one_le_lev_of_ne_zero n₀ (hne n₀ hn₀)
        calc (2 : ℝ) * Real.pi = 2 * Real.pi * 1 := by ring
          _ ≤ 2 * Real.pi * (lev n₀ : ℝ) := by
              refine mul_le_mul_of_nonneg_left hlev (by positivity)
          _ ≤ ‖Work.BoseB4.vec n₀‖ := two_pi_mul_lev_le_norm_vec n₀
      nlinarith [h1, hhigh n₀ hn₀, hR', hKH, Real.pi_pos]
    have hR'pos : 0 < R' := by
      have h1 : (2 : ℝ) * Real.pi ≤ ‖Work.BoseB4.vec n₀‖ := by
        have hlev : (1 : ℝ) ≤ (lev n₀ : ℝ) := by
          exact_mod_cast one_le_lev_of_ne_zero n₀ (hne n₀ hn₀)
        calc (2 : ℝ) * Real.pi = 2 * Real.pi * 1 := by ring
          _ ≤ 2 * Real.pi * (lev n₀ : ℝ) := by
              refine mul_le_mul_of_nonneg_left hlev (by positivity)
          _ ≤ ‖Work.BoseB4.vec n₀‖ := two_pi_mul_lev_le_norm_vec n₀
      linarith [hhigh n₀ hn₀, Real.pi_pos]
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
    have hM₀M₁ : M₀ ≤ M₁ := le_trans (hlo n₀ hn₀) (hhi n₀ hn₀)
    have hpt : ∀ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 3 ≤
        (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 3) (lev n) := by
      intro n hn
      have h1 : 1 ≤ lev n := one_le_lev_of_ne_zero n (hne n hn)
      have hb : 0 < 2 * Real.pi * (lev n : ℝ) := by positivity
      have hle : 2 * Real.pi * (lev n : ℝ) ≤ ‖Work.BoseB4.vec n‖ :=
        two_pi_mul_lev_le_norm_vec n
      exact one_div_le_one_div_of_le (pow_pos hb 3) (pow_le_pow_left₀ hb.le hle 3)
    have hGnn : ∀ m : ℕ, 0 ≤ 1 / (2 * Real.pi * (m : ℝ)) ^ 3 := fun m => by positivity
    have hmain := sum_le_level_range (fun n => 1 / ‖Work.BoseB4.vec n‖ ^ 3)
        (fun m : ℕ => 1 / (2 * Real.pi * (m : ℝ)) ^ 3) S M₀ M₁ hM₀1 hpt hlo hhi hGnn
    have hterm : ∀ m ∈ Finset.Icc M₀ M₁,
        (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 3)
          = (26 / (8 * Real.pi ^ 3)) * (1 / (m : ℝ)) := by
      intro m hm
      have hm1 : 1 ≤ m := le_trans hM₀1 (Finset.mem_Icc.mp hm).1
      have hmne : (m : ℝ) ≠ 0 := by
        have : (0 : ℝ) < m := by exact_mod_cast hm1
        positivity
      field_simp
      ring
    have hsum : (∑ m ∈ Finset.Icc M₀ M₁,
          (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 3))
        = (26 / (8 * Real.pi ^ 3)) * ∑ m ∈ Finset.Icc M₀ M₁, 1 / (m : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hterm
    have hbnd := sum_Icc_inv_le_log M₀ M₁ hM₀1 hM₀M₁
    -- the level ratio is at most `2√3·K_H`
    have hM₁le : (M₁ : ℝ) ≤ R' / (2 * Real.pi) := by
      have hle : M₁ ≤ ⌊R' / (2 * Real.pi)⌋₊ := by
        rw [hM₁]
        refine Finset.sup_le_iff.mpr ?_
        intro n hn
        exact Nat.le_floor (lev_le_of_norm_le (hhigh n hn))
      calc (M₁ : ℝ) ≤ (⌊R' / (2 * Real.pi)⌋₊ : ℝ) := by exact_mod_cast hle
        _ ≤ R' / (2 * Real.pi) := Nat.floor_le (le_of_lt (by positivity : (0:ℝ) < R' / (2 * Real.pi)))
    have hM₀ge : R / (2 * Real.pi * Real.sqrt 3) ≤ (M₀ : ℝ) := by
      have hc : R / (2 * Real.pi * Real.sqrt 3) ≤
          (⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊ : ℝ) := Nat.le_ceil _
      have hc2 : (⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊ : ℝ) ≤ (M₀ : ℝ) := by
        rw [hM₀]
        exact_mod_cast le_max_right 1 ⌈R / (2 * Real.pi * Real.sqrt 3)⌉₊
      linarith
    have hRle : R ≤ 2 * Real.pi * Real.sqrt 3 * (M₀ : ℝ) := by
      have hd : 0 < 2 * Real.pi * Real.sqrt 3 := by positivity
      have h := mul_le_mul_of_nonneg_right hM₀ge hd.le
      rw [div_mul_cancel₀ _ (ne_of_gt hd)] at h
      linarith [h]
    have hM₁le2 : (M₁ : ℝ) ≤ 2 * Real.sqrt 3 * KH * (M₀ : ℝ) := by
      have hR'le : R' ≤ 2 * KH * (2 * Real.pi * Real.sqrt 3 * (M₀ : ℝ)) :=
        le_trans hR' (mul_le_mul_of_nonneg_left hRle (by positivity))
      calc (M₁ : ℝ) ≤ R' / (2 * Real.pi) := hM₁le
        _ ≤ (2 * KH * (2 * Real.pi * Real.sqrt 3 * (M₀ : ℝ))) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right hR'le (by positivity)
        _ = 2 * Real.sqrt 3 * KH * (M₀ : ℝ) := by field_simp
    have hlog : Real.log (M₁ : ℝ) - Real.log (M₀ : ℝ) ≤
        Real.log (2 * Real.sqrt 3 * KH) := by
      have hM₀pos : (0 : ℝ) < M₀ := by exact_mod_cast hM₀1
      have hM₁pos : (0 : ℝ) < M₁ := by exact_mod_cast lt_of_lt_of_le hM₀1 hM₀M₁
      have hc : 0 < 2 * Real.sqrt 3 * KH := by positivity
      have h1 : Real.log (M₁ : ℝ) ≤ Real.log (2 * Real.sqrt 3 * KH * (M₀ : ℝ)) :=
        Real.log_le_log hM₁pos hM₁le2
      rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hM₀pos)] at h1
      linarith
    have hlog23 : Real.log (2 * Real.sqrt 3) ≤ 3 := by
      have hpos : 0 < 2 * Real.sqrt 3 := by positivity
      have h := Real.log_le_sub_one_of_pos hpos
      nlinarith [Real.sqrt_nonneg 3, hs3]
    have hlog23KH : Real.log (2 * Real.sqrt 3 * KH) ≤ 3 + Real.log KH := by
      have hpos : 0 < 2 * Real.sqrt 3 := by positivity
      rw [Real.log_mul (ne_of_gt hpos) (ne_of_gt (by linarith : (0 : ℝ) < KH))]
      linarith
    have hconst : 26 / (8 * Real.pi ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h : (3 : ℝ) ^ 3 ≤ Real.pi ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt Real.pi_gt_three) 3
      norm_num at h ⊢
      linarith
    have hc0 : (0 : ℝ) ≤ 26 / (8 * Real.pi ^ 3) := by positivity
    have hcpos : (0 : ℝ) ≤ 1 + Real.log (2 * Real.sqrt 3 * KH) := by
      have hone : (1 : ℝ) ≤ 2 * Real.sqrt 3 * KH := by
        nlinarith [hKH, Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ 3 by norm_num)]
      have := Real.log_nonneg hone
      linarith
    calc (∑ n ∈ S, 1 / ‖Work.BoseB4.vec n‖ ^ 3)
        ≤ ∑ m ∈ Finset.Icc M₀ M₁,
            (26 * (m : ℝ) ^ 2) * (1 / (2 * Real.pi * (m : ℝ)) ^ 3) := hmain
      _ = (26 / (8 * Real.pi ^ 3)) * (∑ m ∈ Finset.Icc M₀ M₁, 1 / (m : ℝ)) := hsum
      _ ≤ (26 / (8 * Real.pi ^ 3)) * (1 + Real.log (M₁ : ℝ) - Real.log (M₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left hbnd hc0
      _ ≤ (26 / (8 * Real.pi ^ 3)) * (1 + Real.log (2 * Real.sqrt 3 * KH)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0
      _ ≤ 1 * (1 + (3 + Real.log KH)) := by
          refine mul_le_mul hconst ?_ hcpos (by norm_num)
          linarith
      _ ≤ 100 * (1 + Real.log KH) := by nlinarith [hlogKH]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty]
    nlinarith [hlogKH]

end Work.BoseB7AK.K15R
