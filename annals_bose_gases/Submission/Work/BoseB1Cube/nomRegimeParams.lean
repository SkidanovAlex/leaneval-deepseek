import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.fsRegimeAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.nomRegimeParams` — FS's parameter regime in its packaged form

This file closes the packaged regime statement `Work.BoseB1Cube.nomRegimeParams`:
there is `ε₀ > 0` (`≤ 1`) such that for every `μ > 0` with diluteness
`μa³ ≤ ε₀` FS's parameter block `paramsAt μ a = fsParams (μa³)` satisfies the
seven inequalities

* `K_B³(μa³)^{1/2} ≤ 1`, `1 ≤ K_ℓ`, `1 ≤ K_B`, `d ≤ 1`,
* `(R/(ℓ d))² ≤ K_B³(μa³)^{1/2}` (the support radius is small against the
  small-box side),
* `((1+d)/d)³ ≤ 8 μℓ³ K_B³(μa³)^{1/2}`,
* `(2μ^{-1/3}/ℓ)^{2M} μ^{-1/3} ℓ² ≤ 2^{2M}(μa³)^{M/3} ℓ³`.

Every one of them is a comparison of monomials `t^{c/323}` with `t = μa³`
(`Work.BoseBox.fsXp`), so the proof is exponent arithmetic:

* `d = t^{6/323}`, `K_B = t^{-6/323}`, `K_ℓ = t^{-3/646}`, `μℓ³ = t^{-166/323}`,
* `K_B³ t^{1/2} = t^{287/646}`, `μℓ³K_B³t^{1/2} = t^{-45/646}`,
  `μ^{-1/3} = a·t^{-1/3}`, `ℓ = a·t^{-163/323}`, hence
  `μ^{-1/3}/ℓ = t^{166/969}`;

the only two thresholds that are not automatic are `t ≤ 1` and
`t ≤ (a²/R²)^{646/341}` (the latter for the support-radius row), and both are
absorbed in `ε₀ = min(1/2, (a²/R²)^{646/341})`.

The rows `K_B³(μa³)^{1/2} ≤ 1`, `1 ≤ K_ℓ`, `1 ≤ K_B`, `(R/(ℓd))² ≤ …` are
reused from the proved parameter-regime module
`Submission.Work.BoseFixB1.fsRegimeAt`; the remaining three are proved here.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseB1Cube

open Work.BoseBox

set_option maxHeartbeats 1000000

/-! ## 1. The two scalar rows -/

/-- `d ≤ 1` for `μa³ ≤ 1`, since `d = (μa³)^{6/323} ≤ 1`. -/
lemma paramsAt_d_le_one {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) (ht : μ * a ^ 3 ≤ 1) :
    (Work.BoseBox.paramsAt μ a).d ≤ 1 := by
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  rw [Work.BoseFixB1.d_eq_fsXp μ a]
  exact fsXp_le_one ht0 ht (by norm_num)

/-- The small-box localisation bound `((1+d)/d)³ ≤ 8 μℓ³ K_B³(μa³)^{1/2}`:

`((1+d)/d)³ ≤ 8 d^{-3} = 8 (μa³)^{-18/323}` and
`μℓ³K_B³(μa³)^{1/2} = (μa³)^{-45/646} ≥ (μa³)^{-18/323}` for `μa³ ≤ 1`. -/
lemma one_add_d_div_d_cube_le {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    (ht1 : μ * a ^ 3 ≤ 1) :
    ((1 + (Work.BoseBox.paramsAt μ a).d) / (Work.BoseBox.paramsAt μ a).d) ^ 3
      ≤ 8 * (μ * Work.BoseBox.sideAt μ a ^ 3
          * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  have hd0 : 0 < (Work.BoseBox.paramsAt μ a).d := by
    rw [Work.BoseFixB1.d_eq_fsXp μ a]; exact fsXp_pos ht0
  have hd1 : (Work.BoseBox.paramsAt μ a).d ≤ 1 := paramsAt_d_le_one ha hμ ht1
  -- `((1+d)/d)³ ≤ (2/d)³ = 8 (d³)⁻¹`
  have hle : (1 + (Work.BoseBox.paramsAt μ a).d) / (Work.BoseBox.paramsAt μ a).d
      ≤ 2 / (Work.BoseBox.paramsAt μ a).d := by
    have h2 : (1 : ℝ) ≤ 1 / (Work.BoseBox.paramsAt μ a).d := by
      rw [one_le_div hd0]; exact hd1
    have h3 : (2 : ℝ) / (Work.BoseBox.paramsAt μ a).d
        = 1 / (Work.BoseBox.paramsAt μ a).d + 1 / (Work.BoseBox.paramsAt μ a).d := by
      ring
    rw [add_div, div_self (ne_of_gt hd0), h3]
    linarith
  have hcube : (2 / (Work.BoseBox.paramsAt μ a).d) ^ 3
      = 8 * (((Work.BoseBox.paramsAt μ a).d) ^ 3)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
    norm_num
  have hstep1 : ((1 + (Work.BoseBox.paramsAt μ a).d) / (Work.BoseBox.paramsAt μ a).d) ^ 3
      ≤ 8 * (((Work.BoseBox.paramsAt μ a).d) ^ 3)⁻¹ := by
    calc ((1 + (Work.BoseBox.paramsAt μ a).d) / (Work.BoseBox.paramsAt μ a).d) ^ 3
        ≤ (2 / (Work.BoseBox.paramsAt μ a).d) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hle 3
      _ = 8 * (((Work.BoseBox.paramsAt μ a).d) ^ 3)⁻¹ := hcube
  -- `8 (d³)⁻¹ ≤ 8 μℓ³K_B³(μa³)^{1/2}`
  have hstep2 : 8 * (((Work.BoseBox.paramsAt μ a).d) ^ 3)⁻¹
      ≤ 8 * (μ * Work.BoseBox.sideAt μ a ^ 3
          * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by
    have h6 : (((Work.BoseBox.paramsAt μ a).d) ^ 3)⁻¹ = fsXp (μ * a ^ 3) (-18) := by
      rw [Work.BoseFixB1.d_cube_eq ha hμ, fsXp_inv ht0]
    have h7 : μ * Work.BoseBox.sideAt μ a ^ 3
          * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))
        = fsXp (μ * a ^ 3) (-(45 / 2)) := by
      rw [show μ * Work.BoseBox.sideAt μ a ^ 3
            * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))
          = μ * Work.BoseBox.sideAt μ a ^ 3 * (Work.BoseBox.paramsAt μ a).KB ^ 3
            * (μ * a ^ 3) ^ (1 / 2 : ℝ) from by ring]
      exact Work.BoseFixB1.mu_ell_cube_KB3_half_eq ha hμ
    rw [h6, h7]
    have hmono := fsXp_le_fsXp (t := μ * a ^ 3) (a := (-18 : ℝ)) (b := (-(45 / 2) : ℝ))
      ht0 ht1 (by norm_num)
    linarith
  exact le_trans hstep1 hstep2

/-- The `M`-row of the packaged regime:
`(2μ^{-1/3}/ℓ)^{2M} μ^{-1/3} ℓ² ≤ 2^{2M}(μa³)^{M/3}ℓ³`.

Indeed `μ^{-1/3}/ℓ = (μa³)^{166/969}`, so the left-hand side divided by
`2^{2M}ℓ³` is `(μa³)^{(332M+166)/969}` while the right-hand side divided by
`2^{2M}ℓ³` is `(μa³)^{M/3}`, and `323M ≤ 332M + 166`. -/
lemma lastConjAux {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) (ht1 : μ * a ^ 3 ≤ 1) (M : ℕ) :
    (2 * μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ a) ^ (2 * M)
        * μ ^ (-(1 / 3) : ℝ) * Work.BoseBox.sideAt μ a ^ 2
      ≤ (2 : ℝ) ^ (2 * M) * (μ * a ^ 3) ^ ((M : ℝ) / 3)
          * Work.BoseBox.sideAt μ a ^ 3 := by
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  have hℓ0 : 0 < Work.BoseBox.sideAt μ a := Work.BoseBox.sideAt_pos hμ ha
  -- `μ^{-1/3}/ℓ = (μa³)^{166/969}`
  have hq : μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ a = fsXp (μ * a ^ 3) (166 / 3) := by
    rw [Work.BoseFixB1.mu_inv_third_eq ha hμ, Work.BoseFixB1.sideAt_eq_fsXp ha hμ,
      mul_div_mul_left _ _ (ne_of_gt ha), div_eq_mul_inv, fsXp_inv ht0 (-163), neg_neg,
      fsXp_mul ht0]
    congr 1
    norm_num
  have hx : μ ^ (-(1 / 3) : ℝ) = Work.BoseBox.sideAt μ a * fsXp (μ * a ^ 3) (166 / 3) := by
    rw [← hq, mul_comm]
    exact (div_mul_cancel₀ (μ ^ (-(1 / 3) : ℝ)) (ne_of_gt hℓ0)).symm
  -- the two clean forms of the powers of `μa³`
  have hqpow : (fsXp (μ * a ^ 3) (166 / 3)) ^ (2 * M + 1)
      = fsXp (μ * a ^ 3) ((166 / 3) * ((2 * M + 1 : ℕ) : ℝ)) :=
    fsXp_pow ht0.le (166 / 3) (2 * M + 1)
  have hTm : (μ * a ^ 3) ^ ((M : ℝ) / 3) = fsXp (μ * a ^ 3) ((M : ℝ) * (323 / 3)) := by
    rw [fsXp]
    congr 1
    ring
  have hle : fsXp (μ * a ^ 3) ((166 / 3) * ((2 * M + 1 : ℕ) : ℝ))
      ≤ fsXp (μ * a ^ 3) ((M : ℝ) * (323 / 3)) := by
    refine fsXp_le_fsXp ht0 ht1 ?_
    push_cast
    linarith
  have key : (fsXp (μ * a ^ 3) (166 / 3)) ^ (2 * M + 1)
      ≤ (μ * a ^ 3) ^ ((M : ℝ) / 3) := by
    rw [hTm, hqpow]
    exact hle
  calc (2 * μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ a) ^ (2 * M)
        * μ ^ (-(1 / 3) : ℝ) * Work.BoseBox.sideAt μ a ^ 2
      = (2 * fsXp (μ * a ^ 3) (166 / 3)) ^ (2 * M)
          * (Work.BoseBox.sideAt μ a * fsXp (μ * a ^ 3) (166 / 3))
          * Work.BoseBox.sideAt μ a ^ 2 := by
        rw [show 2 * μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ a
              = 2 * (μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ a) from mul_div_assoc 2 _ _,
          hq, hx]
    _ = (2 : ℝ) ^ (2 * M) * (fsXp (μ * a ^ 3) (166 / 3)) ^ (2 * M + 1)
          * Work.BoseBox.sideAt μ a ^ 3 := by
        rw [mul_pow, pow_succ]
        ring
    _ ≤ (2 : ℝ) ^ (2 * M) * (μ * a ^ 3) ^ ((M : ℝ) / 3)
          * Work.BoseBox.sideAt μ a ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left key (by positivity)) (by positivity)

/-! ## 2. The packaged statement -/

theorem nomRegimeParams {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε₀ →
      (Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ) ≤ 1 ∧
      1 ≤ (Work.BoseBox.paramsAt μ a).Kl ∧ 1 ≤ (Work.BoseBox.paramsAt μ a).KB
        ∧ (Work.BoseBox.paramsAt μ a).d ≤ 1 ∧
      (R / (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)) ^ 2
        ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ) ∧
      ((1 + (Work.BoseBox.paramsAt μ a).d) / (Work.BoseBox.paramsAt μ a).d) ^ 3
        ≤ 8 * (μ * Work.BoseBox.sideAt μ a ^ 3
            * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))) ∧
      (2 * μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ a) ^ (2 * (Work.BoseBox.paramsAt μ a).M)
          * μ ^ (-(1 / 3) : ℝ) * Work.BoseBox.sideAt μ a ^ 2
        ≤ (2 : ℝ) ^ (2 * (Work.BoseBox.paramsAt μ a).M)
            * (μ * a ^ 3) ^ (((Work.BoseBox.paramsAt μ a).M : ℕ) / 3 : ℝ)
            * Work.BoseBox.sideAt μ a ^ 3 := by
  refine ⟨min (1 / 2) ((a ^ 2 / R ^ 2) ^ (646 / 341 : ℝ)), ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  · exact le_trans (min_le_left _ _) (by norm_num)
  · intro μ hμ ht
    have ht1 : μ * a ^ 3 ≤ 1 := le_trans ht (le_trans (min_le_left _ _) (by norm_num))
    have h5 : μ * a ^ 3 ≤ (a ^ 2 / R ^ 2) ^ (646 / 341 : ℝ) := le_trans ht (min_le_right _ _)
    refine ⟨Work.BoseFixB1.kb3_half_le_one ha hμ ht1,
      Work.BoseFixB1.one_le_Kl hμ ha ht1,
      Work.BoseFixB1.one_le_KB hμ ha ht1,
      paramsAt_d_le_one ha hμ ht1, ?_, one_add_d_div_d_cube_le ha hμ ht1,
      lastConjAux ha hμ ht1 (Work.BoseBox.paramsAt μ a).M⟩
    have h := Work.BoseFixB1.RsbSide_sq_le_fb ha hR hμ h5
    rw [mul_comm (Work.BoseBox.sideAt μ a) (Work.BoseBox.paramsAt μ a).d]
    exact h

end Work.BoseB1Cube
