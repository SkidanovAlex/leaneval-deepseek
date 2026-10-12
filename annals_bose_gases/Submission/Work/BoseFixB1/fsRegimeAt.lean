import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.Regime.inv_third_le_sideAt
import Submission.Work.BoseFixB1.Regime.muA_le_muA_ell_cube_KB3
import Submission.Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.fsRegimeAt` — the elementary FS regime at the parameter block

FS's parameters at the diluteness `t = μ A³` are the monomials
`d = t^{6/323}`, `K_ℓ = t^{-3/646}`, `K_B = t^{-6/323}`, `M = mValue = 48`
(`Work.BoseBox.fsParams`) and the box side is `ℓ = sideAt μ A = A t^{-163/323}`.
Consequently *every* elementary comparison of the FS regime — the small-box
occupation `μ(dℓ)³ ≥ 1`, the support-radius bound `(R/dℓ)² ≤ K_B³(μA³)^{1/2}`,
`ℓ ≥ μ^{-1/3}`, the good-set margin `ℓ(1+d)/2 - 2μ^{-1/3} ≥ 0`, … — holds as soon
as the diluteness `μA³` is below an explicit positive threshold, and this lemma
collects them: `ε₀` is the minimum of the finitely many individual thresholds, so
it is allowed to depend on the *fixed* `A` and `R`.

All constants here are free: the lemma is pure bookkeeping on
`fsXp t c = t^{c/323}` (`Work.BoseFixB1.RegimeAux`), the individual estimates
being supplied by the `Work.BoseFixB1.Regime.*` lemmas (and, for the two
diluteness-monotone comparisons `R/(dℓ)` and the good-set margin, by the local
lemmas `RsbSide_sq_le_fb`, `ell_residual_nonneg_fb` below).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixB1

open Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The remaining per-conjunct regime facts -/

/-- `K_B³ (μA³)^{1/2} ≤ 1` for `μA³ ≤ 1`: `K_B³(μA³)^{1/2} = (μA³)^{287/646}`. -/
lemma kb3_half_le_one {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [KB3_half_eq hA hμ]
  exact fsXp_le_one ht0 ht (by norm_num)

/-- `(d³)⁻¹ ≤ K_B³`: both sides are `(μA³)^{-18/323}`, so this is an identity. -/
lemma d_cube_inv_le {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    ((paramsAt μ A).d ^ 3)⁻¹ ≤ (paramsAt μ A).KB ^ 3 := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  have h1 : (paramsAt μ A).KB ^ 3 = fsXp (μ * A ^ 3) (-18) := by
    rw [KB_eq_fsXp, fsXp_pow ht0.le]; norm_num
  have h2 : ((paramsAt μ A).d ^ 3)⁻¹ = fsXp (μ * A ^ 3) (-18) := by
    rw [d_cube_eq hA hμ, fsXp_inv ht0]
  rw [h1, h2]

/-- `(μA³)^{M/3} ≤ K_B³(μA³)^{1/2}` for `μA³ ≤ 1`: the left side is
`(μA³)^{16}` and the right one `(μA³)^{287/646}`. -/
lemma t_pow_mValue_le {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    (μ * A ^ 3) ^ ((mValue : ℝ) / 3)
      ≤ (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [mValue_div_three_eq_fsXp, KB3_half_eq hA hμ]
  exact fsXp_le_fsXp ht0 ht (by norm_num [mValue])

/-- FS's regularity `M = mValue = 48 ≥ 1`. -/
lemma M_ge_one (μ A : ℝ) : 1 ≤ (paramsAt μ A).M := by
  rw [M_eq_mValue]
  norm_num [mValue]

/-- The support-radius comparison against the small-box side, at diluteness
`μA³ ≤ (A²/R²)^{646/341}`.  This is the statement of the requested lemma
`Work.BoseFixB1.Regime.RsbSide_sq_le`, proved here as well so that the assembly
below does not depend on it. -/
lemma RsbSide_sq_le_fb {A R μ : ℝ} (hA : 0 < A) (hR : 0 < R) (hμ : 0 < μ)
    (ht : μ * A ^ 3 ≤ (A ^ 2 / R ^ 2) ^ (646 / 341 : ℝ)) :
    (R / ((paramsAt μ A).d * sideAt μ A)) ^ 2
      ≤ (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hAR : (0 : ℝ) < A ^ 2 / R ^ 2 := by positivity
  -- (1) `t^{341/646} ≤ A²/R²`
  have h1 : (μ * A ^ 3) ^ (341 / 646 : ℝ) ≤ A ^ 2 / R ^ 2 := by
    calc (μ * A ^ 3) ^ (341 / 646 : ℝ)
        ≤ ((A ^ 2 / R ^ 2) ^ (646 / 341 : ℝ)) ^ (341 / 646 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht (by norm_num)
      _ = (A ^ 2 / R ^ 2) ^ ((646 / 341 : ℝ) * (341 / 646)) :=
          (Real.rpow_mul hAR.le _ _).symm
      _ = A ^ 2 / R ^ 2 := by
          rw [show (646 / 341 : ℝ) * (341 / 646) = 1 by norm_num, Real.rpow_one]
  -- (2) `R²/A² ≤ t^{-341/646}`
  have h2 : R ^ 2 / A ^ 2 ≤ (μ * A ^ 3) ^ (-(341 / 646) : ℝ) := by
    have h3 : (A ^ 2 / R ^ 2)⁻¹ ≤ ((μ * A ^ 3) ^ (341 / 646 : ℝ))⁻¹ :=
      (inv_le_inv₀ hAR (Real.rpow_pos_of_pos ht0 (341 / 646))).mpr h1
    have h4 : (A ^ 2 / R ^ 2)⁻¹ = R ^ 2 / A ^ 2 := by field_simp
    rw [Real.rpow_neg ht0.le, ← h4]
    exact h3
  have h2' : R ^ 2 / A ^ 2 ≤ fsXp (μ * A ^ 3) (-(341 / 2)) := by
    rw [fsXp, show (-(341 / 2) : ℝ) / 323 = -(341 / 646) by norm_num]
    exact h2
  have hdl : (0 : ℝ) < (paramsAt μ A).d * sideAt μ A := by
    rw [d_mul_sideAt_eq hA hμ]
    exact mul_pos hA (fsXp_pos ht0)
  have hdl2 : ((paramsAt μ A).d * sideAt μ A) ^ 2
      = A ^ 2 * fsXp (μ * A ^ 3) (-314) := by
    rw [d_mul_sideAt_eq hA hμ, mul_pow, fsXp_pow ht0.le]
    have : (-157 : ℝ) * ((2 : ℕ) : ℝ) = -314 := by norm_num
    rw [this]
  rw [div_pow, div_le_iff₀ (pow_pos hdl 2), hdl2]
  rw [KB3_half_eq hA hμ]
  have hmul : fsXp (μ * A ^ 3) (287 / 2) * (A ^ 2 * fsXp (μ * A ^ 3) (-314))
      = A ^ 2 * fsXp (μ * A ^ 3) (-(341 / 2)) := by
    rw [mul_comm (fsXp (μ * A ^ 3) (287 / 2)) (A ^ 2 * fsXp (μ * A ^ 3) (-314)),
      mul_assoc, fsXp_mul ht0]
    have harg : (-314 : ℝ) + 287 / 2 = -(341 / 2) := by norm_num
    rw [harg]
  rw [hmul]
  have h5 : R ^ 2 = A ^ 2 * (R ^ 2 / A ^ 2) := by field_simp
  rw [h5]
  exact mul_le_mul_of_nonneg_left h2' (by positivity)

/-- The good-set margin of the sliding localisation is nonnegative at diluteness
`μA³ ≤ (1/4)^{969/166}`.  This is the statement of the requested lemma
`Work.BoseFixB1.Regime.ell_residual_nonneg`, proved here as well so that the
assembly below does not depend on it. -/
lemma ell_residual_nonneg_fb {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (ht : μ * A ^ 3 ≤ (1 / 4) ^ (969 / 166 : ℝ)) :
    0 ≤ (1 / 2) * sideAt μ A * (1 + (paramsAt μ A).d) - 2 * μ ^ (-(1 / 3) : ℝ) := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hℓ : sideAt μ A = A * (μ * A ^ 3) ^ (-(163 / 323) : ℝ) := sideAt_eq_rpow hA hμ
  have hm : μ ^ (-(1 / 3) : ℝ) = A * (μ * A ^ 3) ^ (-(1 / 3) : ℝ) := by
    have hA3 : (0 : ℝ) < A ^ 3 := by positivity
    have h2 : ((A : ℝ) ^ 3) ^ (-(1 / 3) : ℝ) = A⁻¹ := by
      rw [show ((A : ℝ) ^ 3) = A ^ ((3 : ℕ) : ℝ) by exact (Real.rpow_natCast A 3).symm]
      rw [← Real.rpow_mul hA.le]
      norm_num
      rw [Real.rpow_neg hA.le 1, Real.rpow_one]
    calc μ ^ (-(1 / 3) : ℝ) = ((μ * A ^ 3) / A ^ 3) ^ (-(1 / 3) : ℝ) := by
          rw [show (μ * A ^ 3) / A ^ 3 = μ by field_simp]
      _ = (μ * A ^ 3) ^ (-(1 / 3) : ℝ) * A := by
          rw [Real.div_rpow ht0.le hA3.le, h2, div_inv_eq_mul]
      _ = A * (μ * A ^ 3) ^ (-(1 / 3) : ℝ) := by ring
  -- `4 ≤ t^{-166/969}`
  have h4 : (4 : ℝ) ≤ (μ * A ^ 3) ^ (-(166 / 969) : ℝ) := by
    have hle : (μ * A ^ 3) ^ (166 / 969 : ℝ) ≤ 1 / 4 := by
      calc (μ * A ^ 3) ^ (166 / 969 : ℝ)
          ≤ ((1 / 4) ^ (969 / 166 : ℝ)) ^ (166 / 969 : ℝ) :=
            Real.rpow_le_rpow ht0.le ht (by norm_num)
        _ = (1 / 4) ^ ((969 / 166 : ℝ) * (166 / 969)) :=
            (Real.rpow_mul (by norm_num) _ _).symm
        _ = 1 / 4 := by
            rw [show (969 / 166 : ℝ) * (166 / 969) = 1 by norm_num, Real.rpow_one]
    have hp : (0 : ℝ) < (μ * A ^ 3) ^ (166 / 969 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have h3 : ((1 : ℝ) / 4)⁻¹ ≤ ((μ * A ^ 3) ^ (166 / 969 : ℝ))⁻¹ :=
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 4) hp).mpr hle
    rw [Real.rpow_neg ht0.le]
    simpa using h3
  -- `ℓ = t^{-166/969} · μ^{-1/3}`
  have hsplit : sideAt μ A = (μ * A ^ 3) ^ (-(166 / 969) : ℝ) * μ ^ (-(1 / 3) : ℝ) := by
    rw [hℓ, hm]
    have h1 : (μ * A ^ 3) ^ (-(163 / 323) : ℝ)
        = (μ * A ^ 3) ^ (-(166 / 969) : ℝ) * (μ * A ^ 3) ^ (-(1 / 3) : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      norm_num
    rw [h1]
    ring
  have hμ13 : (0 : ℝ) ≤ μ ^ (-(1 / 3) : ℝ) := Real.rpow_nonneg hμ.le _
  have hℓge : 4 * μ ^ (-(1 / 3) : ℝ) ≤ sideAt μ A := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right h4 hμ13
  have hd : (0 : ℝ) ≤ (paramsAt μ A).d := by
    rw [d_eq_fsXp]; exact fsXp_nonneg ht0.le
  have hℓ0 : (0 : ℝ) ≤ sideAt μ A := le_trans (by positivity) hℓge
  have hprod : (0 : ℝ) ≤ sideAt μ A * (paramsAt μ A).d := mul_nonneg hℓ0 hd
  linarith [hℓge, hprod]

/-! ## 2. The regime bundle -/

theorem fsRegimeAt {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * A ^ 3 ≤ ε₀ →
      (1 ≤ (Work.BoseBox.paramsAt μ A).Kl) ∧ (1 ≤ (Work.BoseBox.paramsAt μ A).KB) ∧
      ((Work.BoseBox.paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) ≤ 1) ∧
      (1 ≤ μ * ((Work.BoseBox.paramsAt μ A).d * Work.BoseBox.sideAt μ A) ^ 3) ∧
      ((R / ((Work.BoseBox.paramsAt μ A).d * Work.BoseBox.sideAt μ A)) ^ 2
        ≤ (Work.BoseBox.paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)) ∧
      (((Work.BoseBox.paramsAt μ A).d ^ 3)⁻¹ ≤ (Work.BoseBox.paramsAt μ A).KB ^ 3) ∧
      (μ * A ≤ μ ^ 2 * A * (Work.BoseBox.sideAt μ A) ^ 3 * (Work.BoseBox.paramsAt μ A).KB ^ 3
          * (μ * A ^ 3) ^ (1 / 2 : ℝ)) ∧
      ((μ * A ^ 3) ^ ((Work.BoseBox.mValue : ℝ) / 3)
        ≤ (Work.BoseBox.paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)) ∧
      (μ ^ (-(1 / 3) : ℝ) ≤ Work.BoseBox.sideAt μ A) ∧
      (0 ≤ (1 / 2) * Work.BoseBox.sideAt μ A * (1 + (Work.BoseBox.paramsAt μ A).d)
          - 2 * μ ^ (-(1 / 3) : ℝ)) ∧
      (1 ≤ (Work.BoseBox.paramsAt μ A).M) := by
  have hAR : (0 : ℝ) < A ^ 2 / R ^ 2 := by positivity
  -- the threshold is the minimum of the (finitely many) individual ones
  refine ⟨min (min (1 / 2) ((A ^ 2 / R ^ 2) ^ (646 / 341 : ℝ)))
    ((1 / 4) ^ (969 / 166 : ℝ)), ?_, ?_⟩
  · exact lt_min (lt_min (by norm_num) (Real.rpow_pos_of_pos hAR _))
      (Real.rpow_pos_of_pos (by norm_num) _)
  · intro μ hμ ht
    -- the diluteness thresholds
    have h1 : μ * A ^ 3 ≤ 1 := le_trans ht (le_trans (min_le_left _ _) (by norm_num))
    have h5 : μ * A ^ 3 ≤ (A ^ 2 / R ^ 2) ^ (646 / 341 : ℝ) :=
      le_trans ht (le_trans (min_le_left _ _) (min_le_right _ _))
    have h10 : μ * A ^ 3 ≤ (1 / 4) ^ (969 / 166 : ℝ) := le_trans ht (min_le_right _ _)
    exact ⟨one_le_Kl hμ hA h1, one_le_KB hμ hA h1, kb3_half_le_one hA hμ h1,
      Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube hA hμ h1,
      RsbSide_sq_le_fb hA hR hμ h5,
      d_cube_inv_le hA hμ,
      Work.BoseFixB1.Regime.muA_le_muA_ell_cube_KB3 hA hμ h1,
      t_pow_mValue_le hA hμ h1,
      Work.BoseFixB1.Regime.inv_third_le_sideAt hA hμ h1,
      ell_residual_nonneg_fb hA hμ h10,
      M_ge_one μ A⟩

end Work.BoseFixB1
