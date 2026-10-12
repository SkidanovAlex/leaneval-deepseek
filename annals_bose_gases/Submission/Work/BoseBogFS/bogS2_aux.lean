import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.bogMeshInvSqLe
import Submission.Work.BoseBogFS.bogSideConds
import Submission.Work.BoseBogFS.bogSumAux
import Submission.Work.BoseBogFS.cubeMomSums
import Submission.Work.BoseBogFS.tauScRad_sub_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogS2_aux` — the region-B sum bound of the clean row (auxiliary lemmas)

This module prepares `Work.BoseBogFS.bogS2_sum_le`.  See the target file for the mathematics.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The uniform constant -/

/-- The constant of the region-B sum: it dominates `bogBs v R`, `bogVs v R ρ μ`, `bogVmaxt` and
`bogOscM v R ρ μ · X^{-3}` on the whole admissible region. -/
def bogS2Cst (v : E3 → ℝ) (R : ℝ) : ℝ :=
  1 + bogKB * (1 + R) ^ 3 / a v
    + 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3 / (a v) ^ 2)

lemma one_le_bogS2Cst {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < a v) :
    1 ≤ bogS2Cst v R := by
  have h1 : (0 : ℝ) ≤ (1 + R) ^ 3 := by positivity
  have h2 : 0 ≤ bogKB * (1 + R) ^ 3 / a v :=
    div_nonneg (mul_nonneg bogKB_nonneg h1) hav.le
  have h3 : 0 ≤ 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
      / (a v) ^ 2) := by
    refine mul_nonneg (by norm_num) (div_nonneg ?_ (sq_nonneg _))
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg h1)
      (Real.sqrt_nonneg _)) Real.pi_pos.le) (Real.sqrt_nonneg _)
  rw [bogS2Cst]
  linarith [h2, h3]

lemma bogS2Cst_pos {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < a v) :
    0 < bogS2Cst v R := lt_of_lt_of_le one_pos (one_le_bogS2Cst hR hav)

/-! ## 2. The parameter regime

`X = fsX v μ` is the `1/323`-power of the diluteness; on `Core` it is tiny (`≤ 10^{-12}`).
The exact identities used below are `c₁ = ½X^{1/2}√(μ/ρ)`, `c₂ = ½X^{-11/2}√(μ/ρ)`,
`ℓ = a(v)X^{-163}`, `ℓ√(ρa) = X^{-3/2}√(ρ/μ)` and `Δ = 2π√3·X·c₁`. -/

/-- `fsX v μ` is by definition the `1/323`-power of the diluteness. -/
lemma bogS2_fsX_rpow (v : E3 → ℝ) (μ : ℝ) :
    fsX v μ = (dil v μ) ^ ((1 : ℝ) / 323) := rfl

lemma bogS2_fsX_pos {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    0 < fsX v μ := fsX_pos hC.hμ hav

lemma bogS2_fsX_nonneg {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    0 ≤ fsX v μ := (bogS2_fsX_pos hC hav).le

lemma bogS2_fsX_le_one {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    fsX v μ ≤ 1 := by
  rw [bogS2_fsX_rpow]
  exact Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num)

/-- `X = fsX v μ ≤ 10^{-12}` (from the numeric row `dil^{1/1292} ≤ 1/1024` of `Core`). -/
lemma bogS2_fsX_le_pow {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    fsX v μ ≤ 1 / 10 ^ 12 := by
  have h4 : fsX v μ = ((dil v μ) ^ ((1 : ℝ) / 1292)) ^ 4 := by
    rw [bogS2_fsX_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hC.hD0.le]
    norm_num
  rw [h4]
  have hY0 : (0 : ℝ) ≤ (dil v μ) ^ ((1 : ℝ) / 1292) := Real.rpow_nonneg hC.hD0.le _
  calc ((dil v μ) ^ ((1 : ℝ) / 1292)) ^ 4 ≤ (1 / 1024) ^ 4 := pow_le_pow_left₀ hY0 hC.hDs 4
    _ ≤ 1 / 10 ^ 12 := by norm_num

/-- `X^323 = dil v μ`. -/
lemma bogS2_fsX_pow {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    (fsX v μ) ^ 323 = dil v μ := by
  rw [bogS2_fsX_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hC.hD0.le]
  norm_num

/-! ## 1b. Two elementary `sqrt` helpers -/

lemma bogS2_sqrt_le_of_le_sq {a b : ℝ} (h : a ≤ b ^ 2) (hb : 0 ≤ b) : Real.sqrt a ≤ b := by
  have h1 : Real.sqrt a ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hb] at h1

lemma bogS2_le_sqrt_of_sq_le {a b : ℝ} (h : a ^ 2 ≤ b) (ha : 0 ≤ a) : a ≤ Real.sqrt b := by
  have h1 : Real.sqrt (a ^ 2) ≤ Real.sqrt b := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha] at h1

/-- `√(μ/ρ) ≤ 11/10`. -/
lemma bogS2_sqrt_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    Real.sqrt (μ / ρ) ≤ 11 / 10 := by
  refine bogS2_sqrt_le_of_le_sq (a := μ / ρ) (b := 11 / 10) ?_ (by norm_num)
  have h : μ / ρ ≤ 10 / 9 := by
    rw [div_le_iff₀ hC.hρ0]; linarith [hC.hρlo]
  linarith [h]

/-- `9/10 ≤ √(μ/ρ)`. -/
lemma bogS2_sqrt_ge {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    9 / 10 ≤ Real.sqrt (μ / ρ) := by
  refine bogS2_le_sqrt_of_sq_le (a := 9 / 10) (b := μ / ρ) ?_ (by norm_num)
  have h : 10 / 11 ≤ μ / ρ := by
    rw [le_div_iff₀ hC.hρ0]; linarith [hC.hρhi]
  linarith [h]

/-- `9/10 ≤ √(ρ/μ)`. -/
lemma bogS2_sqrt_rho_ge {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    9 / 10 ≤ Real.sqrt (ρ / μ) := by
  refine bogS2_le_sqrt_of_sq_le (a := 9 / 10) (b := ρ / μ) ?_ (by norm_num)
  have h : 9 / 10 ≤ ρ / μ := by
    rw [le_div_iff₀ hC.hμ]; linarith [hC.hρlo]
  linarith [h]

/-- `√(ρ/μ) ≤ 11/10`. -/
lemma bogS2_sqrt_rho_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    Real.sqrt (ρ / μ) ≤ 11 / 10 := by
  refine bogS2_sqrt_le_of_le_sq (a := ρ / μ) (b := 11 / 10) ?_ (by norm_num)
  have h : ρ / μ ≤ 11 / 10 := by
    rw [div_le_iff₀ hC.hμ]; linarith [hC.hρhi]
  linarith [h]

/-- `√(dil v μ) = X^{323/2}` with `X = fsX v μ`. -/
lemma bogS2_sqrt_dil {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    Real.sqrt (dil v μ) = (fsX v μ) ^ ((323 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← bogS2_fsX_pow hC, ← Real.rpow_natCast,
    ← Real.rpow_mul (bogS2_fsX_nonneg hC hav)]
  norm_num

/-- `√(μ·a v) = X^{323/2}/a v`. -/
lemma bogS2_sqrt_mua {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    Real.sqrt (μ * a v) = (fsX v μ) ^ ((323 : ℝ) / 2) / a v := by
  rw [sqrt_mua v μ hC.hμ hav, bogS2_sqrt_dil hC hav]

/-- `ℓ = a(v)·X^{-163}`. -/
lemma bogS2_ell_eq {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    ell v μ = a v * (fsX v μ) ^ (-(163 : ℝ)) := by
  have hma : 0 < μ * a v := mul_pos hC.hμ hav
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have hX : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have h1 : ell v μ = (fsX v μ) ^ (-(3 / 2 : ℝ)) * (μ * a v) ^ (-(1 / 2 : ℝ)) := by
    rw [ell_eq_boxSide, paramsAt_Kl]
    have h2 : (dil v μ) ^ (-((3 : ℝ) / 646)) = (fsX v μ) ^ (-(3 / 2 : ℝ)) := by
      rw [bogS2_fsX_rpow, ← Real.rpow_mul hC.hD0.le]
      norm_num
    rw [h2]
  have h3 : (μ * a v) ^ (-(1 / 2 : ℝ)) = a v * (fsX v μ) ^ (-((323 : ℝ) / 2)) := by
    rw [Real.rpow_neg hma.le, ← Real.sqrt_eq_rpow, bogS2_sqrt_mua hC hav, inv_div,
      div_eq_mul_inv, ← Real.rpow_neg hX0]
  rw [h1, h3,
    show (fsX v μ) ^ (-(3 / 2 : ℝ)) * (a v * (fsX v μ) ^ (-((323 : ℝ) / 2)))
      = a v * ((fsX v μ) ^ (-(3 / 2 : ℝ)) * (fsX v μ) ^ (-((323 : ℝ) / 2))) by ring,
    ← Real.rpow_add hX, show -(3 / 2 : ℝ) + -((323 : ℝ) / 2) = -(163 : ℝ) by norm_num]

/-- `ℓ·√(ρa) = X^{-3/2}·√(ρ/μ)`. -/
lemma bogS2_ell_mul_sqrt {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    ell v μ * Real.sqrt (ρ * a v) = (fsX v μ) ^ (-(3 / 2 : ℝ)) * Real.sqrt (ρ / μ) := by
  have hma : 0 < μ * a v := mul_pos hC.hμ hav
  have hX : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have ha0 : a v ≠ 0 := ne_of_gt hav
  have hμ0 : μ ≠ 0 := ne_of_gt hC.hμ
  have h1 : Real.sqrt (ρ * a v) = Real.sqrt (μ * a v) * Real.sqrt (ρ / μ) := by
    rw [← Real.sqrt_mul hma.le]
    congr 1
    have hμρ : μ * (ρ / μ) = ρ := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ ρ hμ0]
    rw [show μ * a v * (ρ / μ) = a v * (μ * (ρ / μ)) by ring, hμρ]
    ring
  rw [bogS2_ell_eq hC hav, h1, bogS2_sqrt_mua hC hav]
  have h3 : a v * ((fsX v μ) ^ ((323 : ℝ) / 2) / a v) = (fsX v μ) ^ ((323 : ℝ) / 2) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha0]
  rw [show a v * (fsX v μ) ^ (-(163 : ℝ))
        * ((fsX v μ) ^ ((323 : ℝ) / 2) / a v * Real.sqrt (ρ / μ))
      = (fsX v μ) ^ (-(163 : ℝ))
        * (a v * ((fsX v μ) ^ ((323 : ℝ) / 2) / a v)) * Real.sqrt (ρ / μ) by ring,
    h3]
  rw [show (fsX v μ) ^ (-(163 : ℝ)) * (fsX v μ) ^ ((323 : ℝ) / 2)
      = (fsX v μ) ^ (-(3 / 2 : ℝ)) by
    rw [← Real.rpow_add hX]; norm_num]

lemma bogS2_mesh_ge {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    5 * (fsX v μ) ^ ((3 : ℝ) / 2) ≤ bogMesh v ρ μ := by
  have hP : 0 < ρ * a v := mul_pos hC.hρ0 hav
  have hℓ : 0 < ell v μ := sb_ell_pos hav hC
  have hX : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hs : 0 < Real.sqrt (ρ * a v) := Real.sqrt_pos.mpr hP
  have hkey := bogS2_ell_mul_sqrt hC hav
  have hpos : 0 < ell v μ * Real.sqrt (ρ * a v) := mul_pos hℓ hs
  rw [bogMesh, div_div, le_div_iff₀ hpos, hkey,
    show 5 * (fsX v μ) ^ ((3 : ℝ) / 2)
        * ((fsX v μ) ^ (-(3 / 2 : ℝ)) * Real.sqrt (ρ / μ))
      = 5 * ((fsX v μ) ^ ((3 : ℝ) / 2) * (fsX v μ) ^ (-(3 / 2 : ℝ))) * Real.sqrt (ρ / μ)
      by ring]
  have h0 : (fsX v μ) ^ ((3 : ℝ) / 2) * (fsX v μ) ^ (-(3 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hX, show (3 : ℝ) / 2 + -(3 / 2 : ℝ) = 0 by norm_num,
      Real.rpow_zero]
  rw [h0, mul_one]
  have hsρ : Real.sqrt (ρ / μ) ≤ 11 / 10 := bogS2_sqrt_rho_le hC
  have h5 : 5 * (11 / 10) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  nlinarith [h5, hsρ, Real.sqrt_nonneg (ρ / μ)]

/-- `δ ≤ 9·X^{3/2}`. -/
lemma bogS2_mesh_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    bogMesh v ρ μ ≤ 9 * (fsX v μ) ^ ((3 : ℝ) / 2) := by
  have hP : 0 < ρ * a v := mul_pos hC.hρ0 hav
  have hℓ : 0 < ell v μ := sb_ell_pos hav hC
  have hX : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hs : 0 < Real.sqrt (ρ * a v) := Real.sqrt_pos.mpr hP
  have hkey := bogS2_ell_mul_sqrt hC hav
  have hpos : 0 < ell v μ * Real.sqrt (ρ * a v) := mul_pos hℓ hs
  have hsρ : 9 / 10 ≤ Real.sqrt (ρ / μ) := bogS2_sqrt_rho_ge hC
  rw [bogMesh, div_div, div_le_iff₀ hpos, hkey]
  rw [show 9 * (fsX v μ) ^ ((3 : ℝ) / 2)
      * ((fsX v μ) ^ (-(3 / 2 : ℝ)) * Real.sqrt (ρ / μ))
      = 9 * ((fsX v μ) ^ ((3 : ℝ) / 2) * (fsX v μ) ^ (-(3 / 2 : ℝ))) * Real.sqrt (ρ / μ)
      by ring]
  have h0 : (fsX v μ) ^ ((3 : ℝ) / 2) * (fsX v μ) ^ (-(3 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hX, show (3 : ℝ) / 2 + -(3 / 2 : ℝ) = 0 by norm_num,
      Real.rpow_zero]
  rw [h0, mul_one]
  have h9 : 2 * Real.pi ≤ 9 * (9 / 10) := by
    have := Real.pi_le_four
    linarith
  nlinarith [h9, hsρ]

/-- `δ ≤ 1` on the diluteness window. -/
lemma bogS2_mesh_le_one {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v)
    (hX : fsX v μ ≤ 1 / 10 ^ 12) : bogMesh v ρ μ ≤ 1 := by
  have h1 := bogS2_mesh_le hC hav
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have h2 : (fsX v μ) ^ ((3 : ℝ) / 2) ≤ 1 / 10 ^ 4 := by
    have h3 : (fsX v μ) ^ ((3 : ℝ) / 2) ≤ (fsX v μ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (bogS2_fsX_pos hC hav) (bogS2_fsX_le_one hC)
        (by norm_num)
    rw [Real.rpow_one] at h3
    linarith [h3, hX]
  linarith [h1, h2]

/-- `c₁ ≤ X^{1/2}`. -/
lemma bogS2_c1_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    bogC1 v ρ μ ≤ (fsX v μ) ^ ((1 : ℝ) / 2) := by
  have h1 : (dil v μ) ^ ((1 : ℝ) / 646) = (fsX v μ) ^ ((1 : ℝ) / 2) := by
    rw [bogS2_fsX_rpow, ← Real.rpow_mul hC.hD0.le]
    norm_num
  rw [bogC1_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0, h1]
  have hs := bogS2_sqrt_le hC
  have hX0 := Real.rpow_nonneg (bogS2_fsX_nonneg hC hav) ((1 : ℝ) / 2)
  nlinarith [hs, hX0]

/-- `c₁² ≤ X/3`. -/
lemma bogS2_c1_sq_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    (bogC1 v ρ μ) ^ 2 ≤ fsX v μ / 3 := by
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have h1 : (dil v μ) ^ ((1 : ℝ) / 646) = (fsX v μ) ^ ((1 : ℝ) / 2) := by
    rw [bogS2_fsX_rpow, ← Real.rpow_mul hC.hD0.le]
    norm_num
  have hsq : ((fsX v μ) ^ ((1 : ℝ) / 2)) ^ 2 = fsX v μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
  have hμρ : μ / ρ ≤ 10 / 9 := by
    rw [div_le_iff₀ hC.hρ0]; linarith [hC.hρlo]
  have hsp : (Real.sqrt (μ / ρ)) ^ 2 = μ / ρ :=
    Real.sq_sqrt (le_of_lt (div_pos hC.hμ hC.hρ0))
  rw [bogC1_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0, h1]
  nlinarith [hsq, hsp, hμρ, hX0, sq_nonneg ((fsX v μ) ^ ((1 : ℝ) / 2)),
    sq_nonneg (Real.sqrt (μ / ρ))]

/-- `c₂ ≥ X^{-11/2}/3`. -/
lemma bogS2_c2_ge {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    (fsX v μ) ^ (-(11 / 2 : ℝ)) / 3 ≤ bogC2 v ρ μ := by
  have h1 : (dil v μ) ^ (-(11 / 646 : ℝ)) = (fsX v μ) ^ (-(11 / 2 : ℝ)) := by
    rw [bogS2_fsX_rpow, ← Real.rpow_mul hC.hD0.le]
    norm_num
  rw [bogC2_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0, h1]
  have hs := bogS2_sqrt_ge hC
  have hX0 := Real.rpow_nonneg (bogS2_fsX_nonneg hC hav) (-(11 / 2 : ℝ))
  nlinarith [hs, hX0]

/-- `Δ = 2π√3·X·c₁`. -/
lemma bogS2_half_eq {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    bogHalf v ρ μ = 2 * Real.pi * Real.sqrt 3 * (fsX v μ) * bogC1 v ρ μ := by
  have hℓ : 0 < ell v μ := sb_ell_pos hav hC
  have h := sb_half_eq (v := v) (ρ := ρ) (μ := μ) hav hC.hμ hC.hρ0 hℓ
  linarith [h]

/-- `Δ ≤ 16·X^{3/2}`. -/
lemma bogS2_half_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    bogHalf v ρ μ ≤ 16 * (fsX v μ) ^ ((3 : ℝ) / 2) := by
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have heq := bogS2_half_eq hC hav
  have hc1 := bogS2_c1_le hC hav
  have hX1 : (fsX v μ) * (fsX v μ) ^ ((1 : ℝ) / 2) = (fsX v μ) ^ ((3 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by norm_num,
      Real.rpow_add (bogS2_fsX_pos hC hav), Real.rpow_one]
  have hnum : 2 * Real.pi * Real.sqrt 3 ≤ 16 := by
    have h1 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h2 : Real.pi ≤ 4 := Real.pi_le_four
    have h3 : Real.pi * Real.sqrt 3 ≤ 8 := by
      have := mul_le_mul h2 h1 (Real.sqrt_nonneg 3) (by norm_num : (0 : ℝ) ≤ 4)
      linarith [this]
    linarith [h3]
  have h2 : 2 * Real.pi * Real.sqrt 3 * bogC1 v ρ μ ≤ 16 * (fsX v μ) ^ ((1 : ℝ) / 2) :=
    calc 2 * Real.pi * Real.sqrt 3 * bogC1 v ρ μ ≤ 16 * bogC1 v ρ μ :=
          mul_le_mul_of_nonneg_right hnum (sb_c1_pos hav hC).le
      _ ≤ 16 * (fsX v μ) ^ ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hc1 (by norm_num)
  calc bogHalf v ρ μ = 2 * Real.pi * Real.sqrt 3 * bogC1 v ρ μ * (fsX v μ) := by
        rw [heq]; ring
    _ ≤ (16 * (fsX v μ) ^ ((1 : ℝ) / 2)) * (fsX v μ) :=
        mul_le_mul_of_nonneg_right h2 hX0
    _ = 16 * (fsX v μ) ^ ((3 : ℝ) / 2) := by rw [← hX1]; ring

lemma bogS2_two_half_le_c1 {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v)
    (hX : fsX v μ ≤ 1 / 10 ^ 12) : 2 * bogHalf v ρ μ ≤ bogC1 v ρ μ := by
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have hc1 : 0 < bogC1 v ρ μ := sb_c1_pos hav hC
  have heq := bogS2_half_eq hC hav
  have hnum : 4 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 1 := by
    have h1 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h2 : Real.pi ≤ 4 := Real.pi_le_four
    have h3 : Real.pi * Real.sqrt 3 ≤ 8 := by
      have := mul_le_mul h2 h1 (Real.sqrt_nonneg 3) (by norm_num : (0 : ℝ) ≤ 4)
      linarith [this]
    have h4 : 4 * Real.pi * Real.sqrt 3 ≤ 32 := by linarith
    nlinarith [h4, hX0, hX]
  rw [heq, show 2 * (2 * Real.pi * Real.sqrt 3 * (fsX v μ) * bogC1 v ρ μ)
      = (4 * Real.pi * Real.sqrt 3 * (fsX v μ)) * bogC1 v ρ μ by ring]
  exact mul_le_of_le_one_left hc1.le hnum

lemma bogS2_ell_ge {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v)
    (hX : fsX v μ ≤ (a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163)) :
    2 * Real.pi * Real.sqrt 3 ≤ ell v μ := by
  have hX0 : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hc0 : 0 < a v / (2 * Real.pi * Real.sqrt 3) := by positivity
  have h163 : (fsX v μ) ^ (163 : ℝ) ≤ a v / (2 * Real.pi * Real.sqrt 3) := by
    have h1 := Real.rpow_le_rpow hX0.le hX (by norm_num : (0 : ℝ) ≤ 163)
    rwa [← Real.rpow_mul hc0.le, show ((1 : ℝ) / 163) * 163 = 1 by norm_num,
      Real.rpow_one] at h1
  have hpos : 0 < (fsX v μ) ^ (163 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hinv : (2 * Real.pi * Real.sqrt 3) / a v ≤ ((fsX v μ) ^ (163 : ℝ))⁻¹ := by
    have h1 : (a v / (2 * Real.pi * Real.sqrt 3))⁻¹ ≤ ((fsX v μ) ^ (163 : ℝ))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hpos h163
    rwa [inv_div] at h1
  have h2 : (2 * Real.pi * Real.sqrt 3) / a v * a v ≤ ((fsX v μ) ^ (163 : ℝ))⁻¹ * a v :=
    mul_le_mul_of_nonneg_right hinv hav.le
  rw [div_mul_cancel₀ _ (ne_of_gt hav)] at h2
  rw [bogS2_ell_eq hC hav, Real.rpow_neg hX0.le]
  rw [show a v * ((fsX v μ) ^ (163 : ℝ))⁻¹ = ((fsX v μ) ^ (163 : ℝ))⁻¹ * a v by ring]
  exact h2

/-! ## 3. The cell bounds -/

/-- `|n i| ≤ mn n`. -/
lemma bogS2_abs_coord_le_mn (n : Fin 3 → ℤ) (i : Fin 3) :
    |((n i : ℤ) : ℝ)| ≤ (mn n : ℝ) := by
  have h := mn_coord_le n i
  have h2 : ((n i).natAbs : ℝ) ≤ (mn n : ℝ) := by exact_mod_cast h
  have h3 : |((n i : ℤ) : ℝ)| = ((n i).natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
  rw [h3]
  exact h2

lemma bogS2_eq_zero_of_mn_eq_zero {n : Fin 3 → ℤ} (h0 : mn n = 0) : n = 0 := by
  funext i
  have h1 : (n i).natAbs ≤ mn n := mn_coord_le n i
  rw [h0] at h1
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero h1)

/-- `‖lpt 1 n‖ ≤ √3·mn n`. -/
lemma bogS2_norm_lpt_le_mn (n : Fin 3 → ℤ) :
    ‖lpt (1 : ℝ) n‖ ≤ Real.sqrt 3 * (mn n : ℝ) := by
  have hsq : ‖lpt (1 : ℝ) n‖ ^ 2 = ∑ i : Fin 3, ((n i : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [lpt_ofLp]; norm_num
  have h3 : ∑ i : Fin 3, ((n i : ℝ)) ^ 2 ≤ ∑ _i : Fin 3, (mn n : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h4 := bogS2_abs_coord_le_mn n i
    have h5 : (0 : ℝ) ≤ (mn n : ℝ) := by positivity
    rw [sq_le_sq, abs_of_nonneg h5]
    exact h4
  have h4 : ∑ _i : Fin 3, (mn n : ℝ) ^ 2 = 3 * (mn n : ℝ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have h5 : Real.sqrt (‖lpt (1 : ℝ) n‖ ^ 2) ≤ Real.sqrt (3 * (mn n : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt (by rw [hsq, ← h4]; exact h3)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.sqrt_sq (Nat.cast_nonneg _)] at h5

lemma bogS2_inv_rlo_sq_le {v : E3 → ℝ} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hδ : 0 < bogMesh v ρ μ) :
    1 / (bogRLot v ρ μ n) ^ 2
      ≤ 256 / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2) := by
  have hδ0 : 0 ≤ bogMesh v ρ μ := hδ.le
  have hδ2 : (0 : ℝ) < bogMesh v ρ μ ^ 2 := by positivity
  rw [bogRLot_eq v ρ μ n hδ0]
  by_cases h0 : mn n = 0
  · have hn0 : n = 0 := bogS2_eq_zero_of_mn_eq_zero h0
    have h00 : mn (0 : Fin 3 → ℤ) = 0 := by rw [← hn0]; exact h0
    rw [hn0, norm_lpt_zero, h00, show (((0 : ℕ) : ℝ) + 1) = 1 by norm_num, one_pow, mul_one]
    have heq : (bogMesh v ρ μ * (0 - Real.sqrt 3 / 2)) ^ 2 = bogMesh v ρ μ ^ 2 * (3 / 4) := by
      rw [show (0 : ℝ) - Real.sqrt 3 / 2 = -(Real.sqrt 3 / 2) by ring]
      rw [show bogMesh v ρ μ * (-(Real.sqrt 3 / 2))
          = -(bogMesh v ρ μ * (Real.sqrt 3 / 2)) by ring]
      rw [neg_sq, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [heq]
    have hL : 1 / (bogMesh v ρ μ ^ 2 * (3 / 4)) = 4 / (3 * bogMesh v ρ μ ^ 2) := by
      field_simp
      try ring
    have h4 : (256 : ℝ) / (bogMesh v ρ μ ^ 2) = 768 / (3 * bogMesh v ρ μ ^ 2) := by
      field_simp
      try ring
    rw [hL, h4, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 3 * bogMesh v ρ μ ^ 2)]
    norm_num
  · have hmn1 : (1 : ℝ) ≤ (mn n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hnorm : (mn n : ℝ) ≤ ‖lpt (1 : ℝ) n‖ := mn_cast_le_norm n
    have hr : 0 < ‖lpt (1 : ℝ) n‖ := lt_of_lt_of_le (by linarith) hnorm
    have hge : bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ / 8
        ≤ bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2) := by
      have h3 : Real.sqrt 3 ≤ 7 / 4 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
      have h1 : Real.sqrt 3 / (2 * ‖lpt (1 : ℝ) n‖) ≤ 7 / 8 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [h3, hnorm]
      have h2 : (1 : ℝ) / 8 ≤ 1 - Real.sqrt 3 / (2 * ‖lpt (1 : ℝ) n‖) := by linarith
      have h4 : ‖lpt (1 : ℝ) n‖ * (1 - Real.sqrt 3 / (2 * ‖lpt (1 : ℝ) n‖))
          = ‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2 := by
        field_simp
        try ring
      calc bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ / 8
          = bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ * (1 / 8)) := by ring
        _ ≤ bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖
              * (1 - Real.sqrt 3 / (2 * ‖lpt (1 : ℝ) n‖))) := by
              refine mul_le_mul_of_nonneg_left ?_ hδ0
              exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2) := by rw [h4]
    have hpos : 0 < bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ / 8 := by positivity
    have hXn : 0 < (bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2)) ^ 2 := by
      have h6 : 0 < bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2) :=
        lt_of_lt_of_le hpos hge
      positivity
    have h4 : 1 / (bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2)) ^ 2
        ≤ 64 / (bogMesh v ρ μ ^ 2 * ‖lpt (1 : ℝ) n‖ ^ 2) := by
      rw [div_le_iff₀ hXn]
      have hy : (0 : ℝ) < bogMesh v ρ μ ^ 2 * ‖lpt (1 : ℝ) n‖ ^ 2 := by positivity
      have h5 : 64 / (bogMesh v ρ μ ^ 2 * ‖lpt (1 : ℝ) n‖ ^ 2)
            * (bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2)) ^ 2
          = 64 * (bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2)) ^ 2
            / (bogMesh v ρ μ ^ 2 * ‖lpt (1 : ℝ) n‖ ^ 2) := by
        rw [div_mul_eq_mul_div]
      rw [h5, le_div_iff₀ hy]
      nlinarith [hge, hpos, hδ.le, hr.le]
    have h6 : 64 / (bogMesh v ρ μ ^ 2 * ‖lpt (1 : ℝ) n‖ ^ 2)
        ≤ 64 / (bogMesh v ρ μ ^ 2 * (mn n : ℝ) ^ 2) := by
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      have h9 : (0 : ℝ) ≤ (mn n : ℝ) := by positivity
      have h10 : (mn n : ℝ) ^ 2 ≤ ‖lpt (1 : ℝ) n‖ ^ 2 := by
        nlinarith [hnorm, h9, norm_nonneg (lpt (1 : ℝ) n)]
      exact mul_le_mul_of_nonneg_left h10 hδ2.le
    have h7 : 64 / (bogMesh v ρ μ ^ 2 * (mn n : ℝ) ^ 2)
        ≤ 256 / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < bogMesh v ρ μ ^ 2 * (mn n : ℝ) ^ 2)]
      have h8 : 256 / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2)
            * (bogMesh v ρ μ ^ 2 * (mn n : ℝ) ^ 2)
          = 256 * (mn n : ℝ) ^ 2 / ((mn n : ℝ) + 1) ^ 2 := by
        rw [div_mul_eq_mul_div]
        field_simp
        try ring
      rw [h8, le_div_iff₀ (by positivity : (0 : ℝ) < ((mn n : ℝ) + 1) ^ 2)]
      nlinarith [hmn1, hδ2.le]
    linarith [h4, h6, h7]

lemma bogS2_inv_rlo_sq_sub_le {v : E3 → ℝ} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hδ : 0 < bogMesh v ρ μ) :
    1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2)
      ≤ 1024 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) := by
  have hδ0 : 0 ≤ bogMesh v ρ μ := hδ.le
  have hΔ : 0 < bogHalf v ρ μ := bogHalf_pos hδ
  by_cases h0 : mn n = 0
  · have hn0 : n = 0 := bogS2_eq_zero_of_mn_eq_zero h0
    have h00 : mn (0 : Fin 3 → ℤ) = 0 := by rw [← hn0]; exact h0
    rw [hn0, bogRHit, bogRLot, h00,
      show ‖tSca v ρ μ 0‖ = 0 from by
        rw [norm_tSca]
        have hz : lpt (bogMesh v ρ μ) (0 : Fin 3 → ℤ) = 0 := by
          ext i
          simp [lpt]
        rw [hz, norm_zero]]
    rw [show (0 : ℝ) + bogHalf v ρ μ = bogHalf v ρ μ by ring,
      show (0 : ℝ) - bogHalf v ρ μ = -(bogHalf v ρ μ) by ring, neg_sq]
    rw [sub_self, show (((0 : ℕ) : ℝ) + 1) = 1 by norm_num, one_pow, mul_one]
    exact div_nonneg (mul_nonneg (by norm_num) hΔ.le) (by positivity)
  · have hmn1 : (1 : ℝ) ≤ (mn n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hnorm : (mn n : ℝ) ≤ ‖lpt (1 : ℝ) n‖ := mn_cast_le_norm n
    set ρn := ‖lpt (1 : ℝ) n‖ with hρn
    have hr : 0 < ρn := lt_of_lt_of_le (by linarith) hnorm
    have hρn1 : (1 : ℝ) ≤ ρn := le_trans hmn1 hnorm
    have h3 : Real.sqrt 3 ≤ 7 / 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have hrlo : bogMesh v ρ μ * ρn / 8 ≤ bogRLot v ρ μ n := by
      rw [bogRLot_eq v ρ μ n hδ0, ← hρn]
      have h1 : Real.sqrt 3 / (2 * ρn) ≤ 7 / 8 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [h3, hρn1]
      have h2 : (1 : ℝ) / 8 ≤ 1 - Real.sqrt 3 / (2 * ρn) := by linarith
      have h4 : ρn * (1 - Real.sqrt 3 / (2 * ρn)) = ρn - Real.sqrt 3 / 2 := by
        field_simp
        try ring
      calc bogMesh v ρ μ * ρn / 8 = bogMesh v ρ μ * (ρn * (1 / 8)) := by ring
        _ ≤ bogMesh v ρ μ * (ρn * (1 - Real.sqrt 3 / (2 * ρn))) := by
            refine mul_le_mul_of_nonneg_left ?_ hδ0
            exact mul_le_mul_of_nonneg_left h2 hr.le
        _ = bogMesh v ρ μ * (ρn - Real.sqrt 3 / 2) := by rw [h4]
    have hrhi : bogMesh v ρ μ * ρn ≤ bogRHit v ρ μ n := by
      rw [bogRHit_eq v ρ μ n hδ0, ← hρn]
      have h2 : (0 : ℝ) ≤ bogMesh v ρ μ * (Real.sqrt 3 / 2) := by positivity
      nlinarith
    have hpos : 0 < bogMesh v ρ μ * ρn / 8 := by positivity
    have hrlo_pos : 0 < bogRLot v ρ μ n := lt_of_lt_of_le hpos hrlo
    have hrlo0 : bogRLot v ρ μ n ≠ 0 := ne_of_gt hrlo_pos
    have hrhi_pos : 0 < bogRHit v ρ μ n := lt_of_lt_of_le hpos (le_trans hrlo (by
      rw [bogRHit, bogRLot]; linarith))
    have hrhi0 : bogRHit v ρ μ n ≠ 0 := ne_of_gt hrhi_pos
    have hsum : bogRHit v ρ μ n + bogRLot v ρ μ n = 2 * (bogMesh v ρ μ * ρn) := by
      rw [bogRHit_eq v ρ μ n hδ0, bogRLot_eq v ρ μ n hδ0, ← hρn]; ring
    have hkey1 : 1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2)
        = ((bogRHit v ρ μ n - bogRLot v ρ μ n) * (bogRHit v ρ μ n + bogRLot v ρ μ n))
          / (2 * (bogRLot v ρ μ n) ^ 2 * (bogRHit v ρ μ n) ^ 2) := by
      field_simp
      try ring
    rw [hkey1]
    have hsub : bogRHit v ρ μ n - bogRLot v ρ μ n = 2 * bogHalf v ρ μ := by
      rw [bogRHit, bogRLot]; ring
    rw [hsub, hsum]
    have hkey2 : 2 * bogHalf v ρ μ * (2 * (bogMesh v ρ μ * ρn))
          / (2 * (bogRLot v ρ μ n) ^ 2 * (bogRHit v ρ μ n) ^ 2)
        = 2 * bogHalf v ρ μ * (bogMesh v ρ μ * ρn)
          / ((bogRLot v ρ μ n) ^ 2 * (bogRHit v ρ μ n) ^ 2) := by
      field_simp
      try ring
    rw [hkey2]
    have hden : (bogMesh v ρ μ * ρn / 8) ^ 2 * (bogMesh v ρ μ * ρn) ^ 2
        ≤ (bogRLot v ρ μ n) ^ 2 * (bogRHit v ρ μ n) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hpos.le hrlo 2)
        (pow_le_pow_left₀ (by positivity) hrhi 2) (by positivity) (by positivity)
    have hposA : 0 < (bogMesh v ρ μ * ρn / 8) ^ 2 * (bogMesh v ρ μ * ρn) ^ 2 := by
      exact mul_pos (pow_pos hpos 2) (pow_pos (by positivity) 2)
    have hposB : 0 < (bogRLot v ρ μ n) ^ 2 * (bogRHit v ρ μ n) ^ 2 := by
      exact mul_pos (pow_pos hrlo_pos 2) (pow_pos hrhi_pos 2)
    have hposC : 0 < 2 * bogHalf v ρ μ * (bogMesh v ρ μ * ρn) := by positivity
    have hstep : 2 * bogHalf v ρ μ * (bogMesh v ρ μ * ρn)
          / ((bogRLot v ρ μ n) ^ 2 * (bogRHit v ρ μ n) ^ 2)
        ≤ 2 * bogHalf v ρ μ * (bogMesh v ρ μ * ρn)
          / ((bogMesh v ρ μ * ρn / 8) ^ 2 * (bogMesh v ρ μ * ρn) ^ 2) := by
      rw [div_le_div_iff_of_pos_left hposC hposB hposA]
      exact hden
    have hA : 2 * bogHalf v ρ μ * (bogMesh v ρ μ * ρn)
          / ((bogMesh v ρ μ * ρn / 8) ^ 2 * (bogMesh v ρ μ * ρn) ^ 2)
        = 128 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ρn ^ 3) := by
      field_simp
      try ring
    rw [hA] at hstep
    have hcu : ((mn n : ℝ) + 1) ^ 3 ≤ 8 * ρn ^ 3 := by
      have h1 : (mn n : ℝ) + 1 ≤ 2 * ρn := by linarith [hmn1, hnorm]
      have h2 : (0 : ℝ) ≤ (mn n : ℝ) + 1 := by positivity
      calc ((mn n : ℝ) + 1) ^ 3 ≤ (2 * ρn) ^ 3 := pow_le_pow_left₀ h2 h1 3
        _ = 8 * ρn ^ 3 := by ring
    have hfin : 128 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ρn ^ 3)
        ≤ 1024 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < bogMesh v ρ μ ^ 3 * ρn ^ 3)]
      have h9 : 1024 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3)
            * (bogMesh v ρ μ ^ 3 * ρn ^ 3)
          = 1024 * bogHalf v ρ μ * ρn ^ 3 / ((mn n : ℝ) + 1) ^ 3 := by
        rw [div_mul_eq_mul_div]
        field_simp
        try ring
      rw [h9, le_div_iff₀ (by positivity : (0 : ℝ) < ((mn n : ℝ) + 1) ^ 3)]
      have h10 : 128 * bogHalf v ρ μ * ((mn n : ℝ) + 1) ^ 3
          ≤ 128 * bogHalf v ρ μ * (8 * ρn ^ 3) :=
        mul_le_mul_of_nonneg_left hcu (by positivity)
      have h11 : 128 * bogHalf v ρ μ * (8 * ρn ^ 3) = 1024 * bogHalf v ρ μ * ρn ^ 3 := by
        ring
      linarith [h10, h11.le, h11.ge]
    linarith [hstep, hfin]

/-! ## 4. The `β`/`V` and `τ` rows -/

/-- `√(ρa)·Δ = π√3/ℓ`. -/
lemma bogS2_sqrt_mul_half {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (hℓ : 0 < ell v μ) :
    Real.sqrt (ρ * a v) * bogHalf v ρ μ = Real.pi * Real.sqrt 3 / ell v μ := by
  have hs : Real.sqrt (ρ * a v) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  rw [bogHalf, bogMesh]
  field_simp
  try ring

/-- `bogOm n ≤ 2·bogOscM` for **every** cell (on `ℓ ≥ 2π√3`). -/
lemma bogS2_om_le_two_oscM {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hP : 0 < ρ * a v) (hδ : 0 < bogMesh v ρ μ) (hℓ : 0 < ell v μ) (hR : 0 ≤ R)
    (hell : 2 * Real.pi * Real.sqrt 3 ≤ ell v μ) :
    bogOm v h R ρ μ n ≤ 2 * bogOscM v R ρ μ := by
  have hX0 : 0 ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ :=
    mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3))
      (Real.sqrt_nonneg _)) (bogHalf_pos hδ).le
  have hom : bogOm v h R ρ μ n
      = (bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ)
        / (1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n) := by
    simp only [bogOm, bogOscK]
  have hosc : bogOscM v R ρ μ
      = bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ := by
    simp only [bogOscM]
  rw [hom, hosc]
  have hrlo : -(bogHalf v ρ μ) ≤ bogRLot v ρ μ n := by
    rw [bogRLot_eq v ρ μ n hδ.le]
    have h4 : bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2)
        = bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ - bogHalf v ρ μ := by
      rw [bogHalf]; ring
    rw [h4]
    have h2 : (0 : ℝ) ≤ bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ :=
      mul_nonneg hδ.le (norm_nonneg _)
    linarith
  have hden : (1 : ℝ) / 2 ≤ 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n := by
    have h1 : Real.sqrt (ρ * a v) * (-(bogHalf v ρ μ))
        ≤ Real.sqrt (ρ * a v) * bogRLot v ρ μ n :=
      mul_le_mul_of_nonneg_left hrlo (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (ρ * a v) * bogHalf v ρ μ = Real.pi * Real.sqrt 3 / ell v μ :=
      bogS2_sqrt_mul_half hP hℓ
    have h3 : Real.pi * Real.sqrt 3 / ell v μ ≤ 1 / 2 := by
      rw [div_le_iff₀ hℓ]; nlinarith [hell]
    nlinarith [h1, h2, h3]
  rcases le_or_gt 0 (1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n) with hd | hd
  · calc (bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ)
          / (1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n)
        ≤ (bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ) / (1 / 2) :=
          div_le_div_of_nonneg_left hX0 (by norm_num) hden
      _ = 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ) := by ring
  · have h5 : (bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ)
        / (1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hX0 hd.le
    linarith [h5, hX0]

lemma bogS2_oscM_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v)
    (hR : 0 < R) (hX : fsX v μ ≤ 1 / 50) :
    bogOscM v R ρ μ
      ≤ 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3 / (a v) ^ 2)
        * (fsX v μ) ^ (3 : ℝ) := by
  have hρ : 0 < ρ := hC.hρ0
  have hKOs0 : (0 : ℝ) ≤ bogKOs := bogKOs_nonneg
  have hX0 : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hsq := hC.hsqρa
  rw [← Real.sqrt_eq_rpow] at hsq
  rw [bogS2_sqrt_dil hC hav] at hsq
  have h1 : Real.sqrt (ρ / a v) ≤ Real.sqrt (11 / 10) * (fsX v μ) ^ ((323 : ℝ) / 2)
      / (a v) ^ 2 := by
    have heq : ρ / a v = ρ * a v / (a v) ^ 2 := by field_simp
    rw [heq]
    have h2 : Real.sqrt (ρ * a v / (a v) ^ 2) = Real.sqrt (ρ * a v) / a v := by
      rw [Real.sqrt_div (le_of_lt (mul_pos hρ hav)) ((a v) ^ 2),
        show Real.sqrt ((a v) ^ 2) = a v from Real.sqrt_sq hav.le]
    rw [h2]
    calc Real.sqrt (ρ * a v) / a v
        ≤ (Real.sqrt (11 / 10) * (fsX v μ) ^ ((323 : ℝ) / 2) / a v) / a v :=
          div_le_div_of_nonneg_right hsq hav.le
      _ = Real.sqrt (11 / 10) * (fsX v μ) ^ ((323 : ℝ) / 2) / (a v) ^ 2 := by ring
  have h2 : bogHalf v ρ μ ≤ 16 * (fsX v μ) ^ ((3 : ℝ) / 2) := bogS2_half_le hC hav
  have hX1 : (fsX v μ) ^ ((323 : ℝ) / 2) * (fsX v μ) ^ ((3 : ℝ) / 2)
      = (fsX v μ) ^ (163 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  rw [bogOscM]
  have hK : 0 ≤ bogKOs * (1 + R) ^ 3 :=
    mul_nonneg hKOs0 (pow_nonneg (by linarith) 3)
  have hstep : bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ
      ≤ bogKOs * (1 + R) ^ 3
        * (Real.sqrt (11 / 10) * (fsX v μ) ^ ((323 : ℝ) / 2) / (a v) ^ 2)
        * (16 * (fsX v μ) ^ ((3 : ℝ) / 2)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) h2 (bogHalf_pos (bogMesh_pos_of hρ hav
      (sb_ell_pos hav hC))).le ?_
    positivity
  have h160 : 16 * (fsX v μ) ^ (160 : ℝ) ≤ 2 * Real.pi * Real.sqrt 3 := by
    have h1 : (fsX v μ) ^ (160 : ℝ) ≤ 1 / 50 := by
      have h2 : (fsX v μ) ^ (160 : ℝ) ≤ (fsX v μ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hX0 (bogS2_fsX_le_one hC) (by norm_num)
      rw [Real.rpow_one] at h2
      linarith [h2, hX]
    have h3 : (6 : ℝ) ≤ 2 * Real.pi * Real.sqrt 3 := by
      have h4 : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [Real.pi_gt_three, h4]
    linarith
  have h163 : (fsX v μ) ^ (163 : ℝ) ≤ (2 * Real.pi * Real.sqrt 3 / 16) * (fsX v μ) ^ (3 : ℝ) := by
    have h5 : (fsX v μ) ^ (163 : ℝ) = (fsX v μ) ^ (3 : ℝ) * (fsX v μ) ^ (160 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    rw [h5]
    have h6 : 0 ≤ (fsX v μ) ^ (3 : ℝ) := Real.rpow_nonneg hX0.le _
    calc (fsX v μ) ^ (3 : ℝ) * (fsX v μ) ^ (160 : ℝ)
        ≤ (fsX v μ) ^ (3 : ℝ) * (2 * Real.pi * Real.sqrt 3 / 16) :=
          mul_le_mul_of_nonneg_left (by linarith [h160]) h6
      _ = (2 * Real.pi * Real.sqrt 3 / 16) * (fsX v μ) ^ (3 : ℝ) := by ring
  have h7 : (2 * Real.pi * Real.sqrt 3 / 16) ≤ 2 * Real.pi * Real.sqrt 3 := by
    have h8 : (1 : ℝ) ≤ 2 * Real.pi * Real.sqrt 3 := by
      have h4 : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [Real.pi_gt_three, h4]
    nlinarith [h8]
  have hfac : 0 ≤ (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) / (a v) ^ 2) := by positivity
  calc bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ
      ≤ bogKOs * (1 + R) ^ 3
        * (Real.sqrt (11 / 10) * (fsX v μ) ^ ((323 : ℝ) / 2) / (a v) ^ 2)
        * (16 * (fsX v μ) ^ ((3 : ℝ) / 2)) := hstep
    _ = 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) / (a v) ^ 2)
        * ((fsX v μ) ^ ((323 : ℝ) / 2) * (fsX v μ) ^ ((3 : ℝ) / 2)) := by ring
    _ = 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) / (a v) ^ 2)
        * (fsX v μ) ^ (163 : ℝ) := by rw [hX1]
    _ ≤ 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) / (a v) ^ 2)
        * ((2 * Real.pi * Real.sqrt 3 / 16) * (fsX v μ) ^ (3 : ℝ)) :=
        mul_le_mul_of_nonneg_left h163 (by positivity)
    _ = 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3 / (a v) ^ 2)
        * (fsX v μ) ^ (3 : ℝ) := by ring

/-- The state-independent constant bound on the crude oscillation majorant
(`bogOscM = bogKOs(1+R)³√3π/(ℓ·a v)` and `a v ≤ ℓ v μ`). -/
lemma bogS2_oscM_le_eleven {v : E3 → ℝ} {R μ ρ : ℝ} (hav : 0 < a v) (hR : 0 ≤ R)
    (hC : Core v R μ ρ) :
    bogOscM v R ρ μ
      ≤ 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
          / (a v) ^ 2) := by
  have hρ : 0 < ρ := hC.hρ0
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have hXp : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hX1 : fsX v μ ≤ 1 := bogS2_fsX_le_one hC
  have hℓ : 0 < ell v μ := sb_ell_pos hav hC
  have hAle : a v ≤ ell v μ := by
    rw [bogS2_ell_eq hC hav]
    have hinv : (1 : ℝ) ≤ (fsX v μ) ^ (-(163 : ℝ)) := by
      rw [Real.rpow_neg hX0, one_le_inv₀ (Real.rpow_pos_of_pos hXp _)]
      exact Real.rpow_le_one hX0 hX1 (by norm_num)
    nlinarith [hinv, hav.le]
  have hkey : bogOscM v R ρ μ
      = bogKOs * (1 + R) ^ 3 * (Real.sqrt 3 * Real.pi / (ell v μ * a v)) := by
    rw [bogOscM, bogHalf, bogMesh]
    have hsq : Real.sqrt (ρ / a v) * Real.sqrt (ρ * a v) = ρ := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ρ / a v)]
      rw [show ρ / a v * (ρ * a v) = ρ ^ 2 by field_simp]
      exact Real.sqrt_sq hρ.le
    have hdiv : Real.sqrt (ρ / a v) = ρ / Real.sqrt (ρ * a v) := by
      rw [eq_div_iff (ne_of_gt (Real.sqrt_pos_of_pos (mul_pos hρ hav)))]
      exact hsq
    rw [hdiv]
    field_simp
    rw [Real.sq_sqrt (mul_pos hρ hav).le]
    ring
  rw [hkey]
  have hb : (1 : ℝ) / (ell v μ * a v) ≤ 2 * Real.sqrt (11 / 10) / (a v) ^ 2 := by
    have h2 : (a v) ^ 2 ≤ ell v μ * a v := by
      have h := mul_le_mul_of_nonneg_right hAle hav.le
      simpa [pow_two] using h
    have h3 : (1 : ℝ) / (ell v μ * a v) ≤ 1 / (a v) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hav 2) h2
    have h4 : (1 : ℝ) / (a v) ^ 2 ≤ 2 * Real.sqrt (11 / 10) / (a v) ^ 2 := by
      have hs : (1 : ℝ) ≤ 2 * Real.sqrt (11 / 10) := by
        have h : (1 : ℝ) ≤ Real.sqrt (11 / 10) := Real.one_le_sqrt.mpr (by norm_num)
        linarith
      exact div_le_div_of_nonneg_right hs (by positivity)
    linarith [h3, h4]
  have hcoef : (0 : ℝ) ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt 3 * Real.pi :=
    mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3))
      (Real.sqrt_nonneg 3)) Real.pi_nonneg
  have hstep : bogKOs * (1 + R) ^ 3 * (Real.sqrt 3 * Real.pi / (ell v μ * a v))
      = (bogKOs * (1 + R) ^ 3 * Real.sqrt 3 * Real.pi) * (1 / (ell v μ * a v)) := by
    ring
  have hstep2 : 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
        / (a v) ^ 2)
      = (bogKOs * (1 + R) ^ 3 * Real.sqrt 3 * Real.pi)
        * (2 * Real.sqrt (11 / 10) / (a v) ^ 2) := by
    ring
  rw [hstep, hstep2]
  exact mul_le_mul_of_nonneg_left hb hcoef

/-! ## 5. The pointwise majorant -/

/-- `R_B = 16√C`: the bound on the gate radius `bogBigThr` (via `Vs ≤ C`). -/
def bogS2RB (v : E3 → ℝ) (R : ℝ) : ℝ := 16 * Real.sqrt (bogS2Cst v R)

/-- The constant part of the majorant. -/
def bogS2A1 (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  4 * bogHalf v ρ μ * bogS2RB v R + 9 * (bogC1 v ρ μ) ^ 2

def bogS2A2 (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
    + 2 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * Real.sqrt 3
      * bogMesh v ρ μ

def bogS2A3 (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  Real.sqrt (2 * bogS2A1 v R ρ μ) * bogS2Cst v R
    + 2 * bogS2Cst v R * (fsX v μ) ^ (3 : ℝ)

def bogS2A4 (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  512 * (bogS2Cst v R) ^ 2 * (fsX v μ) ^ (3 : ℝ) / (bogMesh v ρ μ) ^ 2

def bogS2A5 (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  1024 * bogHalf v ρ μ * (bogS2Cst v R) ^ 2 / (bogMesh v ρ μ) ^ 3

/-- The gate-free part of the majorant. -/
def bogS2MajE (v : E3 → ℝ) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  bogS2A1 v R ρ μ
    + bogS2A2 v R ρ μ * ((mn n : ℝ) + 1)
    + bogS2A3 v R ρ μ
    + bogS2A4 v R ρ μ * (1 / (((mn n : ℝ) + 1) ^ 2))
    + bogS2A5 v R ρ μ * (1 / (((mn n : ℝ) + 1) ^ 3))

/-- The pointwise majorant of `bogS2` (gated by the region-B condition). -/
def bogS2Maj (v : E3 → ℝ) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogRHit v ρ μ n ≤ bogBigThr v R ρ μ then bogS2MajE v R ρ μ n else 0

lemma bogS2_eT_nonneg {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    0 ≤ (paramsAt μ (a v)).eT := by
  rw [paramsAt_eT]; exact Real.rpow_nonneg hC.hD0.le _

lemma bogS2_eT_le_one {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    (paramsAt μ (a v)).eT ≤ 1 := by
  rw [paramsAt_eT]
  exact Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num)

lemma bogS2RB_nonneg {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < a v) :
    0 ≤ bogS2RB v R := by
  rw [bogS2RB]; positivity

lemma bogS2A1_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2A1 v R ρ μ := by
  rw [bogS2A1]
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hρ hav hℓ
  have h1 : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
  have h2 := bogS2RB_nonneg (v := v) hR hav
  have h3 : 0 ≤ (bogC1 v ρ μ) ^ 2 := sq_nonneg _
  nlinarith

lemma bogS2A2_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2A2 v R ρ μ := by
  rw [bogS2A2]
  have h1 := bogS2A1_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have h2 : 0 ≤ bogMesh v ρ μ := (bogMesh_pos_of hρ hav hℓ).le
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hX : 0 ≤ fsX v μ := fsX_pos hμ hav |>.le
  have h3 : 0 ≤ Real.sqrt (2 * bogS2A1 v R ρ μ) := Real.sqrt_nonneg _
  have h4 : 0 ≤ Real.sqrt (bogS2Cst v R) := Real.sqrt_nonneg _
  have h5 : 0 ≤ (fsX v μ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hX _
  exact add_nonneg (mul_nonneg (mul_nonneg h3 (Real.sqrt_nonneg 3)) h2)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4) h5)
      (Real.sqrt_nonneg 3)) h2)

lemma bogS2A3_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2A3 v R ρ μ := by
  rw [bogS2A3]
  have h1 := bogS2A1_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hX : 0 ≤ fsX v μ := (fsX_pos hμ hav).le
  have h3 : 0 ≤ Real.sqrt (2 * bogS2A1 v R ρ μ) := Real.sqrt_nonneg _
  have h4 : 0 ≤ (fsX v μ) ^ (3 : ℝ) := Real.rpow_nonneg hX _
  nlinarith

lemma bogS2A4_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2A4 v R ρ μ := by
  rw [bogS2A4]
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hX : 0 ≤ fsX v μ := (fsX_pos hμ hav).le
  have h2 : 0 < bogMesh v ρ μ := bogMesh_pos_of hρ hav hℓ
  have h3 : 0 ≤ (fsX v μ) ^ (3 : ℝ) := Real.rpow_nonneg hX _
  positivity

lemma bogS2A5_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2A5 v R ρ μ := by
  rw [bogS2A5]
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have h2 : 0 < bogMesh v ρ μ := bogMesh_pos_of hρ hav hℓ
  have h4 : 0 ≤ bogHalf v ρ μ := (bogHalf_pos h2).le
  have h5 : 0 ≤ (bogS2Cst v R) ^ 2 := sq_nonneg _
  exact div_nonneg (by nlinarith) (by positivity)

lemma bogS2MajE_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} {n : Fin 3 → ℤ} (hR : 0 < R)
    (hav : 0 < a v) (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2MajE v R ρ μ n := by
  rw [bogS2MajE]
  have h1 := bogS2A1_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have h2 := bogS2A2_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have h3 := bogS2A3_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have h4 := bogS2A4_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have h5 := bogS2A5_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hρ hμ hℓ
  have h6 : 0 ≤ ((mn n : ℝ) + 1) := by positivity
  have h7 : 0 ≤ 1 / (((mn n : ℝ) + 1) ^ 2) := by positivity
  have h8 : 0 ≤ 1 / (((mn n : ℝ) + 1) ^ 3) := by positivity
  nlinarith

lemma bogS2Maj_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} {n : Fin 3 → ℤ} (hR : 0 < R)
    (hav : 0 < a v) (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    0 ≤ bogS2Maj v R ρ μ n := by
  rw [bogS2Maj]
  split
  · exact bogS2MajE_nonneg hR hav hρ hμ hℓ
  · exact le_rfl

/-- `bogS2Maj n ≤ bogS2MajE n`. -/
lemma bogS2Maj_le_majE {v : E3 → ℝ} {R ρ μ : ℝ} {n : Fin 3 → ℤ} (hR : 0 < R)
    (hav : 0 < a v) (hρ : 0 < ρ) (hμ : 0 < μ) (hℓ : 0 < ell v μ) :
    bogS2Maj v R ρ μ n ≤ bogS2MajE v R ρ μ n := by
  rw [bogS2Maj]
  split
  · exact le_rfl
  · exact bogS2MajE_nonneg hR hav hρ hμ hℓ

/-- **The `τ` row of the cell**: `u_hi − u_lo ≤ 4Δr_hi + 9c₁²`. -/
lemma bogS2_hit_sub_lot_le {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hav : 0 < a v) (hC : Core v R μ ρ) (hX : fsX v μ ≤ 1 / 10 ^ 12)
    (hVs : bogVs v R ρ μ ≤ bogS2Cst v R) (hc2big : bogS2RB v R ≤ bogC2 v ρ μ)
    (hgate : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ) :
    bogUHit v ρ μ n - bogULot v ρ μ n
      ≤ 4 * bogHalf v ρ μ * bogRHit v ρ μ n + 9 * (bogC1 v ρ μ) ^ 2 := by
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  by_cases hn : n = 0
  · subst hn
    have h0 : bogRHit v ρ μ 0 = bogHalf v ρ μ := by
      rw [bogRHit]
      have hz : ‖tSca v ρ μ 0‖ = 0 := by
        rw [norm_tSca]
        have hzz : lpt (bogMesh v ρ μ) (0 : Fin 3 → ℤ) = 0 := by
          ext i
          simp [lpt]
        rw [hzz, norm_zero]
      rw [hz]; ring
    have h1 : 0 ≤ bogULot v ρ μ 0 :=
      tauScRad_nonneg v (mul_pos hC.hρ0 hav) (bogS2_eT_nonneg hC) (bogS2_eT_le_one hC)
        (bogRLot v ρ μ 0)
    have h2 : bogUHit v ρ μ 0 ≤ (bogRHit v ρ μ 0) ^ 2 :=
      tauScRad_le_sq v (mul_pos hC.hρ0 hav) (sb_c1_pos hav hC) (sb_c2_pos hav hC)
        (bogS2_eT_nonneg hC) (bogS2_eT_le_one hC) (by rw [h0]; exact (bogHalf_pos hδ).le)
    have h3 := bogHalf_pos hδ
    rw [h0] at h2 ⊢
    have h4 : bogUHit v ρ μ 0 - bogULot v ρ μ 0
        ≤ 4 * bogHalf v ρ μ * bogHalf v ρ μ + 9 * (bogC1 v ρ μ) ^ 2 := by
      have h5 : bogUHit v ρ μ 0 ≤ (bogHalf v ρ μ) ^ 2 := h2
      have h6 : 0 ≤ (bogHalf v ρ μ) ^ 2 := sq_nonneg _
      have h7 : 0 ≤ (bogC1 v ρ μ) ^ 2 := sq_nonneg _
      nlinarith [h1, h5, h6, h7, h3]
    exact h4
  · have hrlo : 0 ≤ bogRLot v ρ μ n := (bogRLo_pos hδ hn).le
    have hrr : bogRLot v ρ μ n ≤ bogRHit v ρ μ n := by
      rw [bogRHit, bogRLot]
      have := bogHalf_pos hδ
      linarith
    have hRB : bogRHit v ρ μ n ≤ bogS2RB v R := by
      have hVs0 : 0 ≤ bogVs v R ρ μ := le_of_lt (bogVs_pos v R ρ μ)
      have h1 : Real.sqrt (bogVs v R ρ μ) ≤ Real.sqrt (bogS2Cst v R) := Real.sqrt_le_sqrt hVs
      simp only [bogS2RB, bogBigThr] at hgate ⊢
      exact le_trans hgate (mul_le_mul_of_nonneg_left h1 (by norm_num))
    have hrc : bogRHit v ρ μ n ≤ bogC2 v ρ μ := le_trans hRB hc2big
    have hsm : bogRHit v ρ μ n - bogRLot v ρ μ n ≤ bogC1 v ρ μ := by
      rw [bogRHit, bogRLot]
      have := bogS2_two_half_le_c1 hC hav hX
      linarith
    have hsub := tauScRad_sub_le (ρ := ρ) (μ := μ) (mul_pos hC.hρ0 hav)
      (sb_c1_pos hav hC) (sb_c2_pos hav hC) (bogS2_eT_nonneg hC) (bogS2_eT_le_one hC)
      hrlo hrr hrc hsm
    rw [bogUHit, bogULot]
    have h3 : bogRHit v ρ μ n - bogRLot v ρ μ n = 2 * bogHalf v ρ μ := by
      rw [bogRHit, bogRLot]; ring
    have h4 : (bogRHit v ρ μ n - bogRLot v ρ μ n) * (bogRHit v ρ μ n + bogRLot v ρ μ n)
        ≤ 4 * bogHalf v ρ μ * bogRHit v ρ μ n := by
      rw [h3]; nlinarith [(bogHalf_pos hδ).le, hrr]
    linarith [hsub, h4]

/-! ## 6. The sum bound -/

/-- `X^{-p} ≤ X^{-4}` for `p ≤ 4` on `0 < X ≤ 1`. -/
lemma bogS2_rpow_neg_le_four {X p : ℝ} (h0 : 0 < X) (h1 : X ≤ 1) (hp : p ≤ 4) :
    X ^ (-p) ≤ X ^ (-(4 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)

/-- `X^p ≤ 1` for `0 ≤ X ≤ 1`, `0 ≤ p`. -/
lemma bogS2_rpow_le_one' {X p : ℝ} (h0 : 0 ≤ X) (h1 : X ≤ 1) (hp : 0 ≤ p) :
    X ^ p ≤ 1 := Real.rpow_le_one h0 h1 hp

/-- `X^a·X^b = X^{a+b}`. -/
lemma bogS2_rpow_mul_eq {X a b : ℝ} (h0 : 0 < X) : X ^ a * X ^ b = X ^ (a + b) :=
  (Real.rpow_add h0 a b).symm

/-- `X^p·X^{-q} ≤ X^{-4}` when `q ≤ p + 4` and `0 < X ≤ 1`. -/
lemma bogS2_rpow_mul_le {X p q : ℝ} (h0 : 0 < X) (h1 : X ≤ 1) (h : q ≤ p + 4) :
    X ^ p * X ^ (-q) ≤ X ^ (-(4 : ℝ)) := by
  rw [← Real.rpow_add h0]
  exact Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)

/-- `X·X^{-q} ≤ X^{-4}` when `q ≤ 5` and `0 < X ≤ 1`. -/
lemma bogS2_rpow_one_mul_le {X q : ℝ} (h0 : 0 < X) (h1 : X ≤ 1) (h : q ≤ 5) :
    X * X ^ (-q) ≤ X ^ (-(4 : ℝ)) := by
  have h2 := bogS2_rpow_mul_le (X := X) (p := 1) (q := q) h0 h1 (by linarith)
  rwa [Real.rpow_one] at h2

/-- `(X^a)^n = X^{a·n}`. -/
lemma bogS2_rpow_pow {X : ℝ} (h0 : 0 ≤ X) (a : ℝ) (n : ℕ) :
    (X ^ a) ^ n = X ^ (a * n) := by
  rw [← Real.rpow_natCast (X ^ a) n, ← Real.rpow_mul h0]

/-- `δ^{-1} ≤ X^{-3/2}`. -/
lemma bogS2_mesh_inv_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    1 / bogMesh v ρ μ ≤ (fsX v μ) ^ (-(3 / 2 : ℝ)) := by
  have hX0 : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  have h1 : 5 * (fsX v μ) ^ ((3 : ℝ) / 2) ≤ bogMesh v ρ μ := bogS2_mesh_ge hC hav
  have h2 : (fsX v μ) ^ (-(3 / 2 : ℝ)) = ((fsX v μ) ^ ((3 : ℝ) / 2))⁻¹ :=
    Real.rpow_neg hX0.le _
  rw [h2, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  linarith [h1]

/-- `δ^{-3} ≤ X^{-9/2}`. -/
lemma bogS2_mesh_inv_cube_le {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) (hav : 0 < a v) :
    1 / (bogMesh v ρ μ) ^ 3 ≤ (fsX v μ) ^ (-(9 / 2 : ℝ)) := by
  have hX0 : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hX0 : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  have h1 : 5 * (fsX v μ) ^ ((3 : ℝ) / 2) ≤ bogMesh v ρ μ := bogS2_mesh_ge hC hav
  have h2 : (fsX v μ) ^ (-(9 / 2 : ℝ)) = ((fsX v μ) ^ ((9 : ℝ) / 2))⁻¹ :=
    Real.rpow_neg hX0.le _
  have h3 : (5 * (fsX v μ) ^ ((3 : ℝ) / 2)) ^ 3 ≤ (bogMesh v ρ μ) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le _)) h1 3
  have h4 : (5 * (fsX v μ) ^ ((3 : ℝ) / 2)) ^ 3 = 125 * (fsX v μ) ^ ((9 : ℝ) / 2) := by
    have h5 : ((fsX v μ) ^ ((3 : ℝ) / 2)) ^ (3 : ℕ)
        = 1 * (fsX v μ) ^ ((9 : ℝ) / 2) := by
      rw [show ((fsX v μ) ^ ((3 : ℝ) / 2)) ^ (3 : ℕ)
          = ((fsX v μ) ^ ((3 : ℝ) / 2)) ^ (3 : ℝ) from (Real.rpow_natCast _ 3).symm]
      rw [← Real.rpow_mul hX0.le]
      norm_num
    rw [mul_pow, h5]
    ring
  rw [h2, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  rw [h4] at h3
  have h5 : (0 : ℝ) ≤ (fsX v μ) ^ ((9 : ℝ) / 2) := Real.rpow_nonneg hX0.le _
  linarith [h3, h5]

/-- `A1 ≤ 1027·√C·X`. -/
lemma bogS2A1_le {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hC : Core v R μ ρ) (hX : fsX v μ ≤ 1 / 50) :
    bogS2A1 v R ρ μ ≤ 1027 * Real.sqrt (bogS2Cst v R) * fsX v μ := by
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have hXp : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  have h1 : bogHalf v ρ μ ≤ 16 * (fsX v μ) ^ ((3 : ℝ) / 2) := bogS2_half_le hC hav
  have h2 : (fsX v μ) ^ ((3 : ℝ) / 2) ≤ fsX v μ := by
    rw [show ((3 : ℝ) / 2) = 1 + (1 : ℝ) / 2 by norm_num,
      Real.rpow_add hXp, Real.rpow_one]
    have h5 : (fsX v μ) ^ ((1 : ℝ) / 2) ≤ 1 :=
      bogS2_rpow_le_one' hX0 (le_trans hX (by norm_num)) (by norm_num)
    nlinarith [hX0, h5]
  have h3 : (bogC1 v ρ μ) ^ 2 ≤ fsX v μ / 3 := bogS2_c1_sq_le hC hav
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have h4 : 1 ≤ Real.sqrt (bogS2Cst v R) := Real.one_le_sqrt.mpr hC1
  have h5 : 0 ≤ Real.sqrt (bogS2Cst v R) := Real.sqrt_nonneg _
  have h6 : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
  rw [bogS2A1, bogS2RB]
  nlinarith [h1, h2, h3, h4, h5, h6, hX0, sq_nonneg (bogC1 v ρ μ)]

/-- `√(2A1) ≤ 46·C^{1/4}·X^{1/2}`. -/
lemma bogS2_sqrt2A1_le {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hC : Core v R μ ρ) (hX : fsX v μ ≤ 1 / 50) :
    Real.sqrt (2 * bogS2A1 v R ρ μ)
      ≤ 46 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2) := by
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have hXp : 0 < fsX v μ := bogS2_fsX_pos hC hav
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hCpos : 0 < bogS2Cst v R := lt_of_lt_of_le one_pos hC1
  have h1 := bogS2A1_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC hX
  have h2 : 0 ≤ bogS2A1 v R ρ μ :=
    bogS2A1_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC.hρ0 hC.hμ
      (sb_ell_pos hav hC)
  have h5 : 2 * bogS2A1 v R ρ μ ≤ 2 * (1027 * Real.sqrt (bogS2Cst v R) * fsX v μ) := by
    linarith
  have h6 : 2 * (1027 * Real.sqrt (bogS2Cst v R) * fsX v μ)
      ≤ 46 ^ 2 * (bogS2Cst v R) ^ ((1 : ℝ) / 2) * fsX v μ := by
    have h7 : (2 : ℝ) * 1027 ≤ 46 ^ 2 := by norm_num
    have h8 : 0 ≤ Real.sqrt (bogS2Cst v R) := Real.sqrt_nonneg _
    have h9 : 0 ≤ fsX v μ := hX0
    have h10 : (bogS2Cst v R) ^ ((1 : ℝ) / 2) = Real.sqrt (bogS2Cst v R) :=
      (Real.sqrt_eq_rpow _).symm
    rw [h10]
    have h11 : 2 * (1027 * Real.sqrt (bogS2Cst v R) * fsX v μ)
        ≤ 46 ^ 2 * Real.sqrt (bogS2Cst v R) * fsX v μ := by
      have h12 : 2 * (1027 * Real.sqrt (bogS2Cst v R) * fsX v μ)
          = 2 * 1027 * (Real.sqrt (bogS2Cst v R) * fsX v μ) := by ring
      rw [h12]
      have h13 : 46 ^ 2 * (Real.sqrt (bogS2Cst v R) * fsX v μ)
          = 46 ^ 2 * Real.sqrt (bogS2Cst v R) * fsX v μ := by ring
      rw [← h13]
      exact mul_le_mul_of_nonneg_right h7 (by positivity)
    exact h11
  have h11 : Real.sqrt (2 * bogS2A1 v R ρ μ)
      ≤ Real.sqrt (46 ^ 2 * (bogS2Cst v R) ^ ((1 : ℝ) / 2) * fsX v μ) :=
    Real.sqrt_le_sqrt (by linarith)
  have h12 : Real.sqrt (46 ^ 2 * (bogS2Cst v R) ^ ((1 : ℝ) / 2) * fsX v μ)
      = 46 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2) := by
    rw [show (46 : ℝ) ^ 2 * (bogS2Cst v R) ^ ((1 : ℝ) / 2) * fsX v μ
        = 46 ^ 2 * ((bogS2Cst v R) ^ ((1 : ℝ) / 2) * fsX v μ) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (Real.rpow_nonneg hCpos.le _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hCpos.le]
    rw [show ((1 : ℝ) / 2) * (1 / 2) = (1 : ℝ) / 4 by norm_num]
    ring
  linarith [h11, h12.le, h12.ge]

/-- `A2 ≤ 80·C^{1/4}X^{1/2}δ + 4√C X^{3/2}δ`. -/
lemma bogS2A2_le {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hC : Core v R μ ρ) (hX : fsX v μ ≤ 1 / 50) :
    bogS2A2 v R ρ μ ≤ 92 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2)
        * bogMesh v ρ μ
      + 4 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * bogMesh v ρ μ := by
  have h1 := bogS2_sqrt2A1_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC hX
  have hδ : 0 ≤ bogMesh v ρ μ := (bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)).le
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have h2 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have h3 : 0 ≤ Real.sqrt (bogS2Cst v R) := Real.sqrt_nonneg _
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hCpos : 0 < bogS2Cst v R := lt_of_lt_of_le one_pos hC1
  have h4 : 0 ≤ (bogS2Cst v R) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hCpos.le _
  rw [bogS2A2]
  have e1 : Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
      ≤ 92 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2)
        * bogMesh v ρ μ := by
    have h5 : Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3
        ≤ 92 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2) := by
      have h7 : Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3
          ≤ (46 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2)) * 2 :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg 3) (by positivity)
      have h8 : (46 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2)) * 2
          = 92 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2) := by ring
      linarith [h7, h8.le, h8.ge]
    calc Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
        ≤ (92 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2))
          * bogMesh v ρ μ := mul_le_mul_of_nonneg_right h5 hδ
      _ = 92 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2)
          * bogMesh v ρ μ := by ring
  have e2 : 2 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * Real.sqrt 3
        * bogMesh v ρ μ
      ≤ 4 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * bogMesh v ρ μ := by
    have h6 : 2 * Real.sqrt 3 ≤ 4 := by linarith [h2]
    have h7 : 0 ≤ Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * bogMesh v ρ μ :=
      mul_nonneg (mul_nonneg h3 (Real.rpow_nonneg hX0 _)) hδ
    calc 2 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * Real.sqrt 3
          * bogMesh v ρ μ
        = (2 * Real.sqrt 3)
          * (Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * bogMesh v ρ μ) := by ring
      _ ≤ 4 * (Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * bogMesh v ρ μ) :=
          mul_le_mul_of_nonneg_right h6 h7
      _ = 4 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * bogMesh v ρ μ := by ring
  linarith [e1, e2]

/-- `A3 ≤ 46·C^{5/4}X^{1/2} + 2CX³`. -/
lemma bogS2A3_le {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hC : Core v R μ ρ) (hX : fsX v μ ≤ 1 / 50) :
    bogS2A3 v R ρ μ ≤ 46 * (bogS2Cst v R) ^ ((5 : ℝ) / 4) * (fsX v μ) ^ ((1 : ℝ) / 2)
      + 2 * bogS2Cst v R * (fsX v μ) ^ (3 : ℝ) := by
  have h1 := bogS2_sqrt2A1_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC hX
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hCpos : 0 < bogS2Cst v R := lt_of_lt_of_le one_pos hC1
  have hX0 : 0 ≤ fsX v μ := bogS2_fsX_nonneg hC hav
  have h2 : (bogS2Cst v R) ^ ((1 : ℝ) / 4) * bogS2Cst v R
      = (bogS2Cst v R) ^ ((5 : ℝ) / 4) := by
    rw [show (bogS2Cst v R) ^ ((1 : ℝ) / 4) * bogS2Cst v R
        = (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (bogS2Cst v R) ^ (1 : ℝ) by
      rw [Real.rpow_one]]
    rw [← Real.rpow_add hCpos]
    norm_num
  rw [bogS2A3, ← h2]
  nlinarith [h1, hC1, hX0, Real.rpow_nonneg hX0 (1 / 2 : ℝ), Real.rpow_nonneg hX0 (3 : ℝ)]

/-! ## 7. The final constant -/

/-- The coefficient of the region-B sum bound. -/
def bogS2KB (v : E3 → ℝ) (R : ℝ) : ℝ :=
  27729 * Real.sqrt (bogS2Cst v R) * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 3
    + 22356 * (bogS2Cst v R) ^ ((1 : ℝ) / 4) * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 4
    + 972 * Real.sqrt (bogS2Cst v R) * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 4
    + 1242 * (bogS2Cst v R) ^ ((5 : ℝ) / 4) * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 3
    + 54 * bogS2Cst v R * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 3
    + 371 * (bogS2Cst v R) ^ 2 * (16 * Real.sqrt (bogS2Cst v R) + 2)
    + 491520 * (bogS2Cst v R) ^ 2
        * (2.5 + Real.log (1 + (16 * Real.sqrt (bogS2Cst v R) + 2)))

lemma bogS2KB_pos {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < a v) :
    0 < bogS2KB v R := by
  have hC1 : 1 ≤ bogS2Cst v R := one_le_bogS2Cst hR hav
  have hC0 : (0 : ℝ) < bogS2Cst v R := lt_of_lt_of_le one_pos hC1
  have hs : (0 : ℝ) ≤ Real.sqrt (bogS2Cst v R) := Real.sqrt_nonneg _
  have hĈ0 : (0 : ℝ) ≤ 16 * Real.sqrt (bogS2Cst v R) + 2 := by positivity
  have hC14 : (0 : ℝ) ≤ (bogS2Cst v R) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hC0.le _
  have hC54 : (0 : ℝ) ≤ (bogS2Cst v R) ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hC0.le _
  have hlog : (0 : ℝ) < 2.5 + Real.log (1 + (16 * Real.sqrt (bogS2Cst v R) + 2)) := by
    have h := Real.log_pos (show (1 : ℝ) < 1 + (16 * Real.sqrt (bogS2Cst v R) + 2) by linarith)
    linarith
  have h1 : (0 : ℝ) ≤ 27729 * Real.sqrt (bogS2Cst v R)
      * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 3 := by positivity
  have h2 : (0 : ℝ) ≤ 22356 * (bogS2Cst v R) ^ ((1 : ℝ) / 4)
      * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ 972 * Real.sqrt (bogS2Cst v R)
      * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 4 := by positivity
  have h4 : (0 : ℝ) ≤ 1242 * (bogS2Cst v R) ^ ((5 : ℝ) / 4)
      * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 3 := by positivity
  have h5 : (0 : ℝ) ≤ 54 * bogS2Cst v R * (16 * Real.sqrt (bogS2Cst v R) + 2) ^ 3 := by
    positivity
  have h6 : (0 : ℝ) ≤ 371 * (bogS2Cst v R) ^ 2 * (16 * Real.sqrt (bogS2Cst v R) + 2) := by
    positivity
  have h7 : (0 : ℝ) < 491520 * (bogS2Cst v R) ^ 2
      * (2.5 + Real.log (1 + (16 * Real.sqrt (bogS2Cst v R) + 2))) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hC0 2)) hlog
  rw [bogS2KB]
  linarith [h1, h2, h3, h4, h5, h6, h7]

/-! ## 8. The cube sum -/

/-- The sum of the majorant over the cube. -/
theorem bogS2_cube_sum_le {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {J : ℕ}
    (hR : 0 < R) (hav : 0 < a v) (hC : Core v R μ ρ) (hX : fsX v μ ≤ 1 / 50)
    (hJ : (J : ℝ) + 1 ≤ (16 * Real.sqrt (bogS2Cst v R) + 2) / bogMesh v ρ μ) :
    ∑ n ∈ cube J, bogS2MajE v R ρ μ n ≤ bogS2KB v R * (fsX v μ) ^ (-(4 : ℝ)) := by
  set C := bogS2Cst v R with hCdef
  set Ĉ := 16 * Real.sqrt C + 2 with hĈdef
  set X := fsX v μ with hXdef
  have hC1 : 1 ≤ C := one_le_bogS2Cst hR hav
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  have hX0 : 0 < X := bogS2_fsX_pos hC hav
  have hXnn : 0 ≤ X := hX0.le
  have hXle1 : X ≤ 1 := by rw [hXdef]; linarith [hX]
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  have hδ0 : 0 ≤ bogMesh v ρ μ := hδ.le
  have hĈ0 : 0 ≤ Ĉ := by rw [hĈdef]; positivity
  have hδle : bogMesh v ρ μ ≤ 9 * X ^ ((3 : ℝ) / 2) := by
    rw [hXdef]; exact bogS2_mesh_le hC hav
  obtain ⟨hS1, hS2, hS3, hS4⟩ := cubeMomSums J
  have hJ1 : (J : ℝ) + 1 ≤ Ĉ * X ^ (-(3 / 2 : ℝ)) := by
    have h1 : 1 / bogMesh v ρ μ ≤ X ^ (-(3 / 2 : ℝ)) := bogS2_mesh_inv_le hC hav
    have h2 : (16 * Real.sqrt C + 2) / bogMesh v ρ μ = Ĉ * (1 / bogMesh v ρ μ) := by
      rw [hĈdef]; ring
    rw [h2] at hJ
    exact le_trans hJ (mul_le_mul_of_nonneg_left h1 hĈ0)
  have hJ1pos : (0 : ℝ) ≤ Ĉ * X ^ (-(3 / 2 : ℝ)) := by
    rw [hĈdef]; positivity
  have hJ3 : ((J : ℝ) + 1) ^ 3 ≤ Ĉ ^ 3 * X ^ (-(9 / 2 : ℝ)) := by
    have h1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (J : ℝ) + 1) hJ1 3
    have h2 : (Ĉ * X ^ (-(3 / 2 : ℝ))) ^ 3 = Ĉ ^ 3 * X ^ (-(9 / 2 : ℝ)) := by
      rw [mul_pow, bogS2_rpow_pow hXnn,
        show (-(3 / 2 : ℝ)) * ((3 : ℕ) : ℝ) = -(9 / 2 : ℝ) by norm_num]
    linarith [h1, h2.le, h2.ge]
  have hJ4 : ((J : ℝ) + 1) ^ 4 ≤ Ĉ ^ 4 * X ^ (-(6 : ℝ)) := by
    have h1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (J : ℝ) + 1) hJ1 4
    have h2 : (Ĉ * X ^ (-(3 / 2 : ℝ))) ^ 4 = Ĉ ^ 4 * X ^ (-(6 : ℝ)) := by
      rw [mul_pow, bogS2_rpow_pow hXnn,
        show (-(3 / 2 : ℝ)) * ((4 : ℕ) : ℝ) = -(6 : ℝ) by norm_num]
    linarith [h1, h2.le, h2.ge]
  have hs1 : (∑ n ∈ cube J, (1 : ℝ)) ≤ 27 * (Ĉ ^ 3 * X ^ (-(9 / 2 : ℝ))) :=
    le_trans hS1 (mul_le_mul_of_nonneg_left hJ3 (by norm_num))
  have hs2 : (∑ n ∈ cube J, ((mn n : ℝ) + 1)) ≤ 27 * (Ĉ ^ 4 * X ^ (-(6 : ℝ))) :=
    le_trans hS2 (mul_le_mul_of_nonneg_left hJ4 (by norm_num))
  have hs3 : (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 2)) ≤ 26 * (Ĉ * X ^ (-(3 / 2 : ℝ))) :=
    le_trans hS3 (mul_le_mul_of_nonneg_left hJ1 (by norm_num))
  have h1nn : (0 : ℝ) ≤ ∑ n ∈ cube J, (1 : ℝ) := Finset.sum_nonneg (fun n _ => by norm_num)
  have h2nn : (0 : ℝ) ≤ ∑ n ∈ cube J, ((mn n : ℝ) + 1) :=
    Finset.sum_nonneg (fun n _ => by
      have h : (0 : ℝ) ≤ (mn n : ℝ) := Nat.cast_nonneg _
      linarith)
  have h3nn : (0 : ℝ) ≤ ∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 2) :=
    Finset.sum_nonneg (fun n _ => by
      have h : (0 : ℝ) < (mn n : ℝ) + 1 := by
        have h2 : (0 : ℝ) ≤ (mn n : ℝ) := Nat.cast_nonneg _
        linarith
      positivity)
  have h4nn : (0 : ℝ) ≤ ∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 3) :=
    Finset.sum_nonneg (fun n _ => by
      have h : (0 : ℝ) < (mn n : ℝ) + 1 := by
        have h2 : (0 : ℝ) ≤ (mn n : ℝ) := Nat.cast_nonneg _
        linarith
      positivity)
  have hA1 : bogS2A1 v R ρ μ ≤ 1027 * Real.sqrt C * X := by
    have h := bogS2A1_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC hX
    rw [← hCdef, ← hXdef] at h
    exact h
  have hA2 : bogS2A2 v R ρ μ
      ≤ 92 * C ^ ((1 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) * bogMesh v ρ μ
        + 4 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * bogMesh v ρ μ := by
    have h := bogS2A2_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC hX
    rw [← hCdef, ← hXdef] at h
    exact h
  have hA2' : bogS2A2 v R ρ μ
      ≤ 92 * C ^ ((1 : ℝ) / 4) * (9 * X ^ (2 : ℝ)) + 4 * Real.sqrt C * (9 * X ^ (3 : ℝ)) := by
    have h1 : 92 * C ^ ((1 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) * bogMesh v ρ μ
        ≤ 92 * C ^ ((1 : ℝ) / 4) * (9 * X ^ (2 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hδle
        (by positivity : (0 : ℝ) ≤ 92 * C ^ ((1 : ℝ) / 4) * X ^ ((1 : ℝ) / 2))
      have he : 92 * C ^ ((1 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) * (9 * X ^ ((3 : ℝ) / 2))
          = 92 * C ^ ((1 : ℝ) / 4) * (9 * X ^ (2 : ℝ)) := by
        rw [show 92 * C ^ ((1 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) * (9 * X ^ ((3 : ℝ) / 2))
            = (92 * C ^ ((1 : ℝ) / 4) * 9) * (X ^ ((1 : ℝ) / 2) * X ^ ((3 : ℝ) / 2)) by ring]
        rw [bogS2_rpow_mul_eq hX0, show ((1 : ℝ) / 2 + 3 / 2) = (2 : ℝ) by norm_num]
        ring
      exact le_trans h he.le
    have h2 : 4 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * bogMesh v ρ μ
        ≤ 4 * Real.sqrt C * (9 * X ^ (3 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hδle
        (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt C * X ^ ((3 : ℝ) / 2))
      have he : 4 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * (9 * X ^ ((3 : ℝ) / 2))
          = 4 * Real.sqrt C * (9 * X ^ (3 : ℝ)) := by
        rw [show 4 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * (9 * X ^ ((3 : ℝ) / 2))
            = (4 * Real.sqrt C * 9) * (X ^ ((3 : ℝ) / 2) * X ^ ((3 : ℝ) / 2)) by ring]
        rw [bogS2_rpow_mul_eq hX0, show ((3 : ℝ) / 2 + 3 / 2) = (3 : ℝ) by norm_num]
        ring
      exact le_trans h he.le
    linarith [hA2, h1, h2]
  have hA3 : bogS2A3 v R ρ μ
      ≤ 46 * C ^ ((5 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) + 2 * C * X ^ (3 : ℝ) := by
    have h := bogS2A3_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC hX
    rw [← hCdef, ← hXdef] at h
    exact h
  have hA4 : bogS2A4 v R ρ μ ≤ 512 * (11 / (40 * Real.pi ^ 2)) * C ^ 2 := by
    have h1 : 1 / (bogMesh v ρ μ) ^ 2 ≤ (11 / (40 * Real.pi ^ 2)) * X ^ (-(3 : ℝ)) := by
      have h := bogMeshInvSqLe (v := v) (R := R) (μ := μ) (ρ := ρ) hav hC
      rw [← hXdef] at h
      exact h
    have h2 : bogS2A4 v R ρ μ
        = (512 * C ^ 2 * X ^ (3 : ℝ)) * (1 / (bogMesh v ρ μ) ^ 2) := by
      rw [bogS2A4, ← hCdef, ← hXdef]
      ring
    have h3 : (512 * C ^ 2 * X ^ (3 : ℝ)) * (1 / (bogMesh v ρ μ) ^ 2)
        ≤ (512 * C ^ 2 * X ^ (3 : ℝ)) * ((11 / (40 * Real.pi ^ 2)) * X ^ (-(3 : ℝ))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : X ^ (3 : ℝ) * X ^ (-(3 : ℝ)) = 1 := by
      rw [bogS2_rpow_mul_eq hX0, show ((3 : ℝ) + -(3 : ℝ)) = 0 by norm_num, Real.rpow_zero]
    have h5 : (512 * C ^ 2 * X ^ (3 : ℝ)) * ((11 / (40 * Real.pi ^ 2)) * X ^ (-(3 : ℝ)))
        = 512 * (11 / (40 * Real.pi ^ 2)) * C ^ 2 := by
      rw [show (512 * C ^ 2 * X ^ (3 : ℝ)) * ((11 / (40 * Real.pi ^ 2)) * X ^ (-(3 : ℝ)))
          = 512 * (11 / (40 * Real.pi ^ 2)) * C ^ 2 * (X ^ (3 : ℝ) * X ^ (-(3 : ℝ))) by ring,
        h4, mul_one]
    rw [h2]
    exact le_trans h3 (le_of_eq h5)
  have hA5 : bogS2A5 v R ρ μ ≤ 1024 * 16 * C ^ 2 * X ^ (-(3 : ℝ)) := by
    have h1 : bogHalf v ρ μ ≤ 16 * X ^ ((3 : ℝ) / 2) := by
      have h := bogS2_half_le hC hav
      rw [← hXdef] at h
      exact h
    have h2 : 1 / (bogMesh v ρ μ) ^ 3 ≤ X ^ (-(9 / 2 : ℝ)) := by
      have h := bogS2_mesh_inv_cube_le hC hav
      rw [← hXdef] at h
      exact h
    have h3 : bogS2A5 v R ρ μ
        = (1024 * C ^ 2 * bogHalf v ρ μ) * (1 / (bogMesh v ρ μ) ^ 3) := by
      rw [bogS2A5, ← hCdef]
      ring
    have h4 : 1024 * C ^ 2 * bogHalf v ρ μ ≤ 1024 * C ^ 2 * (16 * X ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : (1024 * C ^ 2 * (16 * X ^ ((3 : ℝ) / 2))) * (1 / (bogMesh v ρ μ) ^ 3)
        ≤ (1024 * C ^ 2 * (16 * X ^ ((3 : ℝ) / 2))) * X ^ (-(9 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : X ^ ((3 : ℝ) / 2) * X ^ (-(9 / 2 : ℝ)) = X ^ (-(3 : ℝ)) := by
      rw [bogS2_rpow_mul_eq hX0, show ((3 : ℝ) / 2 + -(9 / 2 : ℝ)) = -(3 : ℝ) by norm_num]
    have h7 : (1024 * C ^ 2 * (16 * X ^ ((3 : ℝ) / 2))) * X ^ (-(9 / 2 : ℝ))
        = 1024 * 16 * C ^ 2 * X ^ (-(3 : ℝ)) := by
      rw [show (1024 * C ^ 2 * (16 * X ^ ((3 : ℝ) / 2))) * X ^ (-(9 / 2 : ℝ))
          = 1024 * 16 * C ^ 2 * (X ^ ((3 : ℝ) / 2) * X ^ (-(9 / 2 : ℝ))) by ring, h6]
    rw [h3]
    exact le_trans (le_trans (mul_le_mul_of_nonneg_right h4 (by positivity)) h5) (le_of_eq h7)
  have b1 : bogS2A1 v R ρ μ * (∑ n ∈ cube J, (1 : ℝ))
      ≤ 27729 * Real.sqrt C * Ĉ ^ 3 * X ^ (-(4 : ℝ)) := by
    have hcoef : (0 : ℝ) ≤ 1027 * Real.sqrt C * X := by positivity
    have hstep := mul_le_mul hA1 hs1 h1nn hcoef
    refine le_trans hstep ?_
    have he : (1027 * Real.sqrt C * X) * (27 * (Ĉ ^ 3 * X ^ (-(9 / 2 : ℝ))))
        = 27729 * Real.sqrt C * Ĉ ^ 3 * (X * X ^ (-(9 / 2 : ℝ))) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (bogS2_rpow_one_mul_le hX0 hXle1 (by norm_num))
      (by positivity)
  have b2 : bogS2A2 v R ρ μ * (∑ n ∈ cube J, ((mn n : ℝ) + 1))
      ≤ 22356 * C ^ ((1 : ℝ) / 4) * Ĉ ^ 4 * X ^ (-(4 : ℝ))
        + 972 * Real.sqrt C * Ĉ ^ 4 * X ^ (-(4 : ℝ)) := by
    have hcoef : (0 : ℝ) ≤ 92 * C ^ ((1 : ℝ) / 4) * (9 * X ^ (2 : ℝ))
        + 4 * Real.sqrt C * (9 * X ^ (3 : ℝ)) := by positivity
    have hstep := mul_le_mul hA2' hs2 h2nn hcoef
    have h2n : X ^ (2 : ℝ) * X ^ (-(6 : ℝ)) = X ^ (-(4 : ℝ)) := by
      rw [bogS2_rpow_mul_eq hX0, show ((2 : ℝ) + -(6 : ℝ)) = -(4 : ℝ) by norm_num]
    have h3n : X ^ (3 : ℝ) * X ^ (-(6 : ℝ)) ≤ X ^ (-(4 : ℝ)) :=
      bogS2_rpow_mul_le (X := X) (p := 3) (q := 6) hX0 hXle1 (by norm_num)
    refine le_trans hstep ?_
    calc (92 * C ^ ((1 : ℝ) / 4) * (9 * X ^ (2 : ℝ)) + 4 * Real.sqrt C * (9 * X ^ (3 : ℝ)))
          * (27 * (Ĉ ^ 4 * X ^ (-(6 : ℝ))))
        = 22356 * C ^ ((1 : ℝ) / 4) * Ĉ ^ 4 * (X ^ (2 : ℝ) * X ^ (-(6 : ℝ)))
          + 972 * Real.sqrt C * Ĉ ^ 4 * (X ^ (3 : ℝ) * X ^ (-(6 : ℝ))) := by ring
      _ ≤ 22356 * C ^ ((1 : ℝ) / 4) * Ĉ ^ 4 * X ^ (-(4 : ℝ))
          + 972 * Real.sqrt C * Ĉ ^ 4 * X ^ (-(4 : ℝ)) := by
          have e1 : 22356 * C ^ ((1 : ℝ) / 4) * Ĉ ^ 4 * (X ^ (2 : ℝ) * X ^ (-(6 : ℝ)))
              = 22356 * C ^ ((1 : ℝ) / 4) * Ĉ ^ 4 * X ^ (-(4 : ℝ)) := by rw [h2n]
          have e2 : 972 * Real.sqrt C * Ĉ ^ 4 * (X ^ (3 : ℝ) * X ^ (-(6 : ℝ)))
              ≤ 972 * Real.sqrt C * Ĉ ^ 4 * X ^ (-(4 : ℝ)) :=
            mul_le_mul_of_nonneg_left h3n (by positivity)
          linarith [e1.le, e1.ge, e2]
  have b3 : bogS2A3 v R ρ μ * (∑ n ∈ cube J, (1 : ℝ))
      ≤ 1242 * C ^ ((5 : ℝ) / 4) * Ĉ ^ 3 * X ^ (-(4 : ℝ))
        + 54 * C * Ĉ ^ 3 * X ^ (-(4 : ℝ)) := by
    have hcoef : (0 : ℝ) ≤ 46 * C ^ ((5 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) + 2 * C * X ^ (3 : ℝ) :=
      by positivity
    have hstep := mul_le_mul hA3 hs1 h1nn hcoef
    have h1n : X ^ ((1 : ℝ) / 2) * X ^ (-(9 / 2 : ℝ)) = X ^ (-(4 : ℝ)) := by
      rw [bogS2_rpow_mul_eq hX0, show ((1 : ℝ) / 2 + -(9 / 2 : ℝ)) = -(4 : ℝ) by norm_num]
    have h2n : X ^ (3 : ℝ) * X ^ (-(9 / 2 : ℝ)) ≤ X ^ (-(4 : ℝ)) :=
      bogS2_rpow_mul_le (X := X) (p := 3) (q := 9 / 2) hX0 hXle1 (by norm_num)
    refine le_trans hstep ?_
    calc (46 * C ^ ((5 : ℝ) / 4) * X ^ ((1 : ℝ) / 2) + 2 * C * X ^ (3 : ℝ))
          * (27 * (Ĉ ^ 3 * X ^ (-(9 / 2 : ℝ))))
        = 1242 * C ^ ((5 : ℝ) / 4) * Ĉ ^ 3 * (X ^ ((1 : ℝ) / 2) * X ^ (-(9 / 2 : ℝ)))
          + 54 * C * Ĉ ^ 3 * (X ^ (3 : ℝ) * X ^ (-(9 / 2 : ℝ))) := by ring
      _ ≤ 1242 * C ^ ((5 : ℝ) / 4) * Ĉ ^ 3 * X ^ (-(4 : ℝ))
          + 54 * C * Ĉ ^ 3 * X ^ (-(4 : ℝ)) := by
          have e1 : 1242 * C ^ ((5 : ℝ) / 4) * Ĉ ^ 3
                * (X ^ ((1 : ℝ) / 2) * X ^ (-(9 / 2 : ℝ)))
              = 1242 * C ^ ((5 : ℝ) / 4) * Ĉ ^ 3 * X ^ (-(4 : ℝ)) := by rw [h1n]
          have e2 : 54 * C * Ĉ ^ 3 * (X ^ (3 : ℝ) * X ^ (-(9 / 2 : ℝ)))
              ≤ 54 * C * Ĉ ^ 3 * X ^ (-(4 : ℝ)) :=
            mul_le_mul_of_nonneg_left h2n (by positivity)
          linarith [e1.le, e1.ge, e2]
  have b4 : bogS2A4 v R ρ μ * (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 2))
      ≤ 371 * C ^ 2 * Ĉ * X ^ (-(4 : ℝ)) := by
    have hcoef : (0 : ℝ) ≤ 512 * (11 / (40 * Real.pi ^ 2)) * C ^ 2 := by positivity
    have hstep := mul_le_mul hA4 hs3 h3nn hcoef
    have h532 : 512 * (11 / (40 * Real.pi ^ 2)) * 26 ≤ 371 := by
      have hpi : (3.1415 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d4
      have hpi2 : (9.868 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [hpi]
      have he : 512 * (11 / (40 * Real.pi ^ 2)) * 26 = 146432 / (40 * Real.pi ^ 2) := by ring
      rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < 40 * Real.pi ^ 2)]
      nlinarith [hpi2]
    have hxp : X ^ (-(3 / 2 : ℝ)) ≤ X ^ (-(4 : ℝ)) :=
      bogS2_rpow_neg_le_four hX0 hXle1 (by norm_num)
    refine le_trans hstep ?_
    calc (512 * (11 / (40 * Real.pi ^ 2)) * C ^ 2) * (26 * (Ĉ * X ^ (-(3 / 2 : ℝ))))
        = 512 * (11 / (40 * Real.pi ^ 2)) * 26 * (C ^ 2 * (Ĉ * X ^ (-(3 / 2 : ℝ)))) := by ring
      _ ≤ 371 * (C ^ 2 * (Ĉ * X ^ (-(3 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_right h532 (by positivity)
      _ ≤ 371 * (C ^ 2 * (Ĉ * X ^ (-(4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxp (by positivity))
              (by positivity)) (by norm_num)
      _ = 371 * C ^ 2 * Ĉ * X ^ (-(4 : ℝ)) := by ring
  have b5 : bogS2A5 v R ρ μ * (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 3))
      ≤ 491520 * C ^ 2 * (2.5 + Real.log (1 + Ĉ)) * X ^ (-(4 : ℝ)) := by
    have hJ1' : (J : ℝ) + 1 ≤ Ĉ / bogMesh v ρ μ := by
      have h2 : (16 * Real.sqrt C + 2) / bogMesh v ρ μ = Ĉ / bogMesh v ρ μ := by rw [hĈdef]
      rw [h2] at hJ
      exact hJ
    have hL : 30 * (1 + Real.log (2 + (J : ℝ)))
        ≤ 30 * (2.5 + Real.log (1 + Ĉ)) * (1 + Real.log (1 / X)) := by
      have hJ2 : (2 : ℝ) + (J : ℝ) ≤ (1 + Ĉ) * X ^ (-(3 / 2 : ℝ)) := by
        have h4 : (1 : ℝ) ≤ X ^ (-(3 / 2 : ℝ)) := by
          have h5 : X ^ (-(3 / 2 : ℝ)) = (X ^ ((3 : ℝ) / 2))⁻¹ := Real.rpow_neg hXnn _
          rw [h5, one_le_inv₀ (Real.rpow_pos_of_pos hX0 _)]
          exact bogS2_rpow_le_one' hXnn hXle1 (by norm_num)
        have h7 : (1 + Ĉ) * X ^ (-(3 / 2 : ℝ))
            = X ^ (-(3 / 2 : ℝ)) + Ĉ * X ^ (-(3 / 2 : ℝ)) := by ring
        linarith [h4, hJ1, h7.le, h7.ge]
      have h9 : Real.log (2 + (J : ℝ)) ≤ Real.log ((1 + Ĉ) * X ^ (-(3 / 2 : ℝ))) :=
        Real.log_le_log (by positivity) hJ2
      have h10 : Real.log ((1 + Ĉ) * X ^ (-(3 / 2 : ℝ)))
          = Real.log (1 + Ĉ) + (-(3 / 2 : ℝ)) * Real.log X := by
        rw [Real.log_mul (by linarith) (Real.rpow_pos_of_pos hX0 _).ne']
        rw [Real.log_rpow hX0]
      have h11 : Real.log (1 / X) = -Real.log X := by
        rw [one_div]
        exact Real.log_inv X
      have h12 : (0 : ℝ) ≤ Real.log (1 / X) :=
        Real.log_nonneg (by rw [one_le_div hX0]; exact hXle1)
      have h13 : Real.log (2 + (J : ℝ))
          ≤ (Real.log (1 + Ĉ) + 1.5) * (1 + Real.log (1 / X)) := by
        rw [h10] at h9
        have h14 : (-(3 / 2 : ℝ)) * Real.log X ≤ 1.5 * Real.log (1 / X) := by
          rw [h11]; ring_nf; nlinarith [h12]
        have h15 : (0 : ℝ) ≤ Real.log (1 + Ĉ) := Real.log_nonneg (by linarith)
        nlinarith [h9, h14, h12, h15]
      linarith [h13, h12]
    have hXlog : (1 + Real.log (1 / X)) * X ≤ 1 := by
      have h3 : 0 < 1 / X := by positivity
      have h5 : Real.log (1 / X) ≤ 1 / X - 1 := Real.log_le_sub_one_of_pos h3
      have h7 : (1 + Real.log (1 / X)) * X ≤ (1 + (1 / X - 1)) * X :=
        mul_le_mul_of_nonneg_right (by linarith [h5]) hXnn
      have h8 : (1 + (1 / X - 1)) * X = 1 := by
        rw [show 1 + (1 / X - 1) = 1 / X by ring, div_mul_cancel₀ 1 hX0.ne']
      linarith [h7, h8.le, h8.ge]
    have h9 : (1 + Real.log (1 / X)) ≤ X ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, ← one_div, le_div_iff₀ hX0]
      exact hXlog
    have h13 : X ^ (-(3 : ℝ)) * (1 + Real.log (1 / X)) ≤ X ^ (-(4 : ℝ)) := by
      have h3 : X ^ (-(4 : ℝ)) = X ^ (-(3 : ℝ)) * X ^ (-(1 : ℝ)) := by
        rw [bogS2_rpow_mul_eq hX0, show (-(3 : ℝ) + -(1 : ℝ)) = -(4 : ℝ) by norm_num]
      rw [h3]
      exact mul_le_mul_of_nonneg_left h9 (Real.rpow_nonneg hXnn _)
    have hcoef : (0 : ℝ) ≤ 1024 * 16 * C ^ 2 * X ^ (-(3 : ℝ)) := by positivity
    have hs5 : (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 3))
        ≤ 30 * (2.5 + Real.log (1 + Ĉ)) * (1 + Real.log (1 / X)) := le_trans hS4 hL
    have hstep := mul_le_mul hA5 hs5 h4nn hcoef
    refine le_trans hstep ?_
    calc (1024 * 16 * C ^ 2 * X ^ (-(3 : ℝ)))
          * (30 * (2.5 + Real.log (1 + Ĉ)) * (1 + Real.log (1 / X)))
        = 491520 * (C ^ 2 * ((2.5 + Real.log (1 + Ĉ))
            * (X ^ (-(3 : ℝ)) * (1 + Real.log (1 / X))))) := by ring
      _ ≤ 491520 * (C ^ 2 * ((2.5 + Real.log (1 + Ĉ)) * X ^ (-(4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h13
              (by have h := Real.log_nonneg (show (1 : ℝ) ≤ 1 + Ĉ by linarith); linarith))
              (by positivity)) (by norm_num)
      _ = 491520 * C ^ 2 * (2.5 + Real.log (1 + Ĉ)) * X ^ (-(4 : ℝ)) := by ring
  have hsum_id : (∑ n ∈ cube J, bogS2MajE v R ρ μ n)
      = bogS2A1 v R ρ μ * (∑ n ∈ cube J, (1 : ℝ))
        + bogS2A2 v R ρ μ * (∑ n ∈ cube J, ((mn n : ℝ) + 1))
        + bogS2A3 v R ρ μ * (∑ n ∈ cube J, (1 : ℝ))
        + bogS2A4 v R ρ μ * (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 2))
        + bogS2A5 v R ρ μ * (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 3)) := by
    show (∑ n ∈ cube J, (bogS2A1 v R ρ μ
        + bogS2A2 v R ρ μ * ((mn n : ℝ) + 1)
        + bogS2A3 v R ρ μ
        + bogS2A4 v R ρ μ * (1 / (((mn n : ℝ) + 1) ^ 2))
        + bogS2A5 v R ρ μ * (1 / (((mn n : ℝ) + 1) ^ 3))))
      = bogS2A1 v R ρ μ * (∑ n ∈ cube J, (1 : ℝ))
        + bogS2A2 v R ρ μ * (∑ n ∈ cube J, ((mn n : ℝ) + 1))
        + bogS2A3 v R ρ μ * (∑ n ∈ cube J, (1 : ℝ))
        + bogS2A4 v R ρ μ * (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 2))
        + bogS2A5 v R ρ μ * (∑ n ∈ cube J, 1 / (((mn n : ℝ) + 1) ^ 3))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hb : (∑ n ∈ cube J, bogS2MajE v R ρ μ n)
      ≤ (27729 * Real.sqrt C * Ĉ ^ 3
          + (22356 * C ^ ((1 : ℝ) / 4) + 972 * Real.sqrt C) * Ĉ ^ 4
          + (1242 * C ^ ((5 : ℝ) / 4) + 54 * C) * Ĉ ^ 3
          + 371 * C ^ 2 * Ĉ
          + 491520 * C ^ 2 * (2.5 + Real.log (1 + Ĉ))) * X ^ (-(4 : ℝ)) := by
    rw [hsum_id]
    have hdist : (27729 * Real.sqrt C * Ĉ ^ 3
          + (22356 * C ^ ((1 : ℝ) / 4) + 972 * Real.sqrt C) * Ĉ ^ 4
          + (1242 * C ^ ((5 : ℝ) / 4) + 54 * C) * Ĉ ^ 3
          + 371 * C ^ 2 * Ĉ
          + 491520 * C ^ 2 * (2.5 + Real.log (1 + Ĉ))) * X ^ (-(4 : ℝ))
        = 27729 * Real.sqrt C * Ĉ ^ 3 * X ^ (-(4 : ℝ))
          + (22356 * C ^ ((1 : ℝ) / 4) * Ĉ ^ 4 * X ^ (-(4 : ℝ))
            + 972 * Real.sqrt C * Ĉ ^ 4 * X ^ (-(4 : ℝ)))
          + (1242 * C ^ ((5 : ℝ) / 4) * Ĉ ^ 3 * X ^ (-(4 : ℝ))
            + 54 * C * Ĉ ^ 3 * X ^ (-(4 : ℝ)))
          + 371 * C ^ 2 * Ĉ * X ^ (-(4 : ℝ))
          + 491520 * C ^ 2 * (2.5 + Real.log (1 + Ĉ)) * X ^ (-(4 : ℝ)) := by ring
    rw [hdist]
    linarith [b1, b2, b3, b4, b5]
  refine le_trans hb ?_
  have hkb : bogS2KB v R * X ^ (-(4 : ℝ))
      = (27729 * Real.sqrt C * Ĉ ^ 3
          + (22356 * C ^ ((1 : ℝ) / 4) + 972 * Real.sqrt C) * Ĉ ^ 4
          + (1242 * C ^ ((5 : ℝ) / 4) + 54 * C) * Ĉ ^ 3
          + 371 * C ^ 2 * Ĉ
          + 491520 * C ^ 2 * (2.5 + Real.log (1 + Ĉ))) * X ^ (-(4 : ℝ)) := by
    rw [bogS2KB, ← hCdef, ← hĈdef]
    ring
  rw [hkb]

/-! ## 9. The pointwise bound -/

/-- The state-independent bound on `bogVmaxt`. -/
lemma bogS2_vmaxt_le {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hC : Core v R μ ρ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hVs : bogVs v R ρ μ ≤ bogS2Cst v R)
    (hOsc : bogOscM v R ρ μ
      ≤ 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3 / (a v) ^ 2))
    (hell : 2 * Real.pi * Real.sqrt 3 ≤ ell v μ) :
    bogVmaxt v h R ρ μ n ≤ bogS2Cst v R := by
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  by_cases hn : n = 0
  · subst hn
    have hP : 0 < ρ * a v := mul_pos hC.hρ0 hav
    have hℓ : 0 < ell v μ := sb_ell_pos hav hC
    have hom : bogOm v h R ρ μ 0 ≤ 2 * bogOscM v R ρ μ :=
      bogS2_om_le_two_oscM hP hδ hℓ hR.le hell
    have hβ := bogBeta_le_decay (h := h) hR hC.hρ0 hav hv hvrad hv_supp hRℓ (tSca v ρ μ 0)
    have hβ' : |bogVNt v h ρ μ 0| ≤ bogBs v R := by
      rw [bogVNt]
      refine le_trans hβ (div_le_self (le_of_lt (bogBs_pos v R)) ?_)
      have h3 : (0 : ℝ) ≤ Real.sqrt (ρ * a v) * ‖tSca v ρ μ 0‖ := by positivity
      linarith
    have hom0 : 0 ≤ bogOm v h R ρ μ 0 := by
      have h4 : (0 : ℝ) < 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ 0 := by
        have h5 : bogRLot v ρ μ 0 = -bogHalf v ρ μ := by
          rw [bogRLot]
          have hz : ‖tSca v ρ μ 0‖ = 0 := by
            rw [norm_tSca]
            have hzz : lpt (bogMesh v ρ μ) (0 : Fin 3 → ℤ) = 0 := by
              ext i
              simp [lpt]
            rw [hzz, norm_zero]
          rw [hz]; ring
        rw [h5]
        have h6 : Real.sqrt (ρ * a v) * bogHalf v ρ μ = Real.pi * Real.sqrt 3 / ell v μ :=
          bogS2_sqrt_mul_half hP hℓ
        have h7 : Real.pi * Real.sqrt 3 / ell v μ ≤ 1 / 2 := by
          rw [div_le_iff₀ hℓ]; nlinarith [hell]
        nlinarith [h6, h7]
      rw [bogOm, bogOscK]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg
        (pow_nonneg (by positivity) 3)) (Real.sqrt_nonneg _)) (bogHalf_pos hδ).le) h4.le
    have hkey : bogVmaxt v h R ρ μ 0 ≤ bogBs v R + 2 * bogOscM v R ρ μ := by
      rw [bogVmaxt]
      refine max_le ?_ ?_
      · rw [abs_le]
        constructor
        · rw [bogVlot]; linarith [(abs_le.mp hβ').1, hom0]
        · rw [bogVlot]; linarith [(abs_le.mp hβ').2, hom]
      · rw [abs_le]
        constructor
        · rw [bogVhit]; linarith [(abs_le.mp hβ').1, hom0]
        · rw [bogVhit]; linarith [(abs_le.mp hβ').2, hom]
    have hBs : bogBs v R ≤ 1 + bogKB * (1 + R) ^ 3 / a v := by
      rw [bogBs]
      have hbb : (0 : ℝ) ≤ bogKB * (1 + R) ^ 3 / a v :=
        div_nonneg (mul_nonneg bogKB_nonneg (pow_nonneg (by positivity) 3)) hav.le
      exact max_le (by linarith) (by linarith)
    have hOsc4 : 2 * bogOscM v R ρ μ
        ≤ 4 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
            / (a v) ^ 2) := by linarith [hOsc]
    have hB4 : 4 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
          / (a v) ^ 2)
        ≤ 64 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
          / (a v) ^ 2) := by
      have h1 : (0 : ℝ) ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi
          * Real.sqrt 3 / (a v) ^ 2 := by
        refine div_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg
          (pow_nonneg (by positivity) 3)) (Real.sqrt_nonneg _)) Real.pi_pos.le)
          (Real.sqrt_nonneg _)
      linarith [h1]
    rw [bogS2Cst]
    linarith [hkey, hBs, hOsc4, hB4]
  · have h1 : bogVmaxt v h R ρ μ n ≤ bogVs v R ρ μ :=
      bogVmaxt_le_vs (h := h) hR hC.hρ0 hav hv hvrad hv_supp hRℓ hδ hn
    linarith [h1, hVs]

theorem bogS2_le_maj {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hav : 0 < a v) (hC : Core v R μ ρ)
    (hX : fsX v μ ≤ 1 / 50) (hX12 : fsX v μ ≤ 1 / 10 ^ 12)
    (hOsc : bogOscM v R ρ μ ≤ bogS2Cst v R * (fsX v μ) ^ (3 : ℝ))
    (hVs : bogVs v R ρ μ ≤ bogS2Cst v R)
    (hc2big : bogS2RB v R ≤ bogC2 v ρ μ)
    (hell : 2 * Real.pi * Real.sqrt 3 ≤ ell v μ)
    (hV : bogVmaxt v h R ρ μ n ≤ bogS2Cst v R) :
    bogS2 v h R ρ μ n ≤ bogS2Maj v R ρ μ n := by
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  have hδ0 : 0 ≤ bogMesh v ρ μ := hδ.le
  have hP : 0 < ρ * a v := mul_pos hC.hρ0 hav
  set C := bogS2Cst v R with hCdef
  set X := fsX v μ with hXdef
  have hC1 : 1 ≤ C := one_le_bogS2Cst hR hav
  have hX0 : 0 < X := bogS2_fsX_pos hC hav
  rw [bogS2Maj]
  by_cases hgate : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ
  · rw [if_pos hgate]
    have hVnn : 0 ≤ bogVmaxt v h R ρ μ n := by
      rw [bogVmaxt]; positivity
    have hrh0 : (0 : ℝ) ≤ bogRHit v ρ μ n := by
      rw [bogRHit]
      exact add_nonneg (norm_nonneg _) (bogHalf_pos hδ).le
    have hu2 : bogUHit v ρ μ n ≤ (bogRHit v ρ μ n) ^ 2 :=
      tauScRad_le_sq v hP (sb_c1_pos hav hC) (sb_c2_pos hav hC) (bogS2_eT_nonneg hC)
        (bogS2_eT_le_one hC) hrh0
    have hulonn : 0 ≤ bogUHit v ρ μ n :=
      tauScRad_nonneg v hP (bogS2_eT_nonneg hC) (bogS2_eT_le_one hC) (bogRHit v ρ μ n)
    have hrB : bogRHit v ρ μ n ≤ bogS2RB v R := by
      have h1 : Real.sqrt (bogVs v R ρ μ) ≤ Real.sqrt C := Real.sqrt_le_sqrt hVs
      simp only [bogS2RB, bogBigThr] at hgate ⊢
      exact le_trans hgate (mul_le_mul_of_nonneg_left h1 (by norm_num))
    have hrm : bogRHit v ρ μ n ≤ Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) := by
      have h1 : ‖lpt (1 : ℝ) n‖ ≤ Real.sqrt 3 * (mn n : ℝ) := bogS2_norm_lpt_le_mn n
      rw [bogRHit_eq v ρ μ n hδ0]
      have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      have hJnn : (0 : ℝ) ≤ (mn n : ℝ) + 1 := by positivity
      have h4 : ‖lpt (1 : ℝ) n‖ + Real.sqrt 3 / 2 ≤ Real.sqrt 3 * ((mn n : ℝ) + 1) := by
        nlinarith [h1, hs3, hJnn]
      have h5 := mul_le_mul_of_nonneg_left h4 hδ0
      rw [show bogMesh v ρ μ * (Real.sqrt 3 * ((mn n : ℝ) + 1))
          = Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) by ring] at h5
      exact h5
    have hA1nn : 0 ≤ bogS2A1 v R ρ μ := by
      rw [bogS2A1]
      have h7 : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
      have h8 : 0 ≤ bogS2RB v R := by rw [bogS2RB]; positivity
      nlinarith [h7, h8, sq_nonneg (bogC1 v ρ μ)]
    have hT1 : bogUHit v ρ μ n - bogULot v ρ μ n ≤ bogS2A1 v R ρ μ := by
      have h1 := bogS2_hit_sub_lot_le (h := h) hR hav hC hX12 hVs hc2big hgate
      rw [bogS2A1]
      have h7 : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
      nlinarith [h1, hrB, h7]
    have hom2 : bogOm v h R ρ μ n ≤ 2 * bogOscM v R ρ μ :=
      bogS2_om_le_two_oscM hP hδ (sb_ell_pos hav hC) hR.le hell
    have hT2 : Real.sqrt ((bogUHit v ρ μ n - bogULot v ρ μ n)
          * (2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n))
        ≤ Real.sqrt (2 * bogS2A1 v R ρ μ)
          * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C) := by
      refine bogS2_sqrt_le_of_le_sq ?_ (by positivity)
      have hx0 : (0 : ℝ) ≤ 2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n := by
        linarith [hulonn, hVnn]
      have h2u : 2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n
          ≤ 2 * (bogRHit v ρ μ n) ^ 2 + 2 * C := by linarith [hu2, hV]
      have step1 : (bogUHit v ρ μ n - bogULot v ρ μ n)
            * (2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n)
          ≤ bogS2A1 v R ρ μ * (2 * (bogRHit v ρ μ n) ^ 2 + 2 * C) := by
        have h9 := mul_le_mul_of_nonneg_right hT1 hx0
        have h10 := mul_le_mul_of_nonneg_left h2u hA1nn
        linarith [h9, h10]
      have step2 : bogS2A1 v R ρ μ * (2 * (bogRHit v ρ μ n) ^ 2 + 2 * C)
          ≤ 2 * bogS2A1 v R ρ μ
            * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C) ^ 2 := by
        have hsC : C ≤ C ^ 2 := by nlinarith [hC1]
        have h3 : 0 ≤ Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) := by positivity
        have h2 : (bogRHit v ρ μ n) ^ 2 + C
            ≤ (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C) ^ 2 := by
          nlinarith [hrm, h3, hsC, sq_nonneg (bogRHit v ρ μ n), hδ0]
        nlinarith [h2, hA1nn]
      have step3 : 2 * bogS2A1 v R ρ μ
            * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C) ^ 2
          = (Real.sqrt (2 * bogS2A1 v R ρ μ)
              * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      linarith [step1, step2, step3.le, step3.ge]
    have hT3 : bogOm v h R ρ μ n ≤ 2 * C * X ^ (3 : ℝ) := by
      have h1 : bogOscM v R ρ μ ≤ C * X ^ (3 : ℝ) := hOsc
      linarith [hom2, h1]
    have homX : bogOm v h R ρ μ n ≤ 2 * C * X ^ (3 : ℝ) := hT3
    have hT4 : Real.sqrt (2 * bogOm v h R ρ μ n * bogUHit v ρ μ n)
        ≤ 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ
          * ((mn n : ℝ) + 1) := by
      rcases le_or_gt 0 (bogOm v h R ρ μ n) with hnn | hneg
      · have h2 : (Real.sqrt C * X ^ ((3 : ℝ) / 2)) ^ 2 = C * X ^ (3 : ℝ) := by
          rw [mul_pow, Real.sq_sqrt (by linarith), ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
          norm_num
        have h1 : 2 * bogOm v h R ρ μ n * bogUHit v ρ μ n
            ≤ (2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2) * (Real.sqrt 3 * bogMesh v ρ μ
                * ((mn n : ℝ) + 1)))) ^ 2 := by
          have h3 : 0 ≤ C * X ^ (3 : ℝ) := by positivity
          have h4 : bogUHit v ρ μ n ≤ (bogRHit v ρ μ n) ^ 2 := hu2
          have h5 : (0 : ℝ) ≤ X ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hX0.le _
          have h6 : (0 : ℝ) ≤ Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) := by positivity
          have h7 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
          have h8 : 2 * C * X ^ (3 : ℝ) = 2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2)) ^ 2 := by
            rw [h2]; ring
          rw [h8] at homX
          have hB2 : (bogRHit v ρ μ n) ^ 2
              ≤ (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1)) ^ 2 :=
            pow_le_pow_left₀ hrh0 hrm 2
          have hUB : bogUHit v ρ μ n
              ≤ (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1)) ^ 2 := le_trans h4 hB2
          have h9 : 2 * bogOm v h R ρ μ n
              ≤ 2 * (2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2)) ^ 2) := by linarith [homX]
          have hstep : 2 * bogOm v h R ρ μ n * bogUHit v ρ μ n
              ≤ 2 * (2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2)) ^ 2)
                * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1)) ^ 2 :=
            mul_le_mul h9 hUB hulonn (by positivity)
          have heq : 2 * (2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2)) ^ 2)
                * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1)) ^ 2
              = (2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2) * (Real.sqrt 3 * bogMesh v ρ μ
                  * ((mn n : ℝ) + 1)))) ^ 2 := by ring
          linarith [hstep, heq.le, heq.ge]
        calc Real.sqrt (2 * bogOm v h R ρ μ n * bogUHit v ρ μ n)
            ≤ Real.sqrt ((2 * (Real.sqrt C * X ^ ((3 : ℝ) / 2) * (Real.sqrt 3 * bogMesh v ρ μ
                * ((mn n : ℝ) + 1)))) ^ 2) := Real.sqrt_le_sqrt h1
          _ = 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ
                * ((mn n : ℝ) + 1) := by
              rw [Real.sqrt_sq (by positivity)]
              ring
      · have h1 : 2 * bogOm v h R ρ μ n * bogUHit v ρ μ n ≤ 0 := by
          nlinarith [hneg, hulonn]
        rw [Real.sqrt_eq_zero_of_nonpos h1]
        positivity
    have hT5 : bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n / (bogRLot v ρ μ n) ^ 2
        ≤ 512 * C ^ 2 * X ^ (3 : ℝ) / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2) := by
      have h3 : bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n ≤ 2 * C ^ 2 * X ^ (3 : ℝ) := by
        rcases le_or_gt 0 (bogOm v h R ρ μ n) with hnn | hneg
        · have h2 : bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n
              ≤ (2 * C * X ^ (3 : ℝ)) * C := mul_le_mul homX hV hVnn (by positivity)
          have h2' : (2 * C * X ^ (3 : ℝ)) * C = 2 * C ^ 2 * X ^ (3 : ℝ) := by ring
          linarith [h2, h2'.le, h2'.ge]
        · have h4 : bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hneg.le hVnn
          have h5 : (0 : ℝ) ≤ 2 * C ^ 2 * X ^ (3 : ℝ) := by positivity
          linarith [h4, h5]
      have h4 : 1 / (bogRLot v ρ μ n) ^ 2
          ≤ 256 / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2) :=
        bogS2_inv_rlo_sq_le (v := v) (ρ := ρ) (μ := μ) (n := n) hδ
      have he : bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n / (bogRLot v ρ μ n) ^ 2
          = (bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n)
            * (1 / (bogRLot v ρ μ n) ^ 2) := by ring
      rw [he]
      calc (bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n) * (1 / (bogRLot v ρ μ n) ^ 2)
          ≤ (2 * C ^ 2 * X ^ (3 : ℝ))
              * (256 / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2)) :=
            mul_le_mul h3 h4 (by positivity) (by positivity)
        _ = 512 * C ^ 2 * X ^ (3 : ℝ) / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2) := by
            ring
    have hT6 : (bogVmaxt v h R ρ μ n) ^ 2
          * (1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2))
        ≤ 1024 * bogHalf v ρ μ * C ^ 2 / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) := by
      have h1 : (bogVmaxt v h R ρ μ n) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hVnn hV 2
      have h2 : 1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2)
          ≤ 1024 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) :=
        bogS2_inv_rlo_sq_sub_le (v := v) (ρ := ρ) (μ := μ) (n := n) hδ
      have h5 : (bogVmaxt v h R ρ μ n) ^ 2
            * (1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2))
          ≤ C ^ 2 * (1024 * bogHalf v ρ μ / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3)) := by
        refine le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) ?_
        have hmn : (0 : ℝ) ≤ (mn n : ℝ) + 1 := by
          have h : (0 : ℝ) ≤ (mn n : ℝ) := Nat.cast_nonneg _
          linarith
        exact mul_le_mul_of_nonneg_right h1
          (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024) (bogHalf_pos hδ).le)
            (mul_nonneg (pow_nonneg hδ.le 3) (pow_nonneg hmn 3)))
      calc (bogVmaxt v h R ρ μ n) ^ 2
            * (1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2))
          ≤ C ^ 2 * (1024 * bogHalf v ρ μ
              / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3)) := h5
        _ = 1024 * bogHalf v ρ μ * C ^ 2 / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) := by
            ring
    have h6 : (bogUHit v ρ μ n - bogULot v ρ μ n)
          + Real.sqrt ((bogUHit v ρ μ n - bogULot v ρ μ n)
              * (2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n))
          + bogOm v h R ρ μ n
          + Real.sqrt (2 * bogOm v h R ρ μ n * bogUHit v ρ μ n)
          + bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n / (bogRLot v ρ μ n) ^ 2
          + (bogVmaxt v h R ρ μ n) ^ 2
              * (1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2))
        = bogMajB v h R ρ μ n := by
      rw [bogMajB]
    have hsum6 : bogS2A1 v R ρ μ
          + Real.sqrt (2 * bogS2A1 v R ρ μ)
            * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C)
          + 2 * C * X ^ (3 : ℝ)
          + 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ
            * ((mn n : ℝ) + 1)
          + 512 * C ^ 2 * X ^ (3 : ℝ) / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2)
          + 1024 * bogHalf v ρ μ * C ^ 2 / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3)
        ≤ bogS2MajE v R ρ μ n := by
      have hRHS : bogS2MajE v R ρ μ n
          = bogS2A1 v R ρ μ
            + (Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
                + 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ)
              * ((mn n : ℝ) + 1)
            + (Real.sqrt (2 * bogS2A1 v R ρ μ) * C + 2 * C * X ^ (3 : ℝ))
            + 512 * C ^ 2 * X ^ (3 : ℝ) / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2)
            + 1024 * bogHalf v ρ μ * C ^ 2 / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) := by
        have e4 : (512 * (bogS2Cst v R) ^ 2 * (fsX v μ) ^ (3 : ℝ) / (bogMesh v ρ μ) ^ 2)
              * (1 / (((mn n : ℝ) + 1) ^ 2))
            = 512 * C ^ 2 * X ^ (3 : ℝ) / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2) := by
          rw [← hCdef, ← hXdef]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        have e5 : (1024 * bogHalf v ρ μ * (bogS2Cst v R) ^ 2 / (bogMesh v ρ μ) ^ 3)
              * (1 / (((mn n : ℝ) + 1) ^ 3))
            = 1024 * bogHalf v ρ μ * C ^ 2 / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3) := by
          rw [← hCdef]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        change (bogS2A1 v R ρ μ
            + (Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
                + 2 * Real.sqrt (bogS2Cst v R) * (fsX v μ) ^ ((3 : ℝ) / 2) * Real.sqrt 3
                  * bogMesh v ρ μ) * ((mn n : ℝ) + 1)
            + (Real.sqrt (2 * bogS2A1 v R ρ μ) * (bogS2Cst v R)
                + 2 * (bogS2Cst v R) * (fsX v μ) ^ (3 : ℝ))
            + (512 * (bogS2Cst v R) ^ 2 * (fsX v μ) ^ (3 : ℝ) / (bogMesh v ρ μ) ^ 2)
                * (1 / (((mn n : ℝ) + 1) ^ 2))
            + (1024 * bogHalf v ρ μ * (bogS2Cst v R) ^ 2 / (bogMesh v ρ μ) ^ 3)
                * (1 / (((mn n : ℝ) + 1) ^ 3)))
          = bogS2A1 v R ρ μ
            + (Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
                + 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ)
              * ((mn n : ℝ) + 1)
            + (Real.sqrt (2 * bogS2A1 v R ρ μ) * C + 2 * C * X ^ (3 : ℝ))
            + 512 * C ^ 2 * X ^ (3 : ℝ) / (bogMesh v ρ μ ^ 2 * ((mn n : ℝ) + 1) ^ 2)
            + 1024 * bogHalf v ρ μ * C ^ 2 / (bogMesh v ρ μ ^ 3 * ((mn n : ℝ) + 1) ^ 3)
        rw [e4, e5, ← hCdef, ← hXdef]
      rw [hRHS]
      have e2 : (Real.sqrt (2 * bogS2A1 v R ρ μ) * Real.sqrt 3 * bogMesh v ρ μ
              + 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ)
            * ((mn n : ℝ) + 1)
          = Real.sqrt (2 * bogS2A1 v R ρ μ)
              * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1))
            + 2 * Real.sqrt C * X ^ ((3 : ℝ) / 2) * Real.sqrt 3 * bogMesh v ρ μ
              * ((mn n : ℝ) + 1) := by ring
      have e1 : Real.sqrt (2 * bogS2A1 v R ρ μ)
            * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1) + C)
          = Real.sqrt (2 * bogS2A1 v R ρ μ)
              * (Real.sqrt 3 * bogMesh v ρ μ * ((mn n : ℝ) + 1))
            + Real.sqrt (2 * bogS2A1 v R ρ μ) * C := by rw [mul_add]
      linarith [e1.le, e1.ge, e2.le, e2.ge]
    have hb2 : 0 ≤ bogS2MajE v R ρ μ n :=
      bogS2MajE_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) (n := n) hR hav hC.hρ0 hC.hμ
        (sb_ell_pos hav hC)
    have hb3 : bogS2 v h R ρ μ n ≤ max 0 (bogMajB v h R ρ μ n) := by
      have heq : bogS2 v h R ρ μ n = max 0 (bogMajB v h R ρ μ n) := by
        rw [bogS2, if_pos hgate]
      exact le_of_eq heq
    have hb4 : max 0 (bogMajB v h R ρ μ n) ≤ bogS2MajE v R ρ μ n :=
      max_le hb2 (by rw [← h6]; linarith [hsum6])
    exact le_trans hb3 hb4
  · rw [if_neg hgate, bogS2, if_neg hgate]

end Work.BoseBogFS
